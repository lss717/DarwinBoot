// SPDX-License-Identifier: BSD-2-Clause-Patent
#include <Uefi.h>
#include <Guid/FileInfo.h>
#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/PrintLib.h>
#include <Library/UefiLib.h>
#include <Protocol/UniXNULoader.h>
#include <Protocol/LoadedImage.h>
#include <Protocol/GraphicsOutput.h>
#include <Protocol/Cpu.h>
#include <Protocol/SimpleFileSystem.h>
#include "BootArgs.h"
#include "BootVideo.h"
#include "PackedRamdisk.h"
#include "WindowSize.h"

// The window only applies when the payload ADT has no /chosen/darwinboot-memory-size
// (that property, when present, wins). H126c keeps the ADT value untouched.
#define WINDOW_SIZE  SIZE_256MB
#define BLOCK_SIZE   SIZE_2MB
#define MAX_SEGMENTS 64

typedef struct {
  UINT64  Address;
  UINT64  Size;
  UINT64  FileOffset;
  UINT64  FileSize;
  UINT32  Protection;
} SEGMENT;

typedef struct {
  SEGMENT  Segments[MAX_SEGMENTS];
  UINTN    Count;
  UINT64   Base;
  UINT64   End;
  UINT64   Entry;
} KERNEL;

STATIC EFI_HANDLE  mImage;
UINT64 EFIAPI DarwinCurrentEl (VOID);
VOID EFIAPI DarwinEnter (UINT64 Args, UINT64 Entry, UINT64 Memory, UINT64 Size, UINT64 VideoBase, UINT64 VideoBytes);

#define READ_SYSREG(Name)  ({ UINT64 Value_; __asm__ volatile ("mrs %0, " #Name : "=r" (Value_)); Value_; })

STATIC UINT32 U32 (CONST VOID *P) { return ReadUnaligned32 ((CONST UINT32 *)P); }
STATIC UINT64 U64 (CONST VOID *P) { return ReadUnaligned64 ((CONST UINT64 *)P); }

STATIC
EFI_STATUS
ReadBootVideo (UINT64 Video[6])
{
  EFI_GRAPHICS_OUTPUT_PROTOCOL           *Gop;
  EFI_STATUS                            Status;

  ZeroMem (Video, 6 * sizeof (*Video));
  Status = gBS->HandleProtocol (gST->ConsoleOutHandle, &gEfiGraphicsOutputProtocolGuid, (VOID **)&Gop);
  if (EFI_ERROR (Status)) {
    Status = gBS->LocateProtocol (&gEfiGraphicsOutputProtocolGuid, NULL, (VOID **)&Gop);
  }
  if (Status == EFI_NOT_FOUND) { return EFI_SUCCESS; }
  if (EFI_ERROR (Status)) { return Status; }
  return DarwinBootVideoFromGop (Gop, Video);
}

STATIC
EFI_STATUS
ReadFile (
  EFI_FILE_PROTOCOL *Root,
  CONST CHAR16      *Path,
  UINTN             Limit,
  VOID              **Data,
  UINTN             *Size
  )
{
  EFI_STATUS         Status;
  EFI_FILE_PROTOCOL  *File;
  EFI_FILE_INFO      *Info;
  UINTN              InfoSize;
  UINTN              Actual;

  *Data = NULL;
  *Size = 0;
  Status = Root->Open (Root, &File, (CHAR16 *)Path, EFI_FILE_MODE_READ, 0);
  if (EFI_ERROR (Status)) { return Status; }
  Info = NULL;
  InfoSize = 0;
  Status = File->GetInfo (File, &gEfiFileInfoGuid, &InfoSize, NULL);
  if (Status != EFI_BUFFER_TOO_SMALL) { goto Done; }
  Info = AllocatePool (InfoSize);
  if (Info == NULL) { Status = EFI_OUT_OF_RESOURCES; goto Done; }
  Status = File->GetInfo (File, &gEfiFileInfoGuid, &InfoSize, Info);
  if (EFI_ERROR (Status)) { goto Done; }
  if ((Info->Attribute & EFI_FILE_DIRECTORY) || (Info->FileSize == 0) || (Info->FileSize > Limit)) {
    Print (L"DARWINBOOT: %s attr %lx size %lu limit %lu\n", Path, (UINT64)Info->Attribute, (UINT64)Info->FileSize, (UINT64)Limit);
    Status = EFI_BAD_BUFFER_SIZE;
    goto Done;
  }
  *Size = (UINTN)Info->FileSize;
  *Data = AllocatePool (*Size);
  if (*Data == NULL) { Status = EFI_OUT_OF_RESOURCES; goto Done; }
  Actual = *Size;
  Status = File->Read (File, &Actual, *Data);
  if (!EFI_ERROR (Status) && (Actual != *Size)) { Status = EFI_DEVICE_ERROR; }
Done:
  if (Info != NULL) { FreePool (Info); }
  File->Close (File);
  if (EFI_ERROR (Status) && (*Data != NULL)) { FreePool (*Data); *Data = NULL; }
  return Status;
}

STATIC
EFI_STATUS
ParseKernelHeader (CONST UINT8 *Data, UINTN Size, UINTN Header, KERNEL *Kernel)
{
  UINTN    Offset;
  UINTN    End;
  UINTN    Index;
  UINTN    Other;
  UINT32   Count;
  UINT32   Command;
  UINT32   Length;
  SEGMENT  *Segment;
  BOOLEAN  HasEntry;
  BOOLEAN  Executable;

  if ((Header > Size) || (Size - Header < 32) ||
      (U32 (Data + Header) != 0xfeedfacf) || (U32 (Data + Header + 4) != 0x100000c) ||
      (((U32 (Data + Header + 8) & 0x00ffffff) != 0) &&
       ((U32 (Data + Header + 8) & 0x00ffffff) != 2)) ||
      ((U32 (Data + Header + 12) != 2) &&
       ((Header != 0) || (U32 (Data + Header + 12) != 12)))) {
    return EFI_UNSUPPORTED;
  }
  if (U32 (Data + Header + 20) > Size - Header - 32) { return EFI_LOAD_ERROR; }
  ZeroMem (Kernel, sizeof (*Kernel));
  Count = U32 (Data + Header + 16);
  End = Header + 32 + U32 (Data + Header + 20);
  Offset = Header + 32;
  HasEntry = FALSE;
  for (Index = 0; Index < Count; Index++) {
    if (End - Offset < 8) { return EFI_LOAD_ERROR; }
    Command = U32 (Data + Offset);
    Length = U32 (Data + Offset + 4);
    if ((Length < 8) || (Length & 7) || (Length > End - Offset)) { return EFI_LOAD_ERROR; }
    if (Command == 0x19) {
      if ((Length < 72) || (U32 (Data + Offset + 64) > (Length - 72) / 80) ||
          (Kernel->Count == MAX_SEGMENTS)) { return EFI_LOAD_ERROR; }
      if (U64 (Data + Offset + 32) != 0) {
        Segment = &Kernel->Segments[Kernel->Count++];
        Segment->Address = U64 (Data + Offset + 24);
        Segment->Size = U64 (Data + Offset + 32);
        Segment->FileOffset = U64 (Data + Offset + 40);
        Segment->FileSize = U64 (Data + Offset + 48);
        Segment->Protection = U32 (Data + Offset + 60);
        if ((Segment->Size > WINDOW_SIZE) || (Segment->Address > MAX_UINT64 - Segment->Size) ||
            (Segment->FileSize > Segment->Size) || (Segment->FileOffset > Size) ||
            (Segment->FileSize > Size - Segment->FileOffset)) { return EFI_LOAD_ERROR; }
      }
    } else if (Command == 5) {
      if (HasEntry || (Length != 288) || (U32 (Data + Offset + 8) != 6) ||
          (U32 (Data + Offset + 12) != 68)) { return EFI_LOAD_ERROR; }
      Kernel->Entry = U64 (Data + Offset + 272);
      HasEntry = TRUE;
    }
    Offset += Length;
  }
  if ((Offset != End) || !HasEntry || (Kernel->Count == 0)) { return EFI_LOAD_ERROR; }
  Kernel->Base = MAX_UINT64;
  Executable = FALSE;
  for (Index = 0; Index < Kernel->Count; Index++) {
    Segment = &Kernel->Segments[Index];
    Kernel->Base = MIN (Kernel->Base, Segment->Address);
    Kernel->End = MAX (Kernel->End, Segment->Address + Segment->Size);
    if ((Kernel->Entry >= Segment->Address) && (Kernel->Entry - Segment->Address < Segment->FileSize) &&
        ((Segment->Protection & 4) != 0)) { Executable = TRUE; }
    for (Other = 0; Other < Index; Other++) {
      if ((Segment->Address < Kernel->Segments[Other].Address + Kernel->Segments[Other].Size) &&
          (Kernel->Segments[Other].Address < Segment->Address + Segment->Size)) { return EFI_LOAD_ERROR; }
    }
  }
  if (!Executable || (Kernel->Entry & 3) || (Kernel->Base & EFI_PAGE_MASK) ||
      (Kernel->Base > MAX_UINT64 - WINDOW_SIZE) ||
      (Kernel->End - Kernel->Base > WINDOW_SIZE - SIZE_2MB)) { return EFI_LOAD_ERROR; }
  return EFI_SUCCESS;
}

// Fileset segment offsets are absolute in the collection. XNU rebases and
// signs its own fixup chains after entry; firmware only copies root mappings.
STATIC
EFI_STATUS
ParseKernel (CONST UINT8 *Data, UINTN Size, KERNEL *Kernel)
{
  EFI_STATUS Status;
  KERNEL     Member;
  UINTN      Offset;
  UINTN      End;
  UINTN      Header;
  UINTN      Name;
  UINTN      Index;
  UINTN      Other;
  UINT32     Length;
  BOOLEAN    Found;
  BOOLEAN    Covered;
  SEGMENT    *Child;
  SEGMENT    *Parent;

  Status = ParseKernelHeader (Data, Size, 0, Kernel);
  if (EFI_ERROR (Status) || (U32 (Data + 12) != 12)) { return Status; }
  Offset = 32;
  End = 32 + U32 (Data + 20);
  Found = FALSE;
  while (Offset < End) {
    Length = U32 (Data + Offset + 4);
    if (U32 (Data + Offset) == 0x80000035) {
      if (Length < 40) { return EFI_LOAD_ERROR; }
      Name = U32 (Data + Offset + 24);
      if ((Name < 32) || (Name >= Length)) { return EFI_LOAD_ERROR; }
      for (Index = Name; (Index < Length) && (Data[Offset + Index] != 0); Index++) {}
      if (Index == Length) { return EFI_LOAD_ERROR; }
      Header = U64 (Data + Offset + 16);
      if ((Header > Size) || (Size - Header < 32) || (Header & 7)) { return EFI_LOAD_ERROR; }
      // Every indexed header must actually be loaded at its advertised VA.
      Covered = FALSE;
      for (Other = 0; Other < Kernel->Count; Other++) {
        Parent = &Kernel->Segments[Other];
        if ((Header >= Parent->FileOffset) &&
            (Header - Parent->FileOffset <= Parent->FileSize) &&
            (32 <= Parent->FileSize - (Header - Parent->FileOffset)) &&
            (U64 (Data + Offset + 8) == Parent->Address + Header - Parent->FileOffset)) {
          Covered = TRUE;
        }
      }
      if (!Covered) { return EFI_LOAD_ERROR; }
      if ((Index - Name == sizeof ("com.apple.kernel") - 1) &&
          (CompareMem (Data + Offset + Name, "com.apple.kernel", sizeof ("com.apple.kernel")) == 0)) {
        if (Found || (U32 (Data + Header + 12) != 2) ||
            (U32 (Data + Header + 8) != U32 (Data + 8)) ||
            ((U32 (Data + Header + 24) & 0x80000000) == 0)) { return EFI_LOAD_ERROR; }
        Found = TRUE;
        Status = ParseKernelHeader (Data, Size, Header, &Member);
        if (EFI_ERROR (Status) || (Member.Entry != Kernel->Entry)) { return EFI_LOAD_ERROR; }
        for (Index = 0; Index < Member.Count; Index++) {
          Child = &Member.Segments[Index];
          Covered = FALSE;
          for (Other = 0; Other < Kernel->Count; Other++) {
            Parent = &Kernel->Segments[Other];
            if ((Child->Address >= Parent->Address) &&
                (Child->Address - Parent->Address <= Parent->Size) &&
                (Child->Size <= Parent->Size - (Child->Address - Parent->Address)) &&
                ((Child->Protection & ~Parent->Protection) == 0) &&
                ((Child->FileSize == 0) ||
                 ((Child->Address - Parent->Address <= Parent->FileSize) &&
                  (Child->FileSize <= Parent->FileSize - (Child->Address - Parent->Address)) &&
                  (Child->FileOffset == Parent->FileOffset + Child->Address - Parent->Address)))) {
              Covered = TRUE;
            }
          }
          if (!Covered) { return EFI_LOAD_ERROR; }
        }
      }
    }
    Offset += Length;
  }
  return Found ? EFI_SUCCESS : EFI_LOAD_ERROR;
}

STATIC
BOOLEAN
AdtNode (CONST UINT8 *Data, UINTN Size, UINTN *Offset, UINTN Depth, UINTN ParentPath, UINTN *RamdiskOffset, UINTN *TrustCacheOffset, UINTN *AddonOffset, UINTN *PolicyOffset, UINT64 *WindowSize, BOOLEAN *KeepPacked)
{
  UINT32 Properties;
  UINT32 Children;
  UINT32 Length;
  UINTN  Index;
  UINTN  Path;
  UINTN  Candidate;
  UINTN  TrustCandidate;
  UINTN  AddonCandidate;
  UINTN  PolicyCandidate;
  UINTN  MemoryCandidate;
  CONST UINT8 *Name;
  UINTN  NameLength;

  Name = NULL;
  NameLength = 0;
  Candidate = MAX_UINTN;
  TrustCandidate = MAX_UINTN;
  AddonCandidate = MAX_UINTN;
  PolicyCandidate = MAX_UINTN;
  MemoryCandidate = MAX_UINTN;
  if ((Depth > 64) || (Size - *Offset < 8)) { return FALSE; }
  Properties = U32 (Data + *Offset);
  Children = U32 (Data + *Offset + 4);
  *Offset += 8;
  if (Properties > (Size - *Offset) / 36) { return FALSE; }
  for (Index = 0; Index < Properties; Index++) {
    if (Size - *Offset < 36) { return FALSE; }
    if (ScanMem8 (Data + *Offset, 32, 0) == NULL) { return FALSE; }
    Length = U32 (Data + *Offset + 32);
    *Offset += 36;
    if (Length > Size - *Offset) { return FALSE; }
    if (AsciiStrCmp ((CONST CHAR8 *)(Data + *Offset - 36), "name") == 0) {
      if (Name != NULL) { return FALSE; }
      Name = Data + *Offset;
      NameLength = Length;
    }
    if ((AsciiStrCmp ((CONST CHAR8 *)(Data + *Offset - 36), "RAMDisk") == 0) ||
        (AsciiStrCmp ((CONST CHAR8 *)(Data + *Offset - 36), "PackedRAMDisk") == 0)) {
      if (AsciiStrCmp ((CONST CHAR8 *)(Data + *Offset - 36), "PackedRAMDisk") == 0) {
        if (*KeepPacked) { return FALSE; }
        *KeepPacked = TRUE;
      }
      if ((Candidate != MAX_UINTN) || (Length != 16)) { return FALSE; }
      Candidate = *Offset;
    }
    if (AsciiStrCmp ((CONST CHAR8 *)(Data + *Offset - 36), "TrustCache") == 0) {
      if ((TrustCandidate != MAX_UINTN) || (Length != 16)) { return FALSE; }
      TrustCandidate = *Offset;
    }
    if (AsciiStrCmp ((CONST CHAR8 *)(Data + *Offset - 36), "GpuAddon") == 0) {
      if ((AddonCandidate != MAX_UINTN) || (Length != 16)) { return FALSE; }
      AddonCandidate = *Offset;
    }
    if (AsciiStrCmp ((CONST CHAR8 *)(Data + *Offset - 36), "RootPolicies") == 0) {
      if ((PolicyCandidate != MAX_UINTN) || (Length != 16)) { return FALSE; }
      PolicyCandidate = *Offset;
    }
    if (AsciiStrCmp ((CONST CHAR8 *)(Data + *Offset - 36), "darwinboot-memory-size") == 0) {
      if ((MemoryCandidate != MAX_UINTN) || (Length != 8)) { return FALSE; }
      MemoryCandidate = *Offset;
    }
    *Offset += Length;
    if (ALIGN_VALUE (*Offset, 4) > Size) { return FALSE; }
    *Offset = ALIGN_VALUE (*Offset, 4);
  }
  Path = 3;
  if (Depth == 0) { Path = 0; }
  if ((Depth == 1) && (ParentPath == 0) && (NameLength == 7) && (CompareMem (Name, "chosen", 7) == 0)) { Path = 1; }
  if ((Depth == 2) && (ParentPath == 1) && (NameLength == 11) && (CompareMem (Name, "memory-map", 11) == 0)) { Path = 2; }
  if ((Path == 2) && (Candidate != MAX_UINTN)) {
    if (*RamdiskOffset != MAX_UINTN) { return FALSE; }
    *RamdiskOffset = Candidate;
  }
  if ((Path == 2) && (TrustCandidate != MAX_UINTN)) {
    if (*TrustCacheOffset != MAX_UINTN) { return FALSE; }
    *TrustCacheOffset = TrustCandidate;
  }
  if ((Path == 2) && (AddonCandidate != MAX_UINTN)) {
    if (*AddonOffset != MAX_UINTN) { return FALSE; }
    *AddonOffset = AddonCandidate;
  }
  if (PolicyCandidate != MAX_UINTN) {
    if ((Path != 2) || (*PolicyOffset != MAX_UINTN)) { return FALSE; }
    *PolicyOffset = PolicyCandidate;
  }
  if (MemoryCandidate != MAX_UINTN) {
    if ((Path != 1) || (*WindowSize != 0)) { return FALSE; }
    *WindowSize = U64 (Data + MemoryCandidate);
    if (!DarwinWindowSizeValid (*WindowSize)) { return FALSE; }
  }
  if (Children > (Size - *Offset) / 8) { return FALSE; }
  for (Index = 0; Index < Children; Index++) {
    if (!AdtNode (Data, Size, Offset, Depth + 1, Path, RamdiskOffset, TrustCacheOffset, AddonOffset, PolicyOffset, WindowSize, KeepPacked)) { return FALSE; }
  }
  return TRUE;
}

STATIC
BOOLEAN
ValidTrustCaches (CONST UINT8 *Data, UINTN Size)
{
  UINTN Count;
  UINTN Index;
  UINTN Start;
  UINTN End;
  UINTN Entries;
  UINTN Entry;

  if (Size < 8) { return FALSE; }
  Count = U32 (Data);
  if ((Count == 0) || (Count > 128) || (Count > (Size - 4) / 4)) { return FALSE; }
  for (Index = 0; Index < Count; Index++) {
    Start = U32 (Data + 4 + Index * 4);
    End = (Index + 1 < Count) ? U32 (Data + 8 + Index * 4) : Size;
    if ((Start < 4 + Count * 4) || (Start & 3) || (End > Size) ||
        (End < Start) || (End - Start < 24) || (U32 (Data + Start) != 2)) { return FALSE; }
    Entries = U32 (Data + Start + 20);
    if ((Entries > (End - Start - 24) / 24) || (End - Start != 24 + Entries * 24)) { return FALSE; }
    for (Entry = 0; Entry < Entries; Entry++) {
      CONST UINT8 *Hash = Data + Start + 24 + Entry * 24;
      if ((Hash[20] < 1) || (Hash[20] > 4) ||
          ((Entry != 0) && (CompareMem (Hash - 24, Hash, 20) >= 0))) { return FALSE; }
    }
  }
  return TRUE;
}

STATIC
EFI_STATUS
GetMap (EFI_MEMORY_DESCRIPTOR **Map, UINTN *Capacity, UINTN *Size, UINTN *Key, UINTN *Stride)
{
  EFI_STATUS Status;
  UINT32     Version;
  UINTN      Attempt;

  for (Attempt = 0; Attempt < 3; Attempt++) {
    *Size = *Capacity;
    Status = gBS->GetMemoryMap (Size, *Map, Key, Stride, &Version);
    if (Status != EFI_BUFFER_TOO_SMALL) { return Status; }
    if (*Map != NULL) { FreePool (*Map); }
    *Capacity = *Size + 32 * sizeof (EFI_MEMORY_DESCRIPTOR);
    *Map = AllocatePool (*Capacity);
    if (*Map == NULL) { return EFI_OUT_OF_RESOURCES; }
  }
  return EFI_OUT_OF_RESOURCES;
}

// End of the run of EfiConventionalMemory that begins at Start: the UEFI map often lists physically
// adjacent free ranges as separate descriptors, so extend over every descriptor that continues the run.
STATIC
UINT64
RunEnd (EFI_MEMORY_DESCRIPTOR *Map, UINTN Size, UINTN Stride, UINT64 Start, UINT64 End)
{
  EFI_MEMORY_DESCRIPTOR *Descriptor;
  UINTN                 Offset;
  BOOLEAN               Extended;

  do {
    Extended = FALSE;
    for (Offset = 0; Offset + Stride <= Size; Offset += Stride) {
      Descriptor = (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)Map + Offset);
      if ((Descriptor->Type == EfiConventionalMemory) && (Descriptor->PhysicalStart == End) &&
          (Descriptor->NumberOfPages != 0) && (Descriptor->NumberOfPages < (MAX_UINT64 - End) / EFI_PAGE_SIZE)) {
        End += EFI_PAGES_TO_SIZE (Descriptor->NumberOfPages);
        Extended = TRUE;
      }
    }
  } while (Extended);
  (VOID)Start;
  return End;
}

// Large diagnostic text straight into the GOP framebuffer: the UEFI text console font is too small to
// photograph. 5x12 glyphs from DiagFont.h scaled 4x, white on a black box; wraps at the right edge.
#include "DiagFont.h"
STATIC CONST UINT64 mDiagFont[] = GLYPH_FONT;

STATIC
VOID
DiagDraw (CONST CHAR16 *Text, UINTN Row)
{
  EFI_GRAPHICS_OUTPUT_PROTOCOL *Gop;
  UINT64                       Video[6];
  UINTN                        Scale = 4, X = 0, Y, Index, Gx, Gy, Dx, Dy, Cell, Line;
  UINT32                       *Fb;
  UINT64                       Glyph, Data;
  CHAR16                       Ch;

  if (EFI_ERROR (gBS->LocateProtocol (&gEfiGraphicsOutputProtocolGuid, NULL, (VOID **)&Gop)) ||
      EFI_ERROR (DarwinBootVideoFromGop (Gop, Video))) { return; }
  Cell = 6 * Scale;
  Line = 14 * Scale;
  Y = Video[4] / 4 + Row * Line;
  Fb = (UINT32 *)(UINTN)Video[0];
  for (Index = 0; Text[Index] != 0; Index++) {
    Ch = Text[Index];
    if ((Ch < 32) || (Ch > 126)) { continue; }
    if (X + Cell > Video[3]) { X = 0; Y += Line; }
    if (Y + Line > Video[4]) { return; }
    Glyph = mDiagFont[Ch - 32];
    for (Gy = 0; Gy < 14 * Scale; Gy++) {
      for (Gx = 0; Gx < Cell; Gx++) {
        Fb[(Y + Gy) * (Video[2] / 4) + X + Gx] = 0xFF000000;
      }
    }
    for (Gy = 0; Gy < 12; Gy++) {
      Data = (Gy < 6) ? ((Glyph >> 32) >> (Gy * 5)) : ((Glyph & 0xFFFFFFFFULL) >> ((Gy - 6) * 5));
      for (Gx = 0; Gx < 5; Gx++) {
        if ((Data >> Gx) & 1) {
          for (Dy = 0; Dy < Scale; Dy++) {
            for (Dx = 0; Dx < Scale; Dx++) {
              Fb[(Y + Gy * Scale + Dy) * (Video[2] / 4) + X + Gx * Scale + Dx] = 0xFFFFFFFF;
            }
          }
        }
      }
    }
    X += Cell;
  }
}

STATIC
EFI_STATUS
AllocateWindow (KERNEL *Kernel, UINT64 WindowSize, EFI_PHYSICAL_ADDRESS *Address)
{
  EFI_MEMORY_DESCRIPTOR *Map;
  EFI_MEMORY_DESCRIPTOR *Descriptor;
  EFI_STATUS            Status;
  UINTN                 Capacity;
  UINTN                 Size;
  UINTN                 Key;
  UINTN                 Stride;
  UINTN                 Offset;
  UINT64                End;
  UINT64                Candidate;
  UINT64                BestStart;
  UINT64                BestBytes;
  UINT64                RunBytes;
  UINT64                Total;
  UINT64                Aligned;
  EFI_PHYSICAL_ADDRESS  Raw;
  EFI_PHYSICAL_ADDRESS  Limit;

  *Address = 0;
  /*
   * H236bs: the device's UEFI map exposes a stable low 1.5 GiB conventional
   * run at 0xA0000000 (printed by the failure diagnostic). The firmware
   * rejects both the exact per-run AllocateAddress and AllocateMaxAddress for
   * a 256 MiB loader allocation, so try the two page/2MiB-aligned bases of
   * that run directly before falling back to the map walk.
   */
  {
    static const UINT64 Fixed[] = { 0xA0000000ULL, 0xA0004000ULL, 0x100000000ULL, 0x180000000ULL };
    static const EFI_MEMORY_TYPE Types[] = { EfiLoaderCode, EfiLoaderData };
    for (UINTN TypeIndex = 0; TypeIndex < sizeof (Types) / sizeof (Types[0]); TypeIndex++) {
      for (UINTN FixedIndex = 0; FixedIndex < sizeof (Fixed) / sizeof (Fixed[0]); FixedIndex++) {
        Candidate = Fixed[FixedIndex];
        Status = gBS->AllocatePages (AllocateAddress, Types[TypeIndex],
                                     EFI_SIZE_TO_PAGES (WindowSize), &Candidate);
        if (!EFI_ERROR (Status)) {
          Print (L"DARWINBOOT: fixed window type=%u base=0x%lx\n",
                 (UINT32)TypeIndex, Candidate);
          *Address = Candidate;
          return EFI_SUCCESS;
        }
      }
    }
  }
  Map = NULL;
  Capacity = 0;
  BestStart = 0;
  BestBytes = 0;
  Status = GetMap (&Map, &Capacity, &Size, &Key, &Stride);
  if (EFI_ERROR (Status)) { if (Map != NULL) { FreePool (Map); } return Status; }
  Status = EFI_OUT_OF_RESOURCES;
  for (Offset = 0; Offset + Stride <= Size; Offset += Stride) {
    Descriptor = (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)Map + Offset);
    if ((Descriptor->Type != EfiConventionalMemory) || (Descriptor->NumberOfPages == 0)) { continue; }
    End = RunEnd (Map, Size, Stride, Descriptor->PhysicalStart,
                  Descriptor->PhysicalStart + EFI_PAGES_TO_SIZE (Descriptor->NumberOfPages));
    RunBytes = End - Descriptor->PhysicalStart;
    if (RunBytes > BestBytes) { BestBytes = RunBytes; BestStart = Descriptor->PhysicalStart; }
    Candidate = ALIGN_VALUE (Descriptor->PhysicalStart, BLOCK_SIZE) + (Kernel->Base & (BLOCK_SIZE - 1));
    if ((Candidate < Descriptor->PhysicalStart) || (End < Candidate) || (End - Candidate < WindowSize)) { continue; }
    Status = gBS->AllocatePages (AllocateAddress, EfiLoaderData, EFI_SIZE_TO_PAGES (WindowSize), &Candidate);
    if (!EFI_ERROR (Status)) { *Address = Candidate; break; }
  }
  /*
   * H236bq: the exact per-run AllocateAddress can be rejected by the firmware
   * even when the run is large enough. Fall back to AllocateMaxAddress and
   * align the base inside the allocation (sagit stageZap's model). The block
   * and the window must remain below 4 GiB so the ZAP stays low.
   */
  if (EFI_ERROR (Status)) {
    Total = WindowSize + BLOCK_SIZE;
    Limit = 0xFFFFFFFFULL;
    for (UINTN Attempt = 0; Attempt < 64; Attempt++) {
      Raw = Limit;
      Status = gBS->AllocatePages (AllocateMaxAddress, EfiLoaderData, EFI_SIZE_TO_PAGES (Total), &Raw);
      if (EFI_ERROR (Status)) { break; }
      Aligned = ALIGN_VALUE (Raw, BLOCK_SIZE) + (Kernel->Base & (BLOCK_SIZE - 1));
      if ((Aligned >= Raw) && ((Aligned - Raw) <= Total) &&
          (WindowSize <= Total - (Aligned - Raw)) && (Aligned + WindowSize <= 0x100000000ULL)) {
        *Address = Aligned;
        Status = EFI_SUCCESS;
        break;
      }
      gBS->FreePages (Raw, EFI_SIZE_TO_PAGES (Total));
      if (Raw < BLOCK_SIZE) { break; }
      Limit = Raw - 1;
    }
  }
  if (EFI_ERROR (Status)) {
    CHAR16 Line[96];
    UINTN  Row = 1;
    UnicodeSPrint (Line, sizeof (Line), L"NO WINDOW %lx BIG RUN %lx @ %lx", WindowSize, BestBytes, BestStart);
    DiagDraw (Line, 0);
    for (Offset = 0; Offset + Stride <= Size; Offset += Stride) {
      Descriptor = (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)Map + Offset);
      if ((Descriptor->Type == EfiConventionalMemory) && (Descriptor->NumberOfPages >= 0x400) && (Row < 8)) {
        UnicodeSPrint (Line, sizeof (Line), L"FREE %lx + %lx", Descriptor->PhysicalStart, EFI_PAGES_TO_SIZE (Descriptor->NumberOfPages));
        DiagDraw (Line, Row++);
      }
    }

  }
  FreePool (Map);
  return Status;
}

/*
 * H236bv: sagit-ios-port's stageZap recipe. Allocate below 4 GiB with
 * AllocateMaxAddress, over-allocate by (alignment - 4096) so the base can be
 * aligned inside the reservation, and lower the limit if the aligned range
 * would cross 4 GiB. The ZAP buffer is outside the kernel window; only the
 * boot stage reserves it.
 */
typedef struct {
  UINT64  Raw;
  UINT64  Total;
  UINT64  Address;
  UINT64  Usable;
} LOW_ALLOC;

STATIC
VOID
FreeLow (
  LOW_ALLOC *Alloc
  )
{
  if ((Alloc != NULL) && (Alloc->Raw != 0) && (Alloc->Total != 0)) {
    gBS->FreePages (Alloc->Raw, EFI_SIZE_TO_PAGES (Alloc->Total));
  }
  if (Alloc != NULL) {
    ZeroMem (Alloc, sizeof (*Alloc));
  }
}

STATIC
EFI_STATUS
AllocateLow (
  UINT64     Usable,
  UINT64     Alignment,
  UINT64     Attributes,
  BOOLEAN    Zero,
  LOW_ALLOC  *Alloc
  )
{
  EFI_STATUS             Status;
  EFI_CPU_ARCH_PROTOCOL  *Cpu;
  EFI_PHYSICAL_ADDRESS   Raw;
  UINT64                 Total;
  UINT64                 Limit;
  UINT64                 Aligned;
  UINTN                  Attempt;

  if ((Alloc == NULL) || (Usable == 0) || (Alignment < EFI_PAGE_SIZE) ||
      ((Alignment & (Alignment - 1)) != 0) ||
      (Usable > MAX_UINT64 - Alignment + EFI_PAGE_SIZE)) {
    return EFI_INVALID_PARAMETER;
  }
  ZeroMem (Alloc, sizeof (*Alloc));
  Total = Usable + Alignment - EFI_PAGE_SIZE;
  Cpu = NULL;
  if (Attributes != 0) {
    EFI_GUID  CpuGuid = EFI_CPU_ARCH_PROTOCOL_GUID;
    Status = gBS->LocateProtocol (&CpuGuid, NULL, (VOID **)&Cpu);
    if (EFI_ERROR (Status)) { Cpu = NULL; }
  }
  Limit = 0xFFFFFFFFULL;
  for (Attempt = 0; Attempt < 64; Attempt++) {
    Raw = Limit;
    Status = gBS->AllocatePages (AllocateMaxAddress, EfiLoaderData,
                                 EFI_SIZE_TO_PAGES (Total), &Raw);
    if (EFI_ERROR (Status)) { return Status; }
    Aligned = ALIGN_VALUE (Raw, Alignment);
    if ((Aligned < Raw) || (Aligned - Raw > Total) ||
        (Usable > Total - (Aligned - Raw)) ||
        (Aligned > 0xFFFFFFFFULL) || (Usable > 0x100000000ULL - Aligned)) {
      gBS->FreePages (Raw, EFI_SIZE_TO_PAGES (Total));
      if (Raw < Alignment) { break; }
      Limit = Raw - 1;
      continue;
    }
    if (Cpu != NULL) {
      Status = Cpu->FlushDataCache (Cpu, Raw, Total, EfiCpuFlushTypeWriteBackInvalidate);
      if (EFI_ERROR (Status)) {
        gBS->FreePages (Raw, EFI_SIZE_TO_PAGES (Total));
        return Status;
      }
      if (Attributes != 0) {
        Status = Cpu->SetMemoryAttributes (Cpu, Raw, Total, Attributes);
        if (EFI_ERROR (Status)) {
          Cpu->SetMemoryAttributes (Cpu, Raw, Total, EFI_MEMORY_WB);
          gBS->FreePages (Raw, EFI_SIZE_TO_PAGES (Total));
          return Status;
        }
      }
    }
    if (Zero) { ZeroMem ((VOID *)(UINTN)Aligned, (UINTN)Usable); }
    Alloc->Raw = Raw;
    Alloc->Total = Total;
    Alloc->Address = Aligned;
    Alloc->Usable = Usable;
    Print (L"DARWINBOOT: low alloc base=0x%lx raw=0x%lx total=0x%lx\n",
           Aligned, Raw, Total);
    return EFI_SUCCESS;
  }
  return EFI_OUT_OF_RESOURCES;
}

STATIC
EFI_STATUS
ReadFileLow (
  EFI_FILE_PROTOCOL *Root,
  CONST CHAR16      *Path,
  UINTN             Limit,
  VOID              **Data,
  UINTN             *Size,
  LOW_ALLOC         *Alloc
  )
{
  EFI_STATUS         Status;
  EFI_FILE_PROTOCOL  *File;
  EFI_FILE_INFO      *Info;
  UINTN              InfoSize;
  UINTN              ReadSize;

  if ((Root == NULL) || (Path == NULL) || (Data == NULL) || (Size == NULL) || (Alloc == NULL)) {
    return EFI_INVALID_PARAMETER;
  }
  *Data = NULL;
  *Size = 0;
  Status = Root->Open (Root, &File, (CHAR16 *)Path, EFI_FILE_MODE_READ, 0);
  if (EFI_ERROR (Status)) { return Status; }
  InfoSize = SIZE_OF_EFI_FILE_INFO + 512;
  Info = AllocatePool (InfoSize);
  if (Info == NULL) { File->Close (File); return EFI_OUT_OF_RESOURCES; }
  Status = File->GetInfo (File, &gEfiFileInfoGuid, &InfoSize, Info);
  if (EFI_ERROR (Status)) { FreePool (Info); File->Close (File); return Status; }
  if (Info->FileSize > Limit) { FreePool (Info); File->Close (File); return EFI_BAD_BUFFER_SIZE; }
  Status = AllocateLow (Info->FileSize, EFI_PAGE_SIZE, 0, FALSE, Alloc);
  if (EFI_ERROR (Status)) { FreePool (Info); File->Close (File); return Status; }
  ReadSize = Info->FileSize;
  Status = File->Read (File, &ReadSize, (VOID *)(UINTN)Alloc->Address);
  FreePool (Info);
  File->Close (File);
  if (EFI_ERROR (Status) || (ReadSize != Alloc->Usable)) {
    FreeLow (Alloc);
    return EFI_ERROR (Status) ? Status : EFI_BAD_BUFFER_SIZE;
  }
  *Data = (VOID *)(UINTN)Alloc->Address;
  *Size = ReadSize;
  return EFI_SUCCESS;
}

STATIC
EFI_STATUS
EFIAPI
Boot (
  IN UNIXNU_LOADER_PROTOCOL    *This,
  IN CONST UNIXNU_LOADER_BOOT_REQUEST *Request
  )
{
  EFI_STATUS                      Status;
  EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  *Fs;
  EFI_FILE_PROTOCOL               *Root;
  VOID                            *Image;
  VOID                            *Tree;
  VOID                            *TrustCaches;
  VOID                            *Addon;
  UINTN                           ImageSize;
  UINTN                           TreeSize;
  UINTN                           TrustCacheSize;
  UINTN                           AddonSize;
  CHAR16                          *TreePath;
  UINTN                           Length;
  UINTN                           Index;
  UINTN                           Offset;
  KERNEL                          Kernel;
  EFI_PHYSICAL_ADDRESS            Address;
  UINT64                          ArgsAddress;
  UINT64                          TreeAddress;
  UINT64                          Used;
  UINT64                          WindowSize;
  UINT64                          RamdiskAddress;
  UINTN                           RamdiskOffset;
  UINTN                           RamdiskBytes;
  UINTN                           RamdiskExpandedSize;
  BOOLEAN                         RamdiskPacked;
  BOOLEAN                         KeepPacked;
  UINTN                           TrustCacheOffset;
  UINT64                          TrustCacheAddress;
  UINTN                           AddonOffset;
  UINT64                          AddonAddress;
  VOID                            *Policies;
  UINTN                           PolicySize;
  UINTN                           PolicyOffset;
  UINT64                          PolicyAddress;
  UINT64                          ZapAddress;
  LOW_ALLOC                       ZapAlloc;
  LOW_ALLOC                       ImageAlloc;
  LOW_ALLOC                       TreeAlloc;
  LOW_ALLOC                       TrustAlloc;
  LOW_ALLOC                       RamdiskAlloc;
  LOW_ALLOC                       AddonAlloc;
  LOW_ALLOC                       PolicyAlloc;
  BOOLEAN                         LowSidecars;
  UINT64                          InitialWindow;
  DARWIN_BOOT_ARGS                *Args;
  EFI_MEMORY_DESCRIPTOR           *Map;
  UINTN                           Capacity;
  UINTN                           MapSize;
  UINTN                           Key;
  UINTN                           Stride;
  UINT32                          Version;
  UINTN                           Attempt;
  CHAR8                           CommandLine[1024];
  UINT64                          Video[6];
  CHAR16                          Diag[96];

  (VOID)This;
  if ((Request == NULL) || (Request->Volume == NULL) || (Request->KernelPath == NULL)) { return EFI_INVALID_PARAMETER; }
  if ((Request->KextCount != 0) || (Request->DeviceTree != NULL) || (Request->DeviceTreeSize != 0) ||
      (DarwinCurrentEl () != 4)) {
    Print (L"DARWINBOOT: unsupported inputs or exception level; firmware retained\n");
    return EFI_UNSUPPORTED;
  }
  if (!RamdiskLayout (Request->Ramdisk, Request->RamdiskSize, &RamdiskExpandedSize, &RamdiskPacked)) {
    Print (L"DARWINBOOT: ramdisk layout rejected, %lu bytes\n", (UINT64)Request->RamdiskSize);
    return EFI_BAD_BUFFER_SIZE;
  }
  ZeroMem (CommandLine, sizeof (CommandLine));
  if (Request->BootArgs != NULL) {
    for (Index = 0; Request->BootArgs[Index] != 0; Index++) {
      if ((Index >= sizeof (CommandLine) - 1) || (Request->BootArgs[Index] > 0x7f)) {
        Print (L"DARWINBOOT: boot args rejected at %lu\n", (UINT64)Index);
        return EFI_BAD_BUFFER_SIZE;
      }
      CommandLine[Index] = (CHAR8)Request->BootArgs[Index];
    }
  }
  Root = NULL;
  Image = NULL;
  Tree = NULL;
  TrustCaches = NULL;
  Addon = NULL;
  AddonSize = 0;
  Policies = NULL;
  PolicySize = 0;
  TreePath = NULL;
  Map = NULL;
  Address = 0;
  Capacity = 0;
  ZeroMem (&ZapAlloc, sizeof (ZapAlloc));
  ZeroMem (&ImageAlloc, sizeof (ImageAlloc));
  ZeroMem (&TreeAlloc, sizeof (TreeAlloc));
  ZeroMem (&TrustAlloc, sizeof (TrustAlloc));
  ZeroMem (&RamdiskAlloc, sizeof (RamdiskAlloc));
  ZeroMem (&AddonAlloc, sizeof (AddonAlloc));
  ZeroMem (&PolicyAlloc, sizeof (PolicyAlloc));
  LowSidecars = FALSE;
  InitialWindow = 0;
  Status = gBS->HandleProtocol (Request->Volume, &gEfiSimpleFileSystemProtocolGuid, (VOID **)&Fs);
  if (EFI_ERROR (Status)) { return Status; }
  Status = Fs->OpenVolume (Fs, &Root);
  if (EFI_ERROR (Status)) { return Status; }
  Status = ReadFileLow (Root, Request->KernelPath, SIZE_128MB, &Image, &ImageSize, &ImageAlloc);
  if (EFI_ERROR (Status)) { goto Fail; }
  Status = ParseKernel (Image, ImageSize, &Kernel);
  if (EFI_ERROR (Status)) { goto Fail; }
  Length = StrSize (Request->KernelPath);
  TreePath = AllocatePool (Length + 11 * sizeof (CHAR16));
  if (TreePath == NULL) { Status = EFI_OUT_OF_RESOURCES; goto Fail; }
  CopyMem (TreePath, Request->KernelPath, Length);
  StrCatS (TreePath, Length / sizeof (CHAR16) + 11, L".adt");
  Status = ReadFileLow (Root, TreePath, SIZE_16MB, &Tree, &TreeSize, &TreeAlloc);
  if (EFI_ERROR (Status)) { goto Fail; }
  Offset = 0;
  RamdiskOffset = MAX_UINTN;
  TrustCacheOffset = MAX_UINTN;
  AddonOffset = MAX_UINTN;
  PolicyOffset = MAX_UINTN;
  WindowSize = 0;
  KeepPacked = FALSE;
  if (!AdtNode (Tree, TreeSize, &Offset, 0, 3, &RamdiskOffset, &TrustCacheOffset, &AddonOffset, &PolicyOffset, &WindowSize, &KeepPacked) || (Offset != TreeSize)) { Status = EFI_COMPROMISED_DATA; goto Fail; }
  if (KeepPacked && (!RamdiskPacked || (RamdiskOffset == MAX_UINTN))) { Status = EFI_COMPROMISED_DATA; goto Fail; }
  if (WindowSize == 0) { WindowSize = WINDOW_SIZE; }
  if (WindowSize > (192ULL * 1024 * 1024)) { WindowSize = 192ULL * 1024 * 1024; }
  if (Kernel.Base > MAX_UINT64 - WindowSize) { Status = EFI_LOAD_ERROR; goto Fail; }
  if (Request->Ramdisk != NULL) {
    if ((RamdiskOffset == MAX_UINTN) || (U64 ((UINT8 *)Tree + RamdiskOffset) != 0) ||
        (U64 ((UINT8 *)Tree + RamdiskOffset + 8) != 0)) { Status = EFI_COMPROMISED_DATA; goto Fail; }
  } else if (RamdiskOffset != MAX_UINTN) {
    Status = EFI_UNSUPPORTED;
    goto Fail;
  }
  CopyMem (TreePath, Request->KernelPath, Length);
  StrCatS (TreePath, Length / sizeof (CHAR16) + 11, L".trustcache");
  Status = ReadFileLow (Root, TreePath, SIZE_16MB, &TrustCaches, &TrustCacheSize, &TrustAlloc);
  if (EFI_ERROR (Status) && (Status != EFI_NOT_FOUND)) { goto Fail; }
  if (TrustCaches != NULL) {
    if ((TrustCacheOffset == MAX_UINTN) || (U64 ((UINT8 *)Tree + TrustCacheOffset) != 0) ||
        (U64 ((UINT8 *)Tree + TrustCacheOffset + 8) != 0) || !ValidTrustCaches (TrustCaches, TrustCacheSize)) {
      Status = EFI_COMPROMISED_DATA;
      goto Fail;
    }
  } else if (TrustCacheOffset != MAX_UINTN) {
    Status = EFI_COMPROMISED_DATA;
    goto Fail;
  }
  //
  // The GPU addon (kernel.macho.gpuaddon, scripts/make-gpu-addon.py): files the kernel writes into the Data volume before its addon
  // mounts. Only its header is checked here; the kernel validates every entry.
  //
  CopyMem (TreePath, Request->KernelPath, Length);
  StrCatS (TreePath, Length / sizeof (CHAR16) + 11, L".gpuaddon");
  Status = ReadFile (Root, TreePath, SIZE_64MB, &Addon, &AddonSize);
  if (EFI_ERROR (Status) && (Status != EFI_NOT_FOUND)) { goto Fail; }
  if (Addon != NULL) {
    if ((AddonOffset == MAX_UINTN) || (U64 ((UINT8 *)Tree + AddonOffset) != 0) || (U64 ((UINT8 *)Tree + AddonOffset + 8) != 0) ||
        (AddonSize < 24) || (CompareMem (Addon, "NGPUADD2", 8) != 0) || (U64 ((UINT8 *)Addon + 16) != AddonSize)) {
      Status = EFI_COMPROMISED_DATA;
      goto Fail;
    }
  } else if (AddonOffset != MAX_UINTN) {
    Status = EFI_COMPROMISED_DATA;
    goto Fail;
  }
  // Root hash tables live outside the kernel's coalesced constant segments.
  // The kernel authenticates each envelope against its compiled owner anchor.
  CopyMem (TreePath, Request->KernelPath, Length);
  StrCatS (TreePath, Length / sizeof (CHAR16) + 11, L".vroot");
  Status = ReadFile (Root, TreePath, SIZE_128MB, &Policies, &PolicySize);
  if (EFI_ERROR (Status) && (Status != EFI_NOT_FOUND)) { goto Fail; }
  if (Policies != NULL) {
    if ((PolicyOffset == MAX_UINTN) || (U64 ((UINT8 *)Tree + PolicyOffset) != 0) ||
        (U64 ((UINT8 *)Tree + PolicyOffset + 8) != 0) || (PolicySize < 32) ||
        (CompareMem (Policies, "VROOTB01", 8) != 0) || (U64 ((UINT8 *)Policies + 8) != 1) ||
        (U64 ((UINT8 *)Policies + 16) == 0) || (U64 ((UINT8 *)Policies + 16) > 16) ||
        (U64 ((UINT8 *)Policies + 24) != PolicySize)) {
      Status = EFI_COMPROMISED_DATA;
      goto Fail;
    }
  } else if (PolicyOffset != MAX_UINTN) {
    Status = EFI_COMPROMISED_DATA;
    goto Fail;
  }
  Status = ReadBootVideo (Video);
  if (EFI_ERROR (Status)) { goto Fail; }

  /*
   * H236bv: reserve the ZAP image outside the XNU arena, using sagit's
   * stageZap recipe (AllocateMaxAddress < 4 GiB, over-allocate by alignment,
   * align inside the reservation, then UC/XP). The kernel maps this through
   * zap-base; it is not part of the kernel window.
   */
  /*
   * H236bw: keep the ZAP allocation WB/normal. The H236bv boot faulted at
   * 0x17ABAC18 (a >4 GiB Image/Addon pool) after the UC|XP SetMemoryAttributes
   * call; the kernel maps zap-base with kIOMapInhibitCache and cleans the
   * .mdt/.b02 before PAS, so the boot-stage UC is not required for the probe.
   */
  Status = AllocateLow (2 * SIZE_1MB, SIZE_1MB, 0, TRUE, &ZapAlloc);
  if (EFI_ERROR (Status)) {
    UnicodeSPrint (Diag, sizeof (Diag), L"NO ZAP ALLOC %r", Status);
    DiagDraw (Diag, 2);
    gBS->Stall (15000000);
    goto Fail;
  }
  ZapAddress = ZapAlloc.Address;
  UnicodeSPrint (Diag, sizeof (Diag), L"ZAP LOW 0x%lx/0x%lx",
                 ZapAddress, ZapAlloc.Raw);

  /*
   * Try 192 MiB first; if the firmware's per-call limit is 128 MiB, retry at
   * 128 MiB and put the ramdisk/addon/policy below 4 GiB. The ZAP already
   * stays outside either window.
   */
  InitialWindow = WindowSize;
  Status = AllocateWindow (&Kernel, WindowSize, &Address);
  if (EFI_ERROR (Status) && (InitialWindow > (128ULL * 1024 * 1024))) {
    WindowSize = 128ULL * 1024 * 1024;
    ZeroMem (&Address, sizeof (Address));
    Status = AllocateWindow (&Kernel, WindowSize, &Address);
    if (!EFI_ERROR (Status)) { LowSidecars = TRUE; }
  }
  if (EFI_ERROR (Status)) {
    UnicodeSPrint (Diag, sizeof (Diag), L"NO KERNEL WINDOW %r size=0x%lx", Status, WindowSize);
    DiagDraw (Diag, 1);
    gBS->Stall (15000000);
    goto Fail;
  }
  UnicodeSPrint (Diag, sizeof (Diag), L"WIN 0x%lx sz 0x%lx low %u",
                 Address, (UINT64)WindowSize, LowSidecars ? 1 : 0);
  /*
   * H236cc: keep the 192 MiB window for the kernel/args/ADT/trust only.
   * The ramdisk/addon/policy go low via AllocateLow even when 192 succeeds,
   * leaving ~139 MiB of early XNU boot memory instead of ~24 MiB.
   */
  LowSidecars = TRUE;
  ArgsAddress = ALIGN_VALUE (Address + Kernel.End - Kernel.Base, SIZE_16KB);
  TreeAddress = ArgsAddress + EFI_PAGE_SIZE;
  if (LowSidecars) {
    TrustCacheAddress = ALIGN_VALUE (TreeAddress + TreeSize, SIZE_16KB);
    if (Request->Ramdisk != NULL) {
      Status = AllocateLow (KeepPacked ? Request->RamdiskSize : RamdiskExpandedSize,
                            EFI_PAGE_SIZE, 0, FALSE, &RamdiskAlloc);
      if (EFI_ERROR (Status)) {
        UnicodeSPrint (Diag, sizeof (Diag), L"NO RAMDISK LOW %r", Status);
        DiagDraw (Diag, 3);
        gBS->Stall (15000000);
        goto Fail;
      }
      if (KeepPacked) {
        CopyMem ((VOID *)(UINTN)RamdiskAlloc.Address, Request->Ramdisk, Request->RamdiskSize);
      } else {
        CopyRamdisk ((VOID *)(UINTN)RamdiskAlloc.Address, Request->Ramdisk,
                     Request->RamdiskSize, RamdiskPacked);
      }
      RamdiskAddress = RamdiskAlloc.Address;
      RamdiskBytes = RamdiskAlloc.Usable;
    } else {
      RamdiskAddress = 0;
      RamdiskBytes = 0;
    }
    if (Addon != NULL) {
      Status = AllocateLow (AddonSize, EFI_PAGE_SIZE, 0, FALSE, &AddonAlloc);
      if (EFI_ERROR (Status)) {
        UnicodeSPrint (Diag, sizeof (Diag), L"NO ADDON LOW %r", Status);
        DiagDraw (Diag, 3);
        gBS->Stall (15000000);
        goto Fail;
      }
      CopyMem ((VOID *)(UINTN)AddonAlloc.Address, Addon, AddonSize);
      AddonAddress = AddonAlloc.Address;
      FreePool (Addon); Addon = NULL;
    } else {
      AddonAddress = 0;
    }
    if (Policies != NULL) {
      Status = AllocateLow (PolicySize, EFI_PAGE_SIZE, 0, FALSE, &PolicyAlloc);
      if (EFI_ERROR (Status)) {
        UnicodeSPrint (Diag, sizeof (Diag), L"NO POLICY LOW %r", Status);
        DiagDraw (Diag, 3);
        gBS->Stall (15000000);
        goto Fail;
      }
      CopyMem ((VOID *)(UINTN)PolicyAlloc.Address, Policies, PolicySize);
      PolicyAddress = PolicyAlloc.Address;
      FreePool (Policies); Policies = NULL;
    } else {
      PolicyAddress = 0;
    }
    Used = ALIGN_VALUE (TrustCacheAddress + TrustCacheSize, SIZE_16KB) - Address;
  } else {
    RamdiskAddress = ALIGN_VALUE (TreeAddress + TreeSize, EFI_PAGE_SIZE);
    RamdiskBytes = ALIGN_VALUE (KeepPacked ? Request->RamdiskSize : RamdiskExpandedSize, EFI_PAGE_SIZE);
    TrustCacheAddress = RamdiskAddress + RamdiskBytes;
    if (Addon != NULL) {
      AddonAddress = ALIGN_VALUE (TrustCacheAddress + TrustCacheSize, SIZE_16KB);
      PolicyAddress = ALIGN_VALUE (AddonAddress + AddonSize, SIZE_16KB);
    } else {
      AddonAddress = 0;
      PolicyAddress = ALIGN_VALUE (TrustCacheAddress + TrustCacheSize, SIZE_16KB);
    }
    if (Policies == NULL) { PolicyAddress = 0; }
    Used = ALIGN_VALUE ((PolicyAddress != 0) ? (PolicyAddress + PolicySize) :
                        ((AddonAddress != 0) ? (AddonAddress + AddonSize) :
                         (TrustCacheAddress + TrustCacheSize)), SIZE_16KB) - Address;
  }
  UnicodeSPrint (Diag, sizeof (Diag), L"IMG 0x%lx ADD 0x%lx POL 0x%lx RAM 0x%lx",
                 (UINT64)(UINTN)Image, AddonAddress, PolicyAddress, RamdiskAddress);
  UnicodeSPrint (Diag, sizeof (Diag), L"USED 0x%lx LIM 0x%lx",
                 Used, Address + WindowSize);
  if (Used > WindowSize - BLOCK_SIZE) {
    Print (L"DARWINBOOT: used %lu window %lu kernel %lu ramdisk %lu\n", (UINT64)Used, (UINT64)WindowSize, (UINT64)(Kernel.End - Kernel.Base), (UINT64)RamdiskBytes);
    Status = EFI_BAD_BUFFER_SIZE;
    goto Fail;
  }
  ZeroMem ((VOID *)(UINTN)ArgsAddress, sizeof (DARWIN_BOOT_ARGS));
  for (Index = 0; Index < Kernel.Count; Index++) {
    CopyMem ((VOID *)(UINTN)(Address + Kernel.Segments[Index].Address - Kernel.Base),
             (UINT8 *)Image + Kernel.Segments[Index].FileOffset, (UINTN)Kernel.Segments[Index].FileSize);
    if (Kernel.Segments[Index].Size > Kernel.Segments[Index].FileSize) {
      ZeroMem ((VOID *)(UINTN)(Address + Kernel.Segments[Index].Address - Kernel.Base +
                             Kernel.Segments[Index].FileSize),
               (UINTN)(Kernel.Segments[Index].Size - Kernel.Segments[Index].FileSize));
    }
  }
  Args = (DARWIN_BOOT_ARGS *)(UINTN)ArgsAddress;
  Args->Revision = 2;
  Args->Version = 2;
  Args->VirtualBase = Kernel.Base;
  Args->PhysicalBase = Address;
  Args->MemorySize = WindowSize;
  Args->MemorySizeActual = WindowSize;
  Args->TopOfKernelData = Address + Used;
  CopyMem (Args->Video, Video, sizeof (Video));
  Args->DeviceTree = Kernel.Base + TreeAddress - Address;
  Args->DeviceTreeLength = (UINT32)TreeSize;
  if (AsciiStrLen (CommandLine) + 32 < sizeof (CommandLine)) {
    AsciiSPrint (CommandLine + AsciiStrLen (CommandLine),
                 sizeof (CommandLine) - AsciiStrLen (CommandLine),
                 " zap-base=0x%lx", ZapAddress);
  }
  CopyMem (Args->CommandLine, CommandLine, sizeof (CommandLine));
  CopyMem ((VOID *)(UINTN)TreeAddress, Tree, TreeSize);
  if ((Request->Ramdisk != NULL) && (RamdiskOffset != MAX_UINTN) && (RamdiskAddress != 0)) {
    if (!LowSidecars) {
      if (KeepPacked) { CopyMem ((VOID *)(UINTN)RamdiskAddress, Request->Ramdisk, Request->RamdiskSize); }
      else { CopyRamdisk ((VOID *)(UINTN)RamdiskAddress, Request->Ramdisk, Request->RamdiskSize, RamdiskPacked); }
    }
    WriteUnaligned64 ((UINT64 *)(UINTN)(TreeAddress + RamdiskOffset), RamdiskAddress);
    WriteUnaligned64 ((UINT64 *)(UINTN)(TreeAddress + RamdiskOffset + 8), RamdiskBytes);
  }
  if ((TrustCaches != NULL) && (TrustCacheOffset != MAX_UINTN)) {
    CopyMem ((VOID *)(UINTN)TrustCacheAddress, TrustCaches, TrustCacheSize);
    WriteUnaligned64 ((UINT64 *)(UINTN)(TreeAddress + TrustCacheOffset), TrustCacheAddress);
    WriteUnaligned64 ((UINT64 *)(UINTN)(TreeAddress + TrustCacheOffset + 8), TrustCacheSize);
    TrustCaches = NULL;
  }
  if ((AddonAddress != 0) && (AddonOffset != MAX_UINTN) && (Addon != NULL)) {
    CopyMem ((VOID *)(UINTN)AddonAddress, Addon, AddonSize);
    WriteUnaligned64 ((UINT64 *)(UINTN)(TreeAddress + AddonOffset), AddonAddress);
    WriteUnaligned64 ((UINT64 *)(UINTN)(TreeAddress + AddonOffset + 8), AddonSize);
    FreePool (Addon); Addon = NULL;
  }
  if ((PolicyAddress != 0) && (PolicyOffset != MAX_UINTN) && (Policies != NULL)) {
    CopyMem ((VOID *)(UINTN)PolicyAddress, Policies, PolicySize);
    WriteUnaligned64 ((UINT64 *)(UINTN)(TreeAddress + PolicyOffset), PolicyAddress);
    WriteUnaligned64 ((UINT64 *)(UINTN)(TreeAddress + PolicyOffset + 8), PolicySize);
    FreePool (Policies); Policies = NULL;
  }
  Tree = NULL;
  FreePool (TreePath); TreePath = NULL;
  Root->Close (Root); Root = NULL;
  Status = GetMap (&Map, &Capacity, &MapSize, &Key, &Stride);
  if (EFI_ERROR (Status)) { goto Fail; }

  for (Attempt = 0; Attempt < 3; Attempt++) {
    MapSize = Capacity;
    Status = gBS->GetMemoryMap (&MapSize, Map, &Key, &Stride, &Version);
    if (EFI_ERROR (Status)) {
      if (Attempt == 0) { goto Fail; }
      break;
    }
    Status = gBS->ExitBootServices (mImage, Key);
    if (!EFI_ERROR (Status)) {
      DarwinEnter (ArgsAddress, Address + Kernel.Entry - Kernel.Base, Address, WindowSize, Video[0], Video[2] * Video[4]);
      CpuDeadLoop ();
    }
    if (Status != EFI_INVALID_PARAMETER) { break; }
  }
  /*
   * H236ce: if ExitBootServices never succeeds, nothing after this point can
   * use the console, so report it in the large direct-framebuffer font. This
   * is a failure diagnostic only; the success path draws nothing but the
   * thin handoff checkpoint in Entry.S.
   */
  UnicodeSPrint (Diag, sizeof (Diag), L"NO EBS %r try %lu key %lu",
                 Status, (UINT64)Attempt, (UINT64)Key);
  DiagDraw (Diag, 1);
  CpuDeadLoop ();
  return EFI_ABORTED;
Fail:
  if (Root != NULL) { Root->Close (Root); }
  FreeLow (&ImageAlloc);
  FreeLow (&TreeAlloc);
  FreeLow (&TrustAlloc);
  if (Addon != NULL) { FreePool (Addon); }
  if (Policies != NULL) { FreePool (Policies); }
  if (TreePath != NULL) { FreePool (TreePath); }
  if (Map != NULL) { FreePool (Map); }
  FreeLow (&RamdiskAlloc);
  FreeLow (&AddonAlloc);
  FreeLow (&PolicyAlloc);
  FreeLow (&ZapAlloc);
  if (Address != 0) { gBS->FreePages (Address, EFI_SIZE_TO_PAGES (WindowSize)); }
  Print (L"DARWINBOOT: boot refused: %r; firmware retained\n", Status);
  return Status;
}

STATIC UNIXNU_LOADER_PROTOCOL mLoader = { UNIXNU_LOADER_REVISION, Boot };

STATIC
EFI_STATUS
EFIAPI
Unload (EFI_HANDLE ImageHandle)
{
  return gBS->UninstallMultipleProtocolInterfaces (ImageHandle, &gUniXNULoaderProtocolGuid, &mLoader, NULL);
}

EFI_STATUS
EFIAPI
DarwinBootEntry (EFI_HANDLE ImageHandle, EFI_SYSTEM_TABLE *SystemTable)
{
  EFI_LOADED_IMAGE_PROTOCOL *Loaded;
  EFI_STATUS               Status;
  VOID                     *Existing;

  (VOID)SystemTable;
  Status = gBS->LocateProtocol (&gUniXNULoaderProtocolGuid, NULL, &Existing);
  if (!EFI_ERROR (Status)) { return EFI_ALREADY_STARTED; }
  Status = gBS->HandleProtocol (ImageHandle, &gEfiLoadedImageProtocolGuid, (VOID **)&Loaded);
  if (EFI_ERROR (Status)) { return Status; }
  mImage = ImageHandle;
  Status = gBS->InstallMultipleProtocolInterfaces (&ImageHandle, &gUniXNULoaderProtocolGuid, &mLoader, NULL);
  if (!EFI_ERROR (Status)) {
    Loaded->Unload = Unload;
    Print (L"DARWINBOOT: loader v2 installed EL%u\n", (UINT32)(DarwinCurrentEl () >> 2));
  }
  return Status;
}
