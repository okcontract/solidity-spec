/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Contents
import Solidity.Core.Aggregates.CopySource
import Solidity.Core.Aggregates.Defaults
import Solidity.Core.Aggregates.StorageArrays
import Solidity.Core.Conversions

/-! Checked assignment consumes the location/shape planner. Fresh-memory targets
use finite packets with source-specific decoding/allocation check order.
Storage-target copies stream in native helper order, including source-word buffering,
and retain concrete hash collisions and wrapped addresses. These operations describe the source model; they do not establish
compiler lowering preservation. -/
namespace Solidity.Aggregates.Copy
open Core Static
open Contract.Interaction (Word Memory wordBytes bytesWord)

def convertScalar (type : SType) (source : Value) : Result Value :=
  match Static.convert .implicit source.type type source.value with
  | .ok value => .ok ⟨type, value⟩
  | .error .rejected => .error .rejected
  | .error .unsupported => .error (.unsupported "implicit scalar conversion")
  | .error (.panic bytes) => .error (.revert bytes)

/-- Reinterpreting a reference changes its resolved descriptor, never its
physical address. A source rvalue does not carry its former lvalue binding. -/
def retag (type : SType) (reference : Reference) : Result Value := do
  let value ← referenceValue type reference
  return ⟨type, value⟩

def alias (heap : Heap) (type : SType) (source : Value) : Result Value := do
  let some reference := source.reference | throw .rejected
  Access.validate heap ⟨source.type, reference⟩
  checkExtent heap reference 0
  retag type { reference with bindingCell := none }

def snapshotValue (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (source : Value) : Result (Contents × Nat) := do
  let place ← Defaults.asPlace source
  CopySource.snapshotForMemory registry fuel budget heap place

/-- A checked memory packet store. The packet is already a frozen source;
its exact read-after-write and frame laws appear below. -/
def writePacket (heap : Heap) (budget : Nat) (reference : Reference)
    (bytes : List UInt8) : Result (Heap × Nat) := do
  let .memory _ := reference.region | throw .rejected
  if reference.byte != 0 || reference.byteCell then throw .rejected
  checkExtent heap reference bytes.length
  let remaining ← reserve budget bytes.length
  return (MemoryOps.snapshotCopy heap reference.address.toNat bytes, remaining)

abbrev Materialize := Nat → Heap → SType → Contents → Result (Value × Heap × Nat)

def memoryCell (materialize : Materialize) (data : Reference) (type : SType)
    (state : Heap × Nat) (entry : Contents × Nat) : Result (Heap × Nat) := do
  let (heap, budget) := state
  let (contents, index) := entry
  let (value, heap, budget) ← materialize budget heap (atLocation type .memory false) contents
  let budget ← reserve budget 32
  let reference ← Access.advance data (index * 32)
  let heap ← Defaults.writeMemoryValue heap reference value
  return (heap, budget)

def memoryField (materialize : Materialize) (data : Reference)
    (state : Heap × Nat) (entry : (SType × Contents) × Nat) : Result (Heap × Nat) :=
  memoryCell materialize data entry.1.1 state (entry.1.2, entry.2)

def initializeArrayHeader (heap : Heap) (budget : Nat) (reference : Reference)
    (count : Nat) (dynamic : Bool) : Result (Reference × Heap × Nat) :=
  if dynamic then do
    let budget ← reserve budget 32
    let heap ← Defaults.writeMemoryValue heap reference ⟨.uint 31, BitVec.ofNat 256 count⟩
    return (← Access.advance reference 32, heap, budget)
  else .ok (reference, heap, budget)

def memoryArray (materialize : Materialize) (heap : Heap) (budget : Nat)
    (element : SType) (size : Option Nat) (pointer : Bool) (values : List Contents) :
    Result (Value × Heap × Nat) := do
  if size.any (· != values.length) then throw .rejected
  let bytes ← MemoryOps.arraySize values.length false size.isNone
  let (reference, heap, budget) ← MemoryOps.allocate heap budget bytes
  let (data, heap, budget) ← initializeArrayHeader heap budget reference values.length size.isNone
  let budget ← reserve budget values.length
  let (heap, budget) ← values.zipIdx.foldlM (memoryCell materialize data element) (heap, budget)
  return (⟨.array element size .memory pointer, reference⟩, heap, budget)

def memoryStruct (materialize : Materialize) (registry : Registry)
    (heap : Heap) (budget identity : Nat) (pointer : Bool) (values : List Contents) :
    Result (Value × Heap × Nat) := do
  let some fields := registry.structFields identity |
    throw (.invalidContext "missing struct members during memory copy")
  if fields.length != values.length then throw .rejected
  let size ← MemoryOps.arraySize fields.length false false
  let (reference, heap, budget) ← MemoryOps.allocate heap budget size
  let budget ← reserve budget fields.length
  let (heap, budget) ← ((fields.map Prod.snd).zip values).zipIdx.foldlM
    (memoryField materialize reference) (heap, budget)
  return (⟨.structType identity .memory pointer, reference⟩, heap, budget)

def memoryBytes (heap : Heap) (budget : Nat) (pointer string : Bool)
    (bytes : List UInt8) : Result (Value × Heap × Nat) := do
  let (value, heap, budget) ← Defaults.newBytes budget heap bytes.length string
  let place ← Defaults.asPlace value
  let data ← Access.advance place.reference 32
  let (heap, budget) ← writePacket heap budget data bytes
  let value ← retag (if string then .string .memory pointer else .bytes .memory pointer) place.reference
  return (value, heap, budget)

def memoryScalar (heap : Heap) (budget : Nat) (type : SType) (source : Value) :
    Result (Value × Heap × Nat) := do
  let value ← convertScalar type source
  return (value, heap, budget)

def buildMemory (registry : Registry) : Nat → Materialize
  | 0, _, _, _, _ => .error .exhausted
  | fuel+1, budget, heap, type, contents =>
      match type, contents with
      | .array element size .memory pointer, .array _ values =>
          memoryArray (buildMemory registry fuel) heap budget element size pointer values
      | .structType identity .memory pointer, .structure sourceIdentity values =>
          if identity != sourceIdentity then .error .rejected else
          memoryStruct (buildMemory registry fuel) registry heap budget identity pointer values
      | .bytes .memory pointer, .bytes false bytes => memoryBytes heap budget pointer false bytes
      | .string .memory pointer, .bytes true bytes => memoryBytes heap budget pointer true bytes
      | _, .scalar value => memoryScalar heap budget type value
      | _, _ => .error .rejected

/-- A fresh aggregate is allocated from raw zeroed memory and populated with
the actual snapshot; nested default objects are not allocated then discarded. -/
def materializeMemory (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (type : SType) (contents : Contents) : Result (Value × Heap × Nat) := do
  eligibleAt registry fuel (.memory heap.invocation) type
  buildMemory registry fuel budget heap type contents

def scalarWord (type : SType) (source : Value) : Result Word := do
  let value ← convertScalar type source
  if same : value.type = type then encodeStorage type (same ▸ value.value) else throw .rejected

def packedWord (type : SType) (bytes : Nat) (values : List Contents) : Result Word :=
  values.zipIdx.foldlM (fun word (contents, index) => do
    let .scalar source := contents | throw .rejected
    let encoded ← scalarWord type source
    return Packed.insert (8*bytes) (8*bytes*index) word (encoded.setWidth (8*bytes))) 0

def writePacked (heap : Heap) (budget : Nat) (data : Reference)
    (type : SType) (bytes : Nat) (values : List Contents) : Result (Heap × Nat) := do
  if bytes = 0 ∨ 32 < bytes then throw .rejected
  let perSlot := 32 / bytes
  let slots := (values.length + perSlot - 1) / perSlot
  let budget ← reserve budget slots
  let heap ← (List.range slots).foldlM (fun heap index => do
    let word ← packedWord type bytes ((values.drop (index*perSlot)).take perSlot)
    Slot.write heap data.region (data.address+BitVec.ofNat 256 index) word) heap
  return (heap, budget)

def storageElement (registry : Registry) (fuel : Nat) (place : Place)
    (element : SType) (index : Nat) : Result Place := do
  let data ← Access.arrayData place
  let (slot, byte) ← elementOffset registry fuel element index
  return ⟨atLocation element .storage false,
    rebase {data with guards := []} (data.address+BitVec.ofNat 256 slot) byte⟩

def writeStorageArray (write : Nat → Heap → Place → Contents → Result (Heap × Nat))
    (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place)
    (element : SType) (size : Option Nat) (values : List Contents) : Result (Heap × Nat) := do
  if size.any (· < values.length) then throw .rejected
  if (storageBytes element).isSome && MemoryOps.maximumMemory < values.length then throw (.panic 0x41)
  let budget ← reserve budget values.length
  let (heap, budget) ← StorageArrays.resize registry fuel budget heap place values.length
  if let some bytes := storageBytes element then
    writePacked heap budget (← Access.arrayData place) element bytes values
  else values.zipIdx.foldlM (fun (state, budget) (contents, index) => do
    let child ← storageElement registry fuel place element index
    write budget state child contents) (heap, budget)

def writeStorageStruct (write : Nat → Heap → Place → Contents → Result (Heap × Nat))
    (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place)
    (identity : Nat) (values : List Contents) : Result (Heap × Nat) := do
  let some fields := registry.structFields identity |
    throw (.invalidContext "missing struct members during storage copy")
  if fields.length != values.length then throw .rejected
  let budget ← reserve budget fields.length
  values.zipIdx.foldlM (fun (state, budget) (contents, index) => do
    let child ← Access.field registry fuel state place index
    write budget state (StorageArrays.captured child) contents) (heap, budget)

def writeContents (registry : Registry) : Nat → Nat → Heap → Place → Contents → Result (Heap × Nat)
  | 0, _, _, _, _ => .error .exhausted
  | fuel+1, budget, heap, place, contents => do
      Access.validate heap place
      let .storage _ := place.reference.region | throw .rejected
      match place.type, contents with
      | .array element size .storage _, .array _ values =>
          writeStorageArray (writeContents registry fuel) registry fuel budget heap place element size values
      | .structType identity .storage _, .structure sourceIdentity values =>
          if identity != sourceIdentity then throw .rejected
          writeStorageStruct (writeContents registry fuel) registry fuel budget heap place identity values
      | .bytes .storage _, .bytes false bytes | .string .storage _, .bytes true bytes =>
          StorageBytes.writeChecked heap budget place.reference bytes
      | _, .scalar source => do
          let value ← convertScalar place.type source
          return (← Access.write heap place value, budget)
      | _, _ => throw .rejected

def sameScalarLayout (source target : SType) : Bool :=
  source == target || match source, target with
    | .function va _ pa ra, .function vb _ pb rb => va == vb && pa == pb && ra == rb
    | _, _ => false

structure Cursor where
  heap : Heap
  slot : Word
  word : Word
  item : Nat := 0

/-- The native helper eagerly reads the next source word before the pending
destination word is stored. Keeping the cached word is essential for overlap. -/
def advanceCursor (region : Region) (bytes : Nat) (cursor : Cursor) : Result Cursor := do
  if 16 < bytes || cursor.item+1 == 32/bytes then
    let slot := cursor.slot+1
    return {cursor with slot, word := ← Slot.read cursor.heap region slot, item := 0}
  else return {cursor with item := cursor.item+1}

def consumeScalar (source target : SType) (sourceRegion : Region) (sourceBytes targetBytes : Nat)
    (state : Cursor × Word) (index : Nat) : Result (Cursor × Word) := do
  let (cursor, word) := state
  let value ← decodeStorage source
    ((Packed.extract (8*sourceBytes) (8*sourceBytes*cursor.item) cursor.word).setWidth 256)
  let encoded ← scalarWord target ⟨source, value⟩
  let word := Packed.insert (8*targetBytes) (8*targetBytes*index) word
    (encoded.setWidth (8*targetBytes))
  return (← advanceCursor sourceRegion sourceBytes cursor, word)

def transferWord (source target : SType) (sourceRegion : Region)
    (sourceBytes targetBytes items : Nat) (cursor : Cursor) : Result (Cursor × Word) :=
  if sameScalarLayout source target then do
    let word := (Packed.extract (8*items*targetBytes) 0 cursor.word).setWidth 256
    let cursor ← advanceCursor sourceRegion 32 cursor
    pure (cursor, word)
  else (List.range items).foldlM
    (consumeScalar source target sourceRegion sourceBytes targetBytes) (cursor, 0)

def storeWord (source target : SType) (sourceData targetData : Reference)
    (sourceBytes targetBytes count : Nat) (cursor : Cursor) (index : Nat) : Result Cursor := do
  let perSlot := 32/targetBytes
  let items := min perSlot (count-index*perSlot)
  let (cursor, word) ← transferWord source target sourceData.region sourceBytes targetBytes items cursor
  let heap ← Slot.write cursor.heap targetData.region
    (targetData.address+BitVec.ofNat 256 index) word
  return {cursor with heap}

def streamScalars (heap : Heap) (budget : Nat) (sourceData targetData : Reference)
    (source target : SType) (sourceBytes targetBytes count : Nat) : Result (Heap × Nat) := do
  if sourceBytes = 0 ∨ targetBytes = 0 ∨ 32 < sourceBytes ∨ 32 < targetBytes then throw .rejected
  let perSlot := 32/targetBytes
  let slots := (count+perSlot-1)/perSlot
  let budget ← reserve budget (count+slots+1)
  let cursor : Cursor := ⟨heap, sourceData.address, ← Slot.read heap sourceData.region sourceData.address, 0⟩
  let cursor ← (List.range slots).foldlM
    (storeWord source target sourceData targetData sourceBytes targetBytes count) cursor
  return (cursor.heap, budget)

abbrev ByteReader := Heap → Nat → Nat → Result Word

structure BytePreparation where
  heap : Heap
  oldLength : Nat
  remaining : Nat

def prepareBytes (heap : Heap) (budget : Nat) (target : Reference) (count : Nat) : Result BytePreparation := do
  if StorageBytes.maximumCopyLength < count then throw (.panic 0x41)
  let (_, oldCount) ← StorageBytes.loadHeader heap target
  let slots := StorageBytes.slotCount count
  let removed := StorageBytes.slotCount oldCount-slots
  let budget ← reserve budget (count+slots+removed+1)
  let heap ← (List.range removed).foldlM (fun heap index =>
    Slot.write heap target.region (StorageBytes.dataSlot target (slots+index)) 0) heap
  return ⟨heap, oldCount, budget⟩

def readShortWord (heap : Heap) (count : Nat) (read : ByteReader) : Result Word :=
  if count = 0 then .ok 0 else read heap 0 count

def finishBytes (heap : Heap) (oldCount budget : Nat) (target : Reference)
    (count : Nat) (read : ByteReader) : Result (Heap × Nat) := do
  if short : count < 32 then
    let word ← readShortWord heap count read
    let heap ← Slot.write heap target.region target.address (StorageBytes.shortFromWord word ⟨count, short⟩)
    return (heap.journalResize target.region target.address oldCount count true, budget)
  else
    let heap ← (List.range (StorageBytes.slotCount count)).foldlM (fun heap index => do
      let word ← read heap (index*32) (min 32 (count-index*32))
      Slot.write heap target.region (StorageBytes.dataSlot target index) word) heap
    let heap ← Slot.write heap target.region target.address (StorageBytes.longHeader count)
    return (heap.journalResize target.region target.address oldCount count true, budget)

/-- The reader is one of the two physical readers below, not a semantic oracle.
Destination cleanup precedes every payload read, and the header is stored last. -/
def writeBytesFrom (heap : Heap) (budget : Nat) (target : Reference)
    (count : Nat) (read : ByteReader) : Result (Heap × Nat) := do
  let prepared ← prepareBytes heap budget target count
  finishBytes prepared.heap prepared.oldLength prepared.remaining target count read

def storedByteWord (source : Reference) (count : Nat) : ByteReader := fun heap start size => do
  let slot := if count < 32 then source.address else StorageBytes.dataSlot source (start/32)
  return StorageBytes.leadingWord (← Slot.read heap source.region slot) size

def streamBytes (heap : Heap) (budget : Nat) (source target : Reference) : Result (Heap × Nat) := do
  let (_, count) ← StorageBytes.loadHeader heap source
  writeBytesFrom heap budget target count (storedByteWord source count)

/-- Copy helpers share this staging interface. It is the actual recursive
callback, not a source-value oracle. -/
abbrev StorageCopyCall := Nat → Heap → Place → Place → Result (Heap × Nat)

def storageArrayCopy (copy : StorageCopyCall) (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (source target : Place) (sourceElement targetElement : SType) : Result (Heap × Nat) := do
  let count ← Access.length heap source
  if (storageBytes targetElement).isSome && MemoryOps.maximumMemory < count then throw (.panic 0x41)
  let budget ← reserve budget count
  let (heap, budget) ← StorageArrays.resize registry fuel budget heap target count
  match storageBytes sourceElement, storageBytes targetElement with
  | some sourceBytes, some targetBytes =>
      streamScalars heap budget (← Access.arrayData source) (← Access.arrayData target)
        sourceElement targetElement sourceBytes targetBytes count
  | none, none =>
      (List.range count).foldlM (fun (state, budget) index => do
        let source ← storageElement registry fuel source sourceElement index
        let target ← storageElement registry fuel target targetElement index
        copy budget state source target) (heap, budget)
  | _, _ => throw .rejected

def storageStructCopy (copy : StorageCopyCall) (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (source target : Place) (identity targetIdentity : Nat) : Result (Heap × Nat) := do
  if identity != targetIdentity then throw .rejected
  let some fields := registry.structFields identity |
    throw (.invalidContext "missing struct definition during storage copy")
  let budget ← reserve budget fields.length
  (List.range fields.length).foldlM (fun (state, budget) index => do
    let source ← Access.field registry fuel state (StorageArrays.captured source) index
    let target ← Access.field registry fuel state (StorageArrays.captured target) index
    copy budget state (StorageArrays.captured source) (StorageArrays.captured target)) (heap, budget)

def scalarCopy (heap : Heap) (budget : Nat) (source target : Place) : Result (Heap × Nat) := do
  let value ← Access.read heap source
  let value ← convertScalar target.type value
  return (← Access.write heap target value, budget)

inductive StorageCopyShape where
  | array (source target : SType)
  | structure (source target : Nat)
  | bytes
  | scalar
  deriving DecidableEq

/-- A local dispatch summary of the existing source/target types. It carries
no declarations, locations or values independent of `SType`. -/
def storageCopyShape (source target : SType) : StorageCopyShape :=
  match source, target with
  | .array a _ .storage _, .array b _ .storage _ => .array a b
  | .structType a .storage _, .structType b .storage _ => .structure a b
  | .bytes .storage _, .bytes .storage _ | .string .storage _, .string .storage _ => .bytes
  | _, _ => .scalar

def storageCopyBody (copy : StorageCopyCall) (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (source target : Place) : Result (Heap × Nat) :=
  match storageCopyShape source.type target.type with
  | .array a b => storageArrayCopy copy registry fuel budget heap source target a b
  | .structure a b => storageStructCopy copy registry fuel budget heap source target a b
  | .bytes => streamBytes heap budget source.reference target.reference
  | .scalar => scalarCopy heap budget source target

/-- Native storage-copy order. Exact physical self assignment returns before
length decoding, resizing, scalar cleanup or allocation. Nested copies keep
positions captured by the enclosing operation rather than rechecking a length
that an earlier physical write may have changed. -/
def copyStorage (registry : Registry) : Nat → StorageCopyCall
  | 0, _, _, _, _ => .error .exhausted
  | fuel+1, budget, heap, source, target => do
      Access.validate heap source
      Access.validate heap target
      let .storage sourceOwner := source.reference.region | throw .rejected
      let .storage targetOwner := target.reference.region | throw .rejected
      if isReference source.type && sourceOwner == targetOwner &&
          source.reference.address == target.reference.address then return (heap, budget)
      storageCopyBody (copyStorage registry fuel) registry fuel budget heap source target

def sourceWord (registry : Registry) (fuel : Nat) (heap : Heap)
    (source : Place) (type : SType) (bytes start count : Nat) : Result Word := do
  let values ← (List.range count).mapM (fun index => do
    let child ← Access.index registry fuel heap source (start+index)
    return Contents.scalar (← Access.read heap child))
  packedWord type bytes values

def copyImmutableScalars (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (source target : Place) (type : SType) (bytes count : Nat) : Result (Heap × Nat) := do
  if bytes = 0 ∨ 32 < bytes then throw .rejected
  let perSlot := 32/bytes
  let slots := (count+perSlot-1)/perSlot
  let budget ← reserve budget (count+slots)
  let data ← Access.arrayData target
  let heap ← (List.range slots).foldlM (fun heap index => do
    let word ← sourceWord registry fuel heap source type bytes (index*perSlot)
      (min perSlot (count-index*perSlot))
    Slot.write heap data.region (data.address+BitVec.ofNat 256 index) word) heap
  return (heap, budget)

def sourceBytes (registry : Registry) (fuel : Nat) (heap : Heap)
    (source : Place) (start count : Nat) : Result (List UInt8) := do
  let source : Place ← match source.type with
    | .bytes location pointer | .string location pointer =>
        pure ⟨.bytes location pointer, source.reference⟩
    | _ => throw .rejected
  (List.range count).mapM (fun index => do
    let child ← Access.index registry fuel heap source (start+index)
    let value ← Access.read heap child
    match value with
    | ⟨.fixedBytes width, value⟩ =>
        if width = 0 then pure value.toNat.toUInt8 else throw .rejected
    | _ => throw .rejected)

def immutableByteWord (registry : Registry) (fuel : Nat) (source : Place) : ByteReader :=
  fun heap start count => do
    return StorageBytes.packet (← sourceBytes registry fuel heap source start count) 0

def copyImmutableBytes (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (source target : Place) : Result (Heap × Nat) := do
  let count ← Access.length heap source
  writeBytesFrom heap budget target.reference count (immutableByteWord registry fuel source)

def immutableArrayCopy (copy : StorageCopyCall) (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (source target : Place) (element : SType) : Result (Heap × Nat) := do
  let count ← Access.length heap source
  if (storageBytes element).isSome && MemoryOps.maximumMemory < count then throw (.panic 0x41)
  let budget ← reserve budget count
  let (heap, budget) ← StorageArrays.resize registry fuel budget heap target count
  if let some bytes := storageBytes element then
    copyImmutableScalars registry fuel budget heap source target element bytes count
  else (List.range count).foldlM (fun (state, budget) index => do
    let child ← Access.index registry fuel state source index
    let destination ← storageElement registry fuel target element index
    copy budget state child destination) (heap, budget)

def immutableStructCopy (copy : StorageCopyCall) (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (source target : Place) (identity targetIdentity : Nat) : Result (Heap × Nat) := do
  if identity != targetIdentity then throw .rejected
  let some fields := registry.structFields identity |
    throw (.invalidContext "missing struct definition during storage copy")
  let budget ← reserve budget fields.length
  (List.range fields.length).foldlM (fun (state, budget) index => do
    let child ← Access.field registry fuel state source index
    let destination ← Access.field registry fuel state (StorageArrays.captured target) index
    copy budget state child (StorageArrays.captured destination)) (heap, budget)

def immutableCopyShape (source target : SType) : StorageCopyShape :=
  match source, target with
  | .array _ _ _ _, .array element _ .storage _ => .array element element
  | .structType a _ _, .structType b .storage _ => .structure a b
  | .bytes _ _, .bytes .storage _ | .string _ _, .string .storage _ => .bytes
  | _, _ => .scalar

def immutableCopyBody (copy : StorageCopyCall) (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (source target : Place) : Result (Heap × Nat) :=
  match immutableCopyShape source.type target.type with
  | .array _ element => immutableArrayCopy copy registry fuel budget heap source target element
  | .structure a b => immutableStructCopy copy registry fuel budget heap source target a b
  | .bytes => copyImmutableBytes registry fuel budget heap source target
  | .scalar => scalarCopy heap budget source target

/-- Storage targets consume source members in helper order. Even immutable
memory/calldata sources are read per destination word/member, so malformed
source decoding does not overtake an earlier destination failure. -/
def copyToStorage (registry : Registry) : Nat → StorageCopyCall
  | 0, _, _, _, _ => .error .exhausted
  | fuel+1, budget, heap, source, target => do
      Access.validate heap source
      Access.validate heap target
      let .storage _ := target.reference.region | throw .rejected
      match source.reference.region with
      | .storage _ => copyStorage registry (fuel+1) budget heap source target
      | _ => immutableCopyBody (copyToStorage registry fuel) registry fuel budget heap source target

private def bindSelected (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (type : SType) (source : Value) : TransferKind → Result (Value × Heap × Nat)
  | .scalarConversion => do return (← convertScalar type source, heap, budget)
  | .storageAlias | .memoryAlias | .calldataAlias => do return (← alias heap type source, heap, budget)
  | .memoryCopy => do
      let (contents, budget) ← snapshotValue registry fuel budget heap source
      materializeMemory registry fuel budget heap type contents
  | .storageCopy => .error .rejected

/-- Binding returns the new environment value. Storage/calldata locals and
memory-to-memory assignments alias; other inputs to memory receive fresh data. -/
def bind (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (type : SType) (source : Value) : Result (Value × Heap × Nat) := do
  let kind ← planTransfer registry fuel true source.type type
  bindSelected registry fuel budget heap type source kind

def bindingReference (destination : Place) : Result Reference := do
  let .memory _ := destination.reference.region | throw .rejected
  let some address := destination.reference.bindingCell |
    throw (.invalidContext "memory reference assignment needs a captured pointer cell")
  return rebase destination.reference address

private def rebindMemory (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (destination : Place) (source : Value) (kind : TransferKind) : Result (Heap × Nat) := do
  let cell ← bindingReference destination
  let (value, heap, budget) ← bindSelected registry fuel budget heap destination.type source kind
  return (← Defaults.writeMemoryValue heap cell value, budget)

/-- Reference-valued memory lvalues update the captured pointer cell. Root
local variables use `bind`, since their bindings live in the caller's frame. -/
def assign (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (destination : Place) (source : Value) : Result (Heap × Nat) := do
  Access.validate heap destination
  let kind ← planTransfer registry fuel false source.type destination.type
  match kind with
  | .scalarConversion =>
      let value ← convertScalar destination.type source
      return (← Access.write heap destination value, budget)
  | .storageCopy =>
      copyToStorage registry fuel budget heap (← Defaults.asPlace source) destination
  | .memoryAlias | .memoryCopy =>
      rebindMemory registry fuel budget heap destination source kind
  | .storageAlias | .calldataAlias => throw .rejected

/-- The public planner equation keeps the private binding dispatcher with its
executable owner. Proof clients inspect this equation without naming it. -/
theorem bind_of_plan
    (planned : planTransfer registry fuel true source.type type = .ok kind) :
    bind registry fuel budget heap type source =
      match kind with
      | .scalarConversion => do return (← convertScalar type source, heap, budget)
      | .storageAlias | .memoryAlias | .calldataAlias => do return (← alias heap type source, heap, budget)
      | .memoryCopy => do
          let (contents, remaining) ← snapshotValue registry fuel budget heap source
          materializeMemory registry fuel remaining heap type contents
      | .storageCopy => .error .rejected := by
  simp only [bind, planned, Bind.bind, Except.bind]
  cases kind <;> rfl

/-- The assignment equation exposes the selected primitive composition while
keeping pointer rebinding's private implementation in this module. -/
theorem assign_of_plan
    (valid : Access.validate heap destination = .ok ())
    (planned : planTransfer registry fuel false source.type destination.type = .ok kind) :
    assign registry fuel budget heap destination source =
      match kind with
      | .scalarConversion => do
          let value ← convertScalar destination.type source
          return (← Access.write heap destination value, budget)
      | .storageCopy => do
          copyToStorage registry fuel budget heap (← Defaults.asPlace source) destination
      | .memoryAlias => do
          let cell ← bindingReference destination
          let (value, copied, remaining) ← (do return (← alias heap destination.type source, heap, budget))
          return (← Defaults.writeMemoryValue copied cell value, remaining)
      | .memoryCopy => do
          let cell ← bindingReference destination
          let (value, copied, remaining) ← (do
            let (contents, available) ← snapshotValue registry fuel budget heap source
            materializeMemory registry fuel available heap destination.type contents)
          return (← Defaults.writeMemoryValue copied cell value, remaining)
      | .storageAlias | .calldataAlias => throw .rejected := by
  simp only [assign, valid, planned, Bind.bind, Except.bind]
  cases kind <;> rfl

end Solidity.Aggregates.Copy
