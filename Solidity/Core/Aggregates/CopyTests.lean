/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy

namespace Solidity.Aggregates.Copy.Tests
open Core Static
open Contract.Interaction (Word wordBytes)

set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def registry : Registry := {
  enumerations := fun _ => none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun identity => identity < 4
  structFields := fun identity => match identity with
    | 0 => some [("x", .uint 0), ("values", .array (.uint 1) none .storage false)]
    | 1 => some [("values", .array (.uint 0) (some 2) .storage false), ("flag", .bool)]
    | 2 => some [("hidden", .mapping (.uint 31) (.uint 0))]
    | 3 => some [("a", .uint 31), ("b", .uint 31), ("c", .uint 31)]
    | _ => none }

private def scalar (number : Nat) (width : Width := 0) : Contents :=
  .scalar ⟨.uint width, BitVec.ofNat width.bits number⟩

private def unsigned (value : Value) : Result Nat :=
  match value with | ⟨.uint _, word⟩ => .ok word.toNat | _ => .error .rejected

private def readUnsigned (heap : Heap) (place : Place) : Result Nat := do
  unsigned (← Access.read heap place)

private def storageArray (slot : Word) (element : SType) (count : Option Nat) : Place :=
  ⟨.array element count .storage false, {region := .storage 0, address := slot}⟩

private def scalarWidening : Result Nat := do
  let (value, _, _) ← bind registry 4 0 MemoryOps.initialHeap (.uint 1) ⟨.uint 0, 255⟩
  unsigned value

example : scalarWidening = .ok 255 := by decide +kernel

private def storageToMemory : Result (Nat × Nat × Bool) := do
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 0 0x0201
  let source := storageArray 0 (.uint 0) (some 2)
  let (value, heap, _) ← bind registry 8 10000 heap
    (.array (.uint 0) (some 2) .memory true) (← Access.read heap source)
  let target ← Defaults.asPlace value
  let cell ← Access.index registry 8 heap target 0
  let heap ← Access.write heap cell ⟨.uint 0, 9⟩
  return (← readUnsigned heap (← Access.index registry 8 heap source 0),
    ← readUnsigned heap cell, target.reference.region == .memory heap.invocation)

example : storageToMemory = .ok (1, 9, true) := by decide +kernel

private def memoryAlias : Result (Bool × Nat × Bool) := do
  let type := .array (.uint 0) (some 2) .memory true
  let (source, heap, _) ← materializeMemory registry 8 10000 MemoryOps.initialHeap type
    (.array (.uint 0) [scalar 1, scalar 2])
  let before := heap.nextMemory
  let (target, heap, _) ← bind registry 8 10000 heap type source
  let source ← Defaults.asPlace source
  let target ← Defaults.asPlace target
  let heap ← Access.write heap (← Access.index registry 8 heap source 1) ⟨.uint 0, 9⟩
  return (source.reference.address == target.reference.address,
    ← readUnsigned heap (← Access.index registry 8 heap target 1), heap.nextMemory == before)

example : memoryAlias = .ok (true, 9, true) := by decide +kernel

private def storageMappingAlias : Result Nat := do
  let type := .mapping (.uint 31) (.uint 0)
  let original : Place := ⟨type, {region := .storage 0, address := 7}⟩
  let (value, heap, _) ← bind registry 8 100 MemoryOps.initialHeap type (← Access.read MemoryOps.initialHeap original)
  let binding ← Defaults.asPlace value
  let cell ← Access.mapping heap binding (.scalar ⟨.uint 31, 42⟩)
  let heap ← Access.write heap cell ⟨.uint 0, 5⟩
  readUnsigned heap (← Access.mapping heap original (.scalar ⟨.uint 31, 42⟩))

example : storageMappingAlias = .ok 5 := by decide +kernel

private def calldataAlias : Result (Nat × Nat × Option Nat) := do
  let heap := MemoryOps.initialHeap {context := {calldata := [1, 2, 3, 4]}}
  let reference ← MemoryOps.calldataView heap 1 2
  let (value, heap, _) ← bind registry 8 0 heap (.bytes .calldata true)
    ⟨.bytes .calldata true, reference⟩
  let place ← Defaults.asPlace value
  let first ← Access.read heap (← Access.index registry 8 heap place 0)
  match first with
  | ⟨.fixedBytes _, byte⟩ => return (place.reference.address.toNat, byte.toNat, place.reference.viewLength)
  | _ => throw .rejected

example : calldataAlias = .ok (1, 2, some 2) := by decide +kernel

private def memoryFieldRebinding (fromStorage : Bool) : Result (Nat × Nat × Bool) := do
  let (container, heap, _) ← materializeMemory registry 10 10000 MemoryOps.initialHeap
    (.structType 1 .memory true)
    (.structure 1 [.array (.uint 0) [scalar 1, scalar 2], .scalar ⟨.bool, false⟩])
  let container ← Defaults.asPlace container
  let field ← Access.field registry 10 heap container 0
  let oldAlias ← Access.read heap field
  let (replacement, heap) ← if fromStorage then do
      let heap ← Slot.write heap (.storage 0) 5 0x0807
      pure (← Access.read heap (storageArray 5 (.uint 0) (some 2)), heap)
    else do
      let (replacement, heap, _) ← materializeMemory registry 10 10000 heap
        (.array (.uint 0) (some 2) .memory true) (.array (.uint 0) [scalar 7, scalar 8])
      pure (replacement, heap)
  let (heap, _) ← assign registry 10 10000 heap field replacement
  let current ← Access.field registry 10 heap container 0
  let old ← Defaults.asPlace oldAlias
  return (← readUnsigned heap (← Access.index registry 10 heap old 0),
    ← readUnsigned heap (← Access.index registry 10 heap current 0),
    old.reference.address != current.reference.address)

example : memoryFieldRebinding false = .ok (1, 7, true) := by decide +kernel
example : memoryFieldRebinding true = .ok (1, 7, true) := by decide +kernel

private def calldataHeap : Heap :=
  MemoryOps.initialHeap {context := {calldata := wordBytes 2 ++ wordBytes 7 ++ wordBytes 8}}

private def calldataArray : Value :=
  ⟨.array (.uint 0) none .calldata true, {region := .calldata 0, address := 0}⟩

private def calldataCopies : Result (Nat × Nat × Nat) := do
  let (value, heap, _) ← bind registry 8 10000 calldataHeap
    (.array (.uint 0) none .memory true) calldataArray
  let memory ← Defaults.asPlace value
  let target := storageArray 10 (.uint 1) none
  let (heap, _) ← assign registry 8 10000 heap target calldataArray
  return (← readUnsigned heap (← Access.index registry 8 heap memory 0),
    ← readUnsigned heap (← Access.index registry 8 heap target 1), ← Access.length heap target)

example : calldataCopies = .ok (7, 8, 2) := by decide +kernel

private def fixedStorageCopy (dynamic : Bool) : Result (Nat × Nat × Nat) := do
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 0 0x0201
  let target := storageArray 10 (.uint 1) (if dynamic then none else some 4)
  let (heap, _) ← writeContents registry 8 10000 heap target
    (.array (.uint 1) [scalar 9 1, scalar 9 1, scalar 9 1, scalar 9 1])
  let source ← Access.read heap (storageArray 0 (.uint 0) (some 2))
  let (heap, _) ← assign registry 8 10000 heap target source
  return (← Access.length heap target, ← readUnsigned heap (← Access.index registry 8 heap target 1),
    (heap.execution.world.storage 0 (if dynamic then (Access.dataArea target.reference).address else 10)).toNat)

example : fixedStorageCopy true = .ok (2, 2, 0x00020001) := by decide +kernel
example : fixedStorageCopy false = .ok (4, 2, 0x00020001) := by decide +kernel

private def nestedStructRoundtrip : Result (Nat × Nat × Nat) := do
  let (value, heap, _) ← materializeMemory registry 12 10000 MemoryOps.initialHeap
    (.structType 0 .memory true)
    (.structure 0 [scalar 3, .array (.uint 1) [scalar 4 1, scalar 5 1]])
  let target : Place := ⟨.structType 0 .storage false, {region := .storage 0, address := 20}⟩
  let (heap, _) ← assign registry 12 10000 heap target value
  let (copy, heap, _) ← bind registry 12 10000 heap (.structType 0 .memory true)
    (← Access.read heap target)
  let copy ← Defaults.asPlace copy
  let values ← Access.field registry 12 heap copy 1
  return (← readUnsigned heap (← Access.field registry 12 heap copy 0),
    ← Access.length heap values, ← readUnsigned heap (← Access.index registry 12 heap values 1))

example : nestedStructRoundtrip = .ok (3, 2, 5) := by decide +kernel

private def streamingOverlap : Result (Nat × Nat × Nat) := do
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 0 1
  let heap ← Slot.write heap (.storage 0) 1 2
  let heap ← Slot.write heap (.storage 0) 2 3
  let target := storageArray 2 (.uint 31) (some 3)
  let source ← Access.read heap (storageArray 0 (.uint 31) (some 3))
  let (heap, _) ← assign registry 8 10000 heap target source
  return ((heap.execution.world.storage 0 2).toNat, (heap.execution.world.storage 0 3).toNat,
    (heap.execution.world.storage 0 4).toNat)

-- Eager source-word lookahead preserves the second item; the later overlap
-- changes the third item. A full source snapshot would incorrectly yield 3.
example : streamingOverlap = .ok (1, 2, 1) := by decide +kernel

private def rawPackedCopy : Result Nat := do
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 0 0x0702
  let heap ← Slot.write heap (.storage 0) 4 (BitVec.allOnes 256)
  let source ← Access.read heap (storageArray 0 .bool (some 2))
  let (heap, _) ← assign registry 8 10000 heap (storageArray 4 .bool (some 2)) source
  return (heap.execution.world.storage 0 4).toNat

example : rawPackedCopy = .ok 0x0702 := by decide +kernel

private def structOverlap : Result (Nat × Nat × Nat) := do
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 0 1
  let heap ← Slot.write heap (.storage 0) 1 2
  let heap ← Slot.write heap (.storage 0) 2 3
  let source : Value := ⟨.structType 3 .storage true, {region := .storage 0, address := 0}⟩
  let target : Place := ⟨.structType 3 .storage false, {region := .storage 0, address := 1}⟩
  let (heap, _) ← assign registry 8 10000 heap target source
  return ((heap.execution.world.storage 0 1).toNat, (heap.execution.world.storage 0 2).toNat,
    (heap.execution.world.storage 0 3).toNat)

example : structOverlap = .ok (1, 1, 1) := by decide +kernel

private def byteHeaderOverlap : Result (List UInt8) := do
  let target : Place := ⟨.bytes .storage false, {region := .storage 0, address := 0}⟩
  let sourceSlot := StorageBytes.dataSlot target.reference 1
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 0 (StorageBytes.longHeader 96)
  let heap ← Slot.write heap (.storage 0) sourceSlot (StorageBytes.encodeHeader [1, 2, 3, 4, 5])
  let source : Value := ⟨.bytes .storage true, {region := .storage 0, address := sourceSlot}⟩
  let (heap, _) ← assign registry 8 10000 heap target source
  return (← StorageBytes.read heap 100 target.reference).1

-- Destination cleanup deletes the short source header before it is loaded.
-- The source length is already cached; the copied payload therefore is zero.
example : byteHeaderOverlap = .ok [0, 0, 0, 0, 0] := by decide +kernel

private def invalidSelfAssignment : Result Nat := do
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 0 1
  let source : Value := ⟨.bytes .storage true, {region := .storage 0, address := 0}⟩
  let (heap, _) ← assign registry 8 0 heap
    ⟨.bytes .storage false, {region := .storage 0, address := 0}⟩ source
  return (heap.execution.world.storage 0 0).toNat

example : invalidSelfAssignment = .ok 1 := by decide +kernel

private def bytesRoundtrip : Result (List UInt8 × List UInt8) := do
  let bytes := List.range 33 |>.map Nat.toUInt8
  let (source, heap, _) ← materializeMemory registry 8 10000 MemoryOps.initialHeap
    (.bytes .memory true) (.bytes false bytes)
  let target : Place := ⟨.bytes .storage false, {region := .storage 0, address := 50}⟩
  let (heap, _) ← assign registry 8 10000 heap target source
  let copyTarget : Place := ⟨.bytes .storage false, {region := .storage 0, address := 51}⟩
  let (heap, _) ← assign registry 8 10000 heap copyTarget (← Access.read heap target)
  let (stored, _) ← StorageBytes.read heap 1000 copyTarget.reference
  let (copied, heap, _) ← bind registry 8 10000 heap (.bytes .memory true) (← Access.read heap copyTarget)
  let copy ← Defaults.asPlace copied
  let contents ← snapshot registry 8 1000 heap copy
  match contents.1 with
  | .bytes false values => return (stored, values)
  | _ => throw .rejected

example : bytesRoundtrip = .ok ((List.range 33).map Nat.toUInt8, (List.range 33).map Nat.toUInt8) :=
  by decide +kernel

private def failureOf (result : Result α) : Option Failure :=
  match result with | .error failure => some failure | .ok _ => none

private def oversizedStorageCopy : Result (Heap × Nat) := do
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 0 (BitVec.ofNat 256 (2^64))
  assign registry 8 0 heap (storageArray 10 (.uint 31) none)
    ⟨.array (.uint 31) none .storage true, {region := .storage 0, address := 0}⟩

example : failureOf oversizedStorageCopy = some (.panic 0x41) := by decide +kernel

private def oversizedMemoryCopy (nested : Bool) : Result (Value × Heap × Nat) := do
  let slot := if nested then 1 else 0
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) slot (BitVec.ofNat 256 (2^64))
  if nested then
    bind registry 10 100 heap (.structType 0 .memory true)
      ⟨.structType 0 .storage true, {region := .storage 0, address := 0}⟩
  else
    bind registry 8 0 heap (.array (.uint 31) none .memory true)
      ⟨.array (.uint 31) none .storage true, {region := .storage 0, address := 0}⟩

-- Native storage scalar-array encoding reads before final allocation. A host
-- traversal limit can therefore stop this path before the resource panic.
example : failureOf (oversizedMemoryCopy false) = some .exhausted := by decide +kernel
example : failureOf (oversizedMemoryCopy true) = some .exhausted := by decide +kernel

private def oversizedCalldataCopy : Result (Value × Heap × Nat) := do
  let heap := MemoryOps.initialHeap {context := {calldata := [wordBytes (BitVec.ofNat 256 (2^64))].flatten}}
  bind registry 8 0 heap (.array (.uint 31) none .memory true)
    ⟨.array (.uint 31) none .calldata true, {region := .calldata 0, address := 0}⟩

example : failureOf oversizedCalldataCopy = some (.panic 0x41) := by decide +kernel

example : failureOf (bind registry 4 100 MemoryOps.initialHeap (.uint 0) ⟨.uint 1, 256⟩) =
    some .rejected := by decide +kernel
example : failureOf (materializeMemory registry 0 100 MemoryOps.initialHeap (.uint 0) (scalar 1)) =
    some .exhausted := by decide +kernel
example : failureOf (materializeMemory registry 8 0 MemoryOps.initialHeap
    (.array (.uint 0) (some 1) .memory true) (.array (.uint 0) [scalar 1])) =
    some .exhausted := by decide +kernel
example : failureOf (bind registry 8 10000 MemoryOps.initialHeap (.structType 2 .memory true)
    ⟨.structType 2 .storage true, {region := .storage 0, address := 0}⟩) =
    some .rejected := by decide +kernel
example : failureOf (assign registry 8 10000 MemoryOps.initialHeap
    ⟨.mapping (.uint 31) (.uint 0), {region := .storage 0, address := 0}⟩
    ⟨.mapping (.uint 31) (.uint 0), {region := .storage 0, address := 1}⟩) =
    some .rejected := by decide +kernel
example : failureOf (bind registry 8 100 MemoryOps.initialHeap
    (.array (.uint 0) (some 1) .memory true)
    ⟨.array (.uint 0) (some 1) .memory true, {region := .memory 1, address := 96}⟩) =
    some (.invalidContext "foreign invocation reference") := by decide +kernel

private def lengthHeap (count : Nat) : Heap :=
  MemoryOps.initialHeap {world := {storage := fun _ slot => if slot == 0 then BitVec.ofNat 256 count else 0}}

private def lengthCopy (references : Bool) (count budget : Nat) : Result (Heap × Nat) :=
  let element : SType := if references then .array (.uint 31) (some 1) .storage false else .uint 31
  copyStorage registry 12 budget (lengthHeap count) (storageArray 0 element none) (storageArray 1 element none)

-- The value-array helper checks 2^64−1; reference arrays use resize's 2^64
-- limit. Host traversal exhaustion must not become an invented resource panic.
example : failureOf (lengthCopy false (2^64) 0) = some (.panic 0x41) := by decide +kernel
example : failureOf (lengthCopy false (2^64-1) 0) = some .exhausted := by decide +kernel
example : failureOf (lengthCopy true (2^64) 0) = some .exhausted := by decide +kernel
example : failureOf (lengthCopy true (2^64+1) (2^64+1)) = some (.panic 0x41) := by decide +kernel

private def growReferenceLength : Result Nat := do
  let element := SType.array (.uint 31) (some 1) .storage false
  let (_, heap, _) ← StorageArrays.pushZero registry 12 1 (lengthHeap (2^64-1))
    (storageArray 0 element none)
  return (← Slot.read heap (.storage 0) 0).toNat

example : growReferenceLength = .ok (2^64) := by decide +kernel

end Solidity.Aggregates.Copy.Tests
