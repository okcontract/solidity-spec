/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Defaults

namespace Solidity.Aggregates.Defaults.Tests
open Static
open Contract.Interaction (wordBytes)

set_option maxRecDepth 16384
set_option maxHeartbeats 800000

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
    | 0 => some [("x", .uint 0), ("dynamic", .array (.uint 1) none .storage true),
        ("fixed", .array (.uint 0) (some 2) .storage true)]
    | 1 => some [("nested", .structType 0 .storage true), ("flag", .bool)]
    | 2 => some [("hidden", .mapping (.uint 31) (.uint 0))]
    | 3 => some [("cycle", .array (.structType 3 .storage true) none .storage true)]
    | _ => none }

private def unsigned (value : Value) : Result Nat :=
  match value with
  | ⟨.uint _, word⟩ => .ok word.toNat
  | _ => .error .rejected

private def defaultScalarObservation : Result Nat := do
  let (value, _, _) ← defaultValue registry 1 0 MemoryOps.initialHeap (.uint 0)
  unsigned value

example : defaultScalarObservation = .ok 0 := by decide +kernel

private def defaultDynamicObservation : Result (Nat × Nat × Nat) := do
  let (value, heap, budget) ← defaultValue registry 4 0 MemoryOps.initialHeap
    (.array (.uint 0) none .memory true)
  let place ← asPlace value
  return (place.reference.address.toNat, ← Access.length heap place, budget)

example : defaultDynamicObservation = .ok (96, 0, 0) := by decide +kernel

private def structObservation : Result (Nat × Nat × Nat × Nat) := do
  let (value, heap, _) ← defaultValue registry 8 10000 MemoryOps.initialHeap (.structType 0 .memory true)
  let place ← asPlace value
  let x ← unsigned (← Access.read heap (← Access.field registry 8 heap place 0))
  let dynamic ← Access.field registry 8 heap place 1
  let fixed ← Access.field registry 8 heap place 2
  let last ← unsigned (← Access.read heap (← Access.index registry 8 heap fixed 1))
  return (x, ← Access.length heap dynamic, ← Access.length heap fixed, last)

example : structObservation = .ok (0, 0, 2, 0) := by decide +kernel

private def nestedObservation : Result Nat := do
  let (value, heap, _) ← defaultValue registry 10 10000 MemoryOps.initialHeap (.structType 1 .memory true)
  let place ← asPlace value
  let nested ← Access.field registry 10 heap place 0
  let fixed ← Access.field registry 10 heap nested 2
  unsigned (← Access.read heap (← Access.index registry 10 heap fixed 0))

example : nestedObservation = .ok 0 := by decide +kernel

private def freshNestedObservation : Result (Bool × Nat × Nat) := do
  let (value, heap, _) ← newArray registry 8 10000 MemoryOps.initialHeap
    (.array (.uint 0) (some 2) .storage true) 2
  let root ← asPlace value
  let left ← Access.index registry 8 heap root 0
  let right ← Access.index registry 8 heap root 1
  let cell ← Access.index registry 8 heap left 0
  let heap ← Access.write heap cell ⟨.uint 0, 7⟩
  let leftValue ← unsigned (← Access.read heap cell)
  let rightValue ← unsigned (← Access.read heap (← Access.index registry 8 heap right 0))
  return (left.reference.address != right.reference.address, leftValue, rightValue)

example : freshNestedObservation = .ok (true, 7, 0) := by decide +kernel

private def byteObservation : Result (Nat × Nat) := do
  let (value, heap, _) ← newBytes 10000 MemoryOps.initialHeap 33
  let root ← asPlace value
  let last ← Access.read heap (← Access.index registry 4 heap root 32)
  match last with
  | ⟨.fixedBytes _, word⟩ => return (← Access.length heap root, word.toNat)
  | _ => throw .rejected

example : byteObservation = .ok (33, 0) := by decide +kernel

private def failureOf (result : Result (Value × Heap × Nat)) : Option Failure :=
  match result with | .error failure => some failure | .ok _ => none

example : failureOf (defaultValue registry 2 0 MemoryOps.initialHeap (.mapping (.uint 0) (.uint 0))) =
    some .rejected := by decide +kernel
example : failureOf (defaultValue registry 8 10000 MemoryOps.initialHeap (.structType 2 .memory true)) =
    some .rejected := by decide +kernel
private def guardedRecursiveDefaults : Result (Bool × Nat × Nat) := do
  let (value, heap, _) ← newArray registry 10 10000 MemoryOps.initialHeap
    (.structType 3 .storage false) 2
  let root ← asPlace value
  let left ← Access.index registry 10 heap root 0
  let right ← Access.index registry 10 heap root 1
  let children ← Access.field registry 10 heap left 0
  return (left.reference.address != right.reference.address,
    ← Access.length heap children, children.reference.address.toNat)

example : guardedRecursiveDefaults = .ok (true, 0, 96) := by decide +kernel
example : failureOf (defaultValue registry 0 10000 MemoryOps.initialHeap (.structType 3 .memory true)) =
    some .exhausted := by decide +kernel
example : failureOf (defaultValue registry 8 10000 MemoryOps.initialHeap
    (.array (.mapping (.uint 0) (.uint 0)) none .memory true)) = some .rejected := by decide +kernel
example : failureOf (newArray registry 4 0 MemoryOps.initialHeap (.uint 0) (2^64)) =
    some (.panic 0x41) := by decide +kernel
example : failureOf (newArray registry 4 0 MemoryOps.initialHeap (.uint 0) 1) =
    some .exhausted := by decide +kernel
example : failureOf (newArray registry 4 10000 MemoryOps.initialHeap (.uint 0) 0 false) =
    some .rejected := by decide +kernel
example : failureOf (defaultValue registry 4 0 MemoryOps.initialHeap (.bytes .calldata true)) =
    some .rejected := by decide +kernel

private def dirtyZeroSlot : Heap :=
  let heap := MemoryOps.initialHeap
  let memory := heap.execution.memory.write 96 (wordBytes 1)
  { heap with execution := { heap.execution with memory } }

example : failureOf (defaultValue registry 4 100 dirtyZeroSlot (.bytes .memory true)) =
    some (.invalidContext "modified memory zero slot") := by decide +kernel

private def byteCellObservation : Result Nat := do
  let (value, heap, _) ← newBytes 300 MemoryOps.initialHeap 1
  let place ← asPlace value
  let cell ← Access.index registry 4 heap place 0
  let heap ← writeMemoryValue heap cell.reference ⟨.fixedBytes 0, 0xab⟩
  return (heap.execution.memory cell.reference.address.toNat).toNat

example : byteCellObservation = .ok 0xab := by decide +kernel

end Solidity.Aggregates.Defaults.Tests
