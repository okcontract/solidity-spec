/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.ConstructorLaws

namespace Solidity.Execution.Constructors.Tests
open Static Aggregates
open Contract.Interaction (bytesWord)

private def arrayType := SType.array (.uint 0) none .memory false
private def registry : Registry := {
  enumerations := fun _ => none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun identity => identity == 1
  structFields := fun identity => if identity == 1 then some [("first", arrayType), ("second", arrayType)] else none }

private def answer : Aggregates.Result α → Option α
  | .ok value => some value
  | .error _ => none

private def referenceAliases : Aggregates.Result (Nat × Nat × Nat × Nat) := do
  let (value, heap, budget) ← Defaults.newArray registry 32 10000 MemoryOps.initialHeap (.uint 0) 1
  let original ← Defaults.asPlace value
  let state : MachineState Unit := {external := (), heap, materializationRemaining := budget}
  let (root, types, state) ← allocateStruct registry {} state 1
  let some firstType := types[0]? | throw .rejected
  let some secondType := types[1]? | throw .rejected
  let state ← writeCell registry {} state root 0 firstType value
  let state ← writeCell registry {} state root 1 secondType value
  let first ← Access.field registry 32 state.heap root 0
  let second ← Access.field registry 32 state.heap root 1
  let cell ← Access.index registry 32 state.heap first 0
  let heap ← Access.write state.heap cell ⟨.uint 0, 9⟩
  let value ← Access.read heap (← Access.index registry 32 heap second 0)
  match value with
  | ⟨.uint _, number⟩ => return (original.reference.address.toNat, root.reference.address.toNat,
      (bytesWord (heap.execution.memory.read root.reference.address.toNat 32)).toNat, number.toNat)
  | _ => throw .rejected

/-- Both constructor fields intentionally alias the earlier array at128.
Mutating either field reaches the same element; no fresh-tree claim applies. -/
example : answer referenceAliases = some (128, 192, 128, 9) := by decide +kernel

private def earlierScalar : Aggregates.Result (Nat × Nat) := do
  let state : MachineState Unit := {external := (), heap := MemoryOps.initialHeap, materializationRemaining := 10000}
  let (root, state) ← allocateArray registry {} state (.uint 0) 2
  let state ← writeCell registry {} state root 0 (.uint 0) ⟨.uint 0, 7⟩
  let state ← writeCell registry {} state root 1 (.uint 0) ⟨.uint 0, 11⟩
  let first ← Access.read state.heap (← Access.index registry 32 state.heap root 0)
  let second ← Access.read state.heap (← Access.index registry 32 state.heap root 1)
  match first, second with
  | ⟨.uint _, a⟩, ⟨.uint _, b⟩ => return (a.toNat, b.toNat)
  | _, _ => throw .rejected

example : answer earlierScalar = some (7, 11) := by decide +kernel

private def descendingScalar : Aggregates.Result (Nat × Nat) := do
  let state : MachineState Unit := {external := (), heap := MemoryOps.initialHeap, materializationRemaining := 10000}
  let (root, state) ← allocateArray registry {} state (.uint 0) 2
  let state ← writeCell registry {} state root 1 (.uint 0) ⟨.uint 0, 11⟩
  let state ← writeCell registry {} state root 0 (.uint 0) ⟨.uint 0, 7⟩
  let first ← Access.read state.heap (← Access.index registry 32 state.heap root 0)
  let second ← Access.read state.heap (← Access.index registry 32 state.heap root 1)
  match first, second with
  | ⟨.uint _, a⟩, ⟨.uint _, b⟩ => return (a.toNat, b.toNat)
  | _, _ => throw .rejected

/-- A permitted inline-element schedule can write index1 before index0.
The symmetric packet frame retains the already written higher cell. -/
example : answer descendingScalar = some (7, 11) := by decide +kernel

example (trace : CellWriteTrace registry {} root state [(1, a), (0, b)] after)
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true) (above : 96 ≤ root.reference.address.toNat) :
    EncodedCell after.heap (root.reference.address.toNat+32) a ∧
      EncodedCell after.heap root.reference.address.toNat b := by
  have packets := trace.packets memory valid above (by simp)
  exact ⟨by simpa using packets 1 a (by simp), by simpa using packets 0 b (by simp)⟩

end Solidity.Execution.Constructors.Tests
