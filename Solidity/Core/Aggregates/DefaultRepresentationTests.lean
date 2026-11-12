/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.DefaultConstructionRepresentation
import Solidity.Core.Aggregates.DefaultTests

namespace Solidity.Aggregates.Defaults.Representation.Tests
open Static
open Contract.Interaction (wordBytes)
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

private def registry : Registry := {
  enumerations := fun _ => none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun identity => identity < 2
  structFields := fun identity => match identity with
    | 0 => some [("n", .uint 0), ("children", .array (.structType 0 .storage true) none .storage true)]
    | 1 => some [("fixed", .array (.uint 0) (some 2) .storage true),
        ("bytes", .bytes .storage true), ("child", .structType 0 .storage true)]
    | _ => none }

private def successful : Result α → Bool
  | .ok _ => true
  | .error _ => false

private def DefaultPackets (type : SType) : Result (Value × Heap × Nat) → Prop
  | .ok (value, after, _) => ∃ contents, DefaultContents registry (normalizedType type) contents ∧
      ValueRep registry after MemoryOps.initialHeap.nextMemory (normalizedType type) contents value
  | .error _ => False

private theorem default_packets (fuel budget : Nat) (type : SType)
    (succeeds : successful (defaultValue registry fuel budget MemoryOps.initialHeap type) = true) :
    DefaultPackets type (defaultValue registry fuel budget MemoryOps.initialHeap type) := by
  cases computed : defaultValue registry fuel budget MemoryOps.initialHeap type with
  | error failure => rw [computed] at succeeds; cases succeeds
  | ok result =>
      rcases result with ⟨value, after, remaining⟩
      exact defaultValue_rep (MemoryOps.initialHeap_frontier _ _) computed

/-- These instantiate the universal theorem after kernel checking constructor
success; a successful result alone does not stand in for representation. -/
example : DefaultPackets (.array (.uint 0) none .memory true)
    (defaultValue registry 4 0 MemoryOps.initialHeap (.array (.uint 0) none .memory true)) :=
  default_packets _ _ _ (by decide +kernel)

example : DefaultPackets (.structType 0 .memory true)
    (defaultValue registry 8 10000 MemoryOps.initialHeap (.structType 0 .memory true)) :=
  default_packets _ _ _ (by decide +kernel)

example : DefaultPackets (.structType 1 .memory true)
    (defaultValue registry 12 20000 MemoryOps.initialHeap (.structType 1 .memory true)) :=
  default_packets _ _ _ (by decide +kernel)

private def NewArrayPackets (element : SType) (count : Nat) : Result (Value × Heap × Nat) → Prop
  | .ok (value, after, _) => ∃ values, values.length = count ∧
      (∀ (index : Nat) contents, values[index]? = some contents →
        DefaultContents registry (atLocation element .memory false) contents) ∧
      ValueRep registry after MemoryOps.initialHeap.nextMemory
        (.array (atLocation element .memory false) none .memory true)
        (.array (atLocation element .memory false) values) value
  | .error _ => False

example : NewArrayPackets (.structType 0 .storage true) 2
    (newArray registry 10 20000 MemoryOps.initialHeap (.structType 0 .storage true) 2) := by
  have succeeds : successful (newArray registry 10 20000 MemoryOps.initialHeap (.structType 0 .storage true) 2) = true :=
    by decide +kernel
  cases computed : newArray registry 10 20000 MemoryOps.initialHeap (.structType 0 .storage true) 2 with
  | error failure => rw [computed] at succeeds; cases succeeds
  | ok result =>
      rcases result with ⟨value, after, remaining⟩
      exact newArray_rep (MemoryOps.initialHeap_frontier _ _) computed

private def dirtyZero : Heap :=
  let heap := MemoryOps.initialHeap
  { heap with execution := { heap.execution with memory := heap.execution.memory.write 96 (wordBytes 1) } }

example : successful (defaultValue registry 8 20000 dirtyZero (.structType 0 .memory true)) = false := by
  decide +kernel

example : successful (defaultValue registry 0 20000 MemoryOps.initialHeap (.structType 0 .memory true)) = false := by
  decide +kernel

end Solidity.Aggregates.Defaults.Representation.Tests
