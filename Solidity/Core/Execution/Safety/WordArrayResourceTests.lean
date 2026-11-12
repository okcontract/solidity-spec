/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.WordArrayResources

namespace Solidity.Execution.Safety.WordArrayResources.Tests
open Static Aggregates
open Contract.Interaction (Word wordBytes)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private def registry : Registry := {
  enumerations := fun _ => none,valueTypes := fun _ => none,
  contracts := fun _ => none,structures := fun _ => false }
private def failure : Aggregates.Result α → Option Failure
  | .error failure => some failure | .ok _ => none
private def summary : Aggregates.Result (Value × Heap × Nat) → Option (List Nat)
  | .error _ => none
  | .ok (value,heap,budget) => match value.reference with
      | none => none
      | some reference => match Access.length heap ⟨value.type,reference⟩ with
          | .error _ => none
          | .ok length => some [budget,heap.nextMemory,reference.address.toNat,length]

example : summary (Defaults.newArray registry 2 96 MemoryOps.initialHeap (.uint 31) 0) =
    some [0,160,128,0] := by decide +kernel
example : summary (Defaults.newArray registry 2 162 MemoryOps.initialHeap (.uint 31) 1) =
    some [0,192,128,1] := by decide +kernel
example : summary (Defaults.newArray registry 2 294 MemoryOps.initialHeap (.uint 31) 3) =
    some [0,256,128,3] := by decide +kernel
example : failure (Defaults.newArray registry 2 161 MemoryOps.initialHeap (.uint 31) 1) =
    some .exhausted := by decide +kernel
example : failure (Defaults.newArray registry 1 162 MemoryOps.initialHeap (.uint 31) 1) =
    some .exhausted := by decide +kernel
example : failure (Defaults.newArray registry 2 0 MemoryOps.initialHeap (.uint 31) (2^64)) =
    some (.panic 0x41) := by decide +kernel
example : failure (Defaults.newArray registry 2 0 MemoryOps.initialHeap (.uint 31) (2^59-5)) =
    some (.panic 0x41) := by decide +kernel
example : summary (Defaults.defaultValue registry 2 0 MemoryOps.initialHeap (WordArena.arrayType false)) =
    some [0,128,96,0] := by decide +kernel

private theorem initial_rep : HeapRep MemoryOps.initialHeap [] := by
  refine ⟨⟨MemoryOps.initialHeap_allocationContext _ _,?_,by simp,by simp⟩,by decide +kernel⟩
  have packet : wordBytes (0 : Word) = List.replicate 32 0 := by decide +kernel
  exact (MemoryOps.initialHeap_zeroSlot _ _).trans packet.symm

/-- This instantiation uses derived totality and physical representation,
without assuming the builder succeeds or supplying any step-safe callback. -/
example : ∃ after,
    Defaults.newArray registry 2 228 MemoryOps.initialHeap (.uint 31) 2 =
      .ok (⟨WordArena.arrayType true,(freshObject MemoryOps.initialHeap 2).reference after⟩,after,0) ∧
    HeapRep after [freshObject MemoryOps.initialHeap 2] ∧
    after.execution.world = MemoryOps.initialHeap.execution.world ∧ after.invocation = MemoryOps.initialHeap.invocation := by
  simpa only [cost,Nat.mul_zero,Nat.zero_add] using
    newArray_success registry 0 228 2 MemoryOps.initialHeap [] initial_rep (by decide +kernel) (by decide +kernel)

end Solidity.Execution.Safety.WordArrayResources.Tests
