/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Pilots.AliasCallRollbackSafety

/-! Independent initial-state witnesses show that the pilot's physical/safety
domain is inhabited for arbitrary persistent worlds. Negative controls retain
the fixed memory high-water and owned-array extent boundaries. -/
namespace Solidity.Pilots.AliasCallRollback
open Static Aggregates Execution Execution.Safety
open Contract.Interaction (Word Memory wordBytes)

private def preparedHeap (world : Contract.Interaction.World) : Heap := {
  execution := {
    world
    memory := Memory.write
      (Memory.write (Memory.write (fun _ => 0) 64 (wordBytes 192)) 128 (wordBytes 1)) 160 (wordBytes 0) }
  nextMemory := 192
  allocations := [⟨96,32⟩,⟨128,64⟩] }

private theorem prepared_rep (world : Contract.Interaction.World) : HeapRep (preparedHeap world) [object] := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · change MemoryOps.validAllocationContext (preparedHeap {}) = true
    decide +kernel
  · change (preparedHeap {}).execution.memory.read 96 32 = wordBytes 0
    decide +kernel
  · intro candidate member
    have same : candidate = object := by simpa using member
    subst candidate
    constructor
    · decide +kernel
    · decide +kernel
    · change (preparedHeap {}).allocated 128 64 = true
      decide +kernel
    · change (preparedHeap {}).execution.memory.read 128 32 = wordBytes 1
      decide +kernel
  · intro first firstMember second secondMember
    have firstEqual : first = object := by simpa using firstMember
    have secondEqual : second = object := by simpa using secondMember
    exact .inl (congrArg WordArena.Object.address (firstEqual.trans secondEqual.symm))
  · change (preparedHeap {}).allocated 96 32 = true
    decide +kernel

private theorem prepared_coherent (world : Contract.Interaction.World) :
    Target.MemoryCoherent (preparedHeap world).execution.memory := by
  intro address above
  simp [preparedHeap,Memory.write,Contract.Interaction.wordBytes_length,
    show ¬address < 64+32 by omega,show ¬address < 128+32 by omega,show ¬address < 160+32 by omega]

private def matchingWorld (world : Contract.Interaction.World) : Contract.Evm.World := {
  storage := fun owner slot => world.storage (owner.setWidth 256) slot,
  balances := fun owner => (world.accounts owner).balance.toNat,
  nonces := fun owner => (world.accounts owner).nonce.toNat,
  code := fun owner => (world.accounts owner).code, logs := world.logs, other := world.other }

theorem domain_nonempty (world : Contract.Interaction.World) :
    ∃ heap targetWorld, heap.execution.world = world ∧ HeapRep heap [object] ∧ Related heap targetWorld ∧
      heap.execution.context.readOnly = false := by
  refine ⟨preparedHeap world,matchingWorld world,rfl,prepared_rep world,?_,rfl⟩
  exact ⟨by intros; rfl,rfl,rfl,by intros; rfl,by intros; rfl,by intros; rfl,prepared_coherent world⟩

/-- The order-sensitive pilot's zero-payload entry relation is inhabited for
arbitrary persistent worlds, not only the empty world. -/
theorem zero_domain_nonempty (world : Contract.Interaction.World) :
    ∃ heap targetWorld, heap.execution.world = world ∧ HeapRep heap [object] ∧ Related heap targetWorld ∧
      heap.execution.context.readOnly = false ∧ heap.execution.memory.read 160 32 = wordBytes 0 := by
  refine ⟨preparedHeap world,matchingWorld world,rfl,prepared_rep world,?_,rfl,?_⟩
  · exact ⟨by intros; rfl,rfl,rfl,by intros; rfl,by intros; rfl,by intros; rfl,prepared_coherent world⟩
  · change (preparedHeap {}).execution.memory.read 160 32 = wordBytes 0
    decide +kernel

example : ¬ Target.MemoryCoherent ((preparedHeap {}).execution.memory.write 192 [1]) := by
  intro coherent
  have bad := coherent 192 (by decide)
  simp [Memory.write] at bad

example : ¬ WordArena.Represents (preparedHeap {}) ⟨128,2⟩ := by
  intro represented
  have bad := represented.extent
  change false = true at bad
  cases bad

end Solidity.Pilots.AliasCallRollback
