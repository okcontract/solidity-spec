/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Pilots.OrderAliasRollbackRefinement
import Solidity.Pilots.AliasCallRollbackTests

namespace Solidity.Pilots.OrderAliasRollback
open Static Aggregates Execution Execution.Safety
open Contract.Interaction (Word wordBytes)

def boundary : Word := BitVec.ofNat 256 (2^255)

/-- The two actual source executions disagree on success versus rollback,
even with zero host-work allowance. -/
theorem boundary_executions (represented : WordArena.Represents heap AliasCallRollback.object)
    (zero : heap.execution.memory.read 160 32 = wordBytes 0)
    (writable : heap.execution.context.readOnly = false) (owner : BitVec 160) :
    source heap owner boundary false false 0 =
      .finished (.returned [.atom ⟨AliasCallRollback.word,boundary⟩] (after heap owner boundary boundary 0)) ∧
    source heap owner boundary true false 0 = .finished (.failed (.panic 0x11) (state heap 0)) := by
  constructor
  · exact source_execution represented zero writable owner boundary false false 0
  · exact source_execution represented zero writable owner boundary true false 0

/-- Wrapping addition returning zero matches neither contracted schedule. -/
theorem rejects_wrapping (heap : Heap) (owner : BitVec 160) (writeFirst : Bool)
    (world : Contract.Evm.World) (transaction : Contract.Evm.Stateful.Transaction) :
    ¬ Observes (observation heap owner boundary writeFirst false 0)
      ⟨⟨.returned,wordBytes 0,world,0⟩,transaction⟩ := by
  cases writeFirst
  · intro observed
    have bytes := observed.2.1
    change wordBytes (0 : Word) = wordBytes boundary at bytes
    have unequal : wordBytes (0 : Word) ≠ wordBytes boundary := by decide +kernel
    exact unequal bytes
  · intro observed
    have status := observed.1
    change Contract.Evm.Status.returned = .reverted at status
    cases status

/-- Matching revert bytes do not conceal a storage write that survived rollback. -/
theorem rejects_lost_rollback (heap : Heap) (owner : BitVec 160)
    (world : Contract.Evm.World) (transaction : Contract.Evm.Stateful.Transaction)
    (zero : heap.execution.world.storage (owner.setWidth 256) 0 = 0) :
    ¬ Observes (.failed (.revert []) (state heap 0))
      ⟨⟨.reverted,[],Contract.Evm.Stateful.World.store world owner
        (Contract.Evm.Stateful.write (world.storage owner) 0 1),0⟩,transaction⟩ := by
  intro observed
  have storage := observed.2.2.storage owner 0
  simp [state,AliasCallRollback.initial,Contract.Evm.Stateful.World.store,
    Contract.Evm.Stateful.write] at storage
  have different : (0 : Word) = 1 := zero.symm.trans storage
  exact (by decide : (0 : Word) ≠ 1) different

end Solidity.Pilots.OrderAliasRollback
