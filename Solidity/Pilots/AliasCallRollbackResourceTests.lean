/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Pilots.AliasCallRollbackResources
import Solidity.Pilots.AliasCallRollbackTests

/-! The uniform prefix premise is inhabited for every persistent world and
arbitrary source inputs. The default 4096 allowance stays a separate, smaller
allowance even though this particular allocation-free trace completes there. -/
namespace Solidity.Pilots.AliasCallRollback
open Static Aggregates Execution Execution.Safety
open Contract.Interaction (Word)

example : ¬ prefixMaterializationBound 0 ≤ 4096 := by decide +kernel

example (heap : Heap) (value : Word) (fail : Bool) :
    (entryState heap value fail).materializationRemaining = 4096 := rfl

example (heap : Heap) (owner : BitVec 160) (value : Word) (fail : Bool) :
    entryRun heap owner value fail 4096 = entryRun heap owner value fail := rfl

theorem resource_domain_nonempty (world : Contract.Interaction.World) (owner : BitVec 160)
    (value : Word) (fail : Bool) :
    ∃ heap targetWorld, heap.execution.world = world ∧ Related heap targetWorld ∧
      StateRep (entryProgram owner) [object] (Execution.Safety.Locals.environment (entryLocals heap value fail))
        (entryState heap value fail (prefixMaterializationBound 160)) ∧
      ∃ observed,
        entryRun heap owner value fail (prefixMaterializationBound 160) = .ok (.finished observed) ∧
        ObservationRep (entryProgram owner) (entryState heap value fail (prefixMaterializationBound 160)) observed := by
  obtain ⟨heap,targetWorld,sameWorld,physical,related,writable⟩ := domain_nonempty world
  refine ⟨heap,targetWorld,sameWorld,related,entry_state_rep_budget physical owner value fail _,?_⟩
  refine ⟨if fail then .failed (.revert []) (entryState heap value fail (prefixMaterializationBound 160))
    else .returned [.atom ⟨word,value⟩] (updatedEntry heap owner value fail (prefixMaterializationBound 160)),?_,?_⟩
  · exact entry_run (physical.arena.represented object (by simp)) writable owner value fail _
  · exact entry_observation_rep physical writable owner value fail _ (Nat.le_refl _)

end Solidity.Pilots.AliasCallRollback
