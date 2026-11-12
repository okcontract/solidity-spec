/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Pilots.AliasCallRollbackSafety
import Solidity.Core.Execution.Safety.FinitePrefixes

/-! The exact pilot consumes no materialization work, so its source trace holds
for every initial allowance. The generic admitted-state theorem deliberately
uses a much larger uniform allowance that also covers array allocation. This
companion applies that theorem to the actual checked pilot entry and combines
its represented result with the same budgeted source/target refinement.
The allowance remains host work; target gas and insufficient-gas rollback are
the separate observations established by the hand-authored target proof. -/
namespace Solidity.Pilots.AliasCallRollback
open Static Aggregates Execution Execution.Safety
open Contract.Interaction (Word)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
def entryChecked (heap : Heap) (owner : BitVec 160) (value : Word) (fail : Bool) (budget : Nat) :
    Checked.Expression registry {} (entryProgram owner) (entryState heap value fail budget) entryExpression :=
  ⟨⟨by rfl⟩,by rfl⟩

theorem entry_state_rep_budget (physical : HeapRep heap [object]) (owner : BitVec 160)
    (value : Word) (fail : Bool) (budget : Nat) :
    StateRep (entryProgram owner) [object] (Execution.Safety.Locals.environment (entryLocals heap value fail))
      (entryState heap value fail budget) := by
  have represented := entry_state_rep physical owner value fail
  exact ⟨represented.heap,represented.cells,represented.shape,represented.nonempty⟩

/-- Every actual checked prefix is represented for every operand schedule,
provided the conservative generic allowance covers the inspected steps. -/
theorem entry_prefix (physical : HeapRep heap [object]) (owner : BitVec 160)
    (value : Word) (fail : Bool) (budget steps : Nat) (choices : List Nat)
    (enough : prefixMaterializationBound steps ≤ budget) :
    PrefixRep registry (entryProgram owner) (entryState heap value fail budget)
      ((entryChecked heap owner value fail budget).execute physicalBackend steps choices) := by
  exact checked_expression_prefix (aggregateFuel := 126) (entryChecked heap owner value fail budget)
    (entry_closed owner) (entry_state_rep_budget physical owner value fail budget) (entry_profile owner) enough

/-- The completion equation is derived by replaying the actual ordinary entry
and helper calls. It is not a premise supplied to the generic safety proof. -/
theorem entry_checked_run (represented : WordArena.Represents heap object)
    (writable : heap.execution.context.readOnly = false) (owner : BitVec 160)
    (value : Word) (fail : Bool) (budget : Nat) :
    (entryChecked heap owner value fail budget).execute physicalBackend 160 [] =
      .finished (if fail then .failed (.revert []) (entryState heap value fail budget)
        else .returned [.atom ⟨word,value⟩] (updatedEntry heap owner value fail budget)) := by
  have completed := entry_run represented writable owner value fail budget
  have facade := Checked.expression_facade (backend := physicalBackend) (fuel := 160) (choices := [])
    (entryChecked heap owner value fail budget)
  exact Except.ok.inj (facade.symm.trans completed)

theorem entry_observation_rep (physical : HeapRep heap [object])
    (writable : heap.execution.context.readOnly = false) (owner : BitVec 160)
    (value : Word) (fail : Bool) (budget : Nat)
    (enough : prefixMaterializationBound 160 ≤ budget) :
    ObservationRep (entryProgram owner) (entryState heap value fail budget)
      (if fail then .failed (.revert []) (entryState heap value fail budget)
        else .returned [.atom ⟨word,value⟩] (updatedEntry heap owner value fail budget)) := by
  have represented := physical.arena.represented object (by simp)
  exact checked_expression_finished (aggregateFuel := 126) (entryChecked heap owner value fail budget)
    (entry_closed owner) (entry_state_rep_budget physical owner value fail budget) (entry_profile owner) enough
    (entry_checked_run represented writable owner value fail budget)

/-- One quantified result combines generic admitted-state safety, the derived
completed source trace, and the exact target artifact observations. It retains
the actual source work allowance in both success and rollback states. -/
theorem refines_represented (physical : HeapRep heap [object])
    (writable : heap.execution.context.readOnly = false) (related : Related heap world)
    (transaction : Contract.Evm.Stateful.Transaction) (context : Contract.Context) (value : Word) (fail : Bool)
    (budget : Nat) (enough : prefixMaterializationBound 160 ≤ budget) :
    ∃ observed used needed,
      entryRun heap context.self value fail budget = .ok (.finished observed) ∧
      ObservationRep (entryProgram context.self) (entryState heap value fail budget) observed ∧ used ≤ needed ∧
      (∀ gas, needed ≤ gas → Observes observed (targetObservation world transaction context heap.execution.memory value fail gas)) ∧
      (∀ gas, needed ≤ gas →
        (targetObservation world transaction context heap.execution.memory value fail gas).gasRemaining = gas-used) ∧
      (∀ gas, gas < needed → targetObservation world transaction context heap.execution.memory value fail gas =
        ⟨⟨.exceptional,[],world,0⟩,transaction⟩) := by
  have represented := physical.arena.represented object (by simp)
  obtain ⟨observed,used,needed,completed,bounded,adequate,metered,insufficient⟩ :=
    refines represented writable related transaction context value fail budget
  have facade := Checked.expression_facade (backend := physicalBackend) (fuel := 160) (choices := [])
    (entryChecked heap context.self value fail budget)
  have finished := Except.ok.inj (facade.symm.trans completed)
  have safe := checked_expression_finished (aggregateFuel := 126) (entryChecked heap context.self value fail budget)
    (entry_closed context.self) (entry_state_rep_budget physical context.self value fail budget)
    (entry_profile context.self) enough finished
  exact ⟨observed,used,needed,completed,safe,bounded,adequate,metered,insufficient⟩

end Solidity.Pilots.AliasCallRollback
