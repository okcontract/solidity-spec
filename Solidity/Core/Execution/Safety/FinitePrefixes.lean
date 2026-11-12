/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Progress
import Solidity.Core.Execution.Checked

/-! Adequacy of the actual finite runner for the admitted-state profile.
Transition fuel bounds the inspected prefix, aggregate fuel is at least two,
and the separate materialization allowance covers every inspected step. None
is EVM gas, a physical host-memory guarantee, or a termination assumption.
-/
namespace Solidity.Execution.Safety
open Static Aggregates

def PrefixRep (registry : Registry) (program : Program EmptyKey) (entry : MachineState Unit) :
    Execution (Config Unit EmptyKey) (Observation Unit) → Prop
  | .finished observation => ObservationRep program entry observation
  | .exhausted current _ => ConfigurationRep registry program current ∧
      current.entry = entry ∧ materializationStepBound ≤ current.state.materializationRemaining

theorem prefixMaterializationBound_zero : prefixMaterializationBound 0 = materializationStepBound := by
  simp [prefixMaterializationBound]

theorem prefixMaterializationBound_succ (steps : Nat) :
    prefixMaterializationBound (steps+1) = prefixMaterializationBound steps+materializationStepBound := by
  simp [prefixMaterializationBound,Nat.add_mul,Nat.add_assoc]
  omega

/-- Every finite prefix of the actual machine is represented or ends in a
represented source observation. The extra allowance at fuel zero covers the
runner's real terminal-step inspection before it reports host exhaustion. -/
theorem execute_prefix
    (represented : ConfigurationRep registry program initial)
    (budget : prefixMaterializationBound steps ≤ initial.state.materializationRemaining) :
    PrefixRep registry program initial.entry
      (Machine.execute physicalBackend registry ⟨aggregateFuel+2,none⟩ program steps choices initial) := by
  unfold Machine.execute
  induction steps generalizing initial choices with
  | zero =>
      have enough : materializationStepBound ≤ initial.state.materializationRemaining := by
        simpa only [prefixMaterializationBound_zero] using budget
      have safe := configuration_progress (fuel := aggregateFuel) (choice := choices.headD 0) represented enough
      cases changed : Machine.step physicalBackend registry ⟨aggregateFuel+2,none⟩ program (choices.headD 0) initial with
      | done observation =>
          rw [changed] at safe
          simpa only [Execution.run,changed,PrefixRep] using safe
      | suspended current => rw [changed] at safe; cases safe
      | next after =>
          simpa only [Execution.run,changed,PrefixRep] using (show ConfigurationRep registry program initial ∧
            initial.entry = initial.entry ∧ materializationStepBound ≤ initial.state.materializationRemaining from
              ⟨represented,rfl,enough⟩)
  | succ steps induction =>
      rw [prefixMaterializationBound_succ] at budget
      have enough : materializationStepBound ≤ initial.state.materializationRemaining := by omega
      have safe := configuration_progress (fuel := aggregateFuel) (choice := choices.headD 0) represented enough
      cases changed : Machine.step physicalBackend registry ⟨aggregateFuel+2,none⟩ program (choices.headD 0) initial with
      | done observation =>
          rw [changed] at safe
          simpa only [Execution.run,changed,PrefixRep] using safe
      | suspended current => rw [changed] at safe; cases safe
      | next after =>
          rw [changed] at safe
          obtain ⟨afterRep,sameEntry,loss⟩ := safe
          have remaining : prefixMaterializationBound steps ≤ after.state.materializationRemaining := by omega
          have tail := induction afterRep remaining (choices := choices.tail)
          rw [Execution.run,changed]
          simpa only [sameEntry] using tail

theorem checked_expression_prefix
    (checked : Checked.Expression registry ⟨aggregateFuel+2,none⟩ program state expression)
    (closed : Profile.ClosedProgram registry program)
    (represented : StateRep program objects environment state)
    (form : Profile.Expression program expression)
    (budget : prefixMaterializationBound steps ≤ state.materializationRemaining) :
    PrefixRep registry program state (checked.execute physicalBackend steps choices) := by
  exact execute_prefix (configuration_expression closed represented form checked.admitted) budget

theorem checked_statement_prefix
    (checked : Checked.Statement registry ⟨aggregateFuel+2,none⟩ program state statement)
    (closed : Profile.ClosedProgram registry program)
    (represented : StateRep program objects environment state)
    (form : Profile.Body program statement)
    (budget : prefixMaterializationBound steps ≤ state.materializationRemaining) :
    PrefixRep registry program state (checked.execute physicalBackend steps choices) := by
  exact execute_prefix (configuration_statement closed represented form checked.admitted) budget

theorem checked_expression_finished
    (checked : Checked.Expression registry ⟨aggregateFuel+2,none⟩ program state expression)
    (closed : Profile.ClosedProgram registry program)
    (represented : StateRep program objects environment state)
    (form : Profile.Expression program expression)
    (budget : prefixMaterializationBound steps ≤ state.materializationRemaining)
    (finished : checked.execute physicalBackend steps choices = .finished observation) :
    ObservationRep program state observation := by
  have safe := checked_expression_prefix checked closed represented form budget (choices := choices)
  rw [finished] at safe
  exact safe

theorem checked_statement_finished
    (checked : Checked.Statement registry ⟨aggregateFuel+2,none⟩ program state statement)
    (closed : Profile.ClosedProgram registry program)
    (represented : StateRep program objects environment state)
    (form : Profile.Body program statement)
    (budget : prefixMaterializationBound steps ≤ state.materializationRemaining)
    (finished : checked.execute physicalBackend steps choices = .finished observation) :
    ObservationRep program state observation := by
  have safe := checked_statement_prefix checked closed represented form budget (choices := choices)
  rw [finished] at safe
  exact safe

end Solidity.Execution.Safety
