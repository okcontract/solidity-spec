/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.EvalSteps
import Solidity.Core.Execution.Safety.CaptureProgress
import Solidity.Core.Execution.Safety.TargetProgress
import Solidity.Core.Execution.Safety.ValueProgress
import Solidity.Core.Execution.Safety.ApplyProgress
import Solidity.Core.Execution.Safety.StatementSteps
import Solidity.Core.Execution.Safety.ResumeSteps
import Solidity.Core.Execution.Safety.WritesSteps

/-! Preservation and progress for the actual machine on the independently
specified admitted/represented profile. Arbitrary eager schedules, aliases,
closed recursion and source rollback remain in the domain. Aggregate fuel and
materialization allowance are explicit; no child-execution/success premise is
part of the configuration invariant or the public step contract. -/
namespace Solidity.Execution.Safety
open Static Aggregates

private theorem statement_stepRep
    (progress : StatementProgress registry program (fuel+2) choice config) :
    StepRep registry program config (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice config) := by
  rcases progress with ⟨after,stepped,represented,budget⟩ | ⟨failure,stepped,source⟩
  · exact stepRep_next stepped represented (Machine.step_next_entry stepped) (by rw [budget];omega)
  · rw [stepped]
    exact ⟨source,rfl⟩

/-- Every represented admitted configuration either terminates with represented
values/an exact source rollback, or takes a real represented step. A one-step
allowance covers the actual materialization operation as well as traversal
fuel; it is separate from transition fuel and EVM gas. -/
theorem configuration_progress (represented : ConfigurationRep registry program config)
    (budget : materializationStepBound ≤ config.state.materializationRemaining) :
    StepRep registry program config (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice config) := by
  obtain ⟨witness⟩ := represented
  rcases config with ⟨task,stack,state,entry⟩
  have original := witness
  rcases witness with ⟨closed,objects,environment,resultEnvironment,kind,stateRep,taskRep,stackRep,checkpoint⟩
  cases taskRep with
  | eval code =>
      exact eval_progress original rfl
  | capture code =>
      exact capture_progress original rfl
  | value represented =>
      exact value_progress original rfl
  | target represented =>
      exact target_progress original rfl
  | collect packet finish =>
      exact stepRep_of_unchanged (collector_progress closed stateRep packet finish stackRep checkpoint)
  | apply packet finish => exact apply_progress ⟨closed,stateRep,stackRep,checkpoint⟩ packet finish budget
  | statement code => exact statement_stepRep (statement_progress ⟨closed,stateRep,stackRep,checkpoint⟩ code)
  | body code => exact statement_stepRep (body_progress closed stateRep stackRep checkpoint code)
  | declaration code => exact statement_stepRep (declaration_progress closed stateRep stackRep checkpoint code)
  | resume signal =>
      exact resume_progress original rfl
  | next =>
      exact resume_progress original rfl
  | loop test boolean body post =>
      apply stepRep_next (after := ⟨.eval _,.loopCondition _ _ _ :: stack,state,entry⟩)
      · rfl
      · exact ⟨⟨closed,objects,environment,environment,.value _,stateRep,.eval test,
          boolean ▸ .cons (.loopCondition test boolean body post) stackRep,checkpoint⟩⟩
      · rfl
      · dsimp;omega
  | writes pending => exact writes_progress ⟨closed,stateRep,stackRep,checkpoint⟩ pending

/-- Preservation is a consequence of the independent invariant and actual
primitive/admission proofs, rather than an assumption on successful stepping. -/
theorem configuration_preservation (represented : ConfigurationRep registry program config)
    (budget : materializationStepBound ≤ config.state.materializationRemaining)
    (stepped : Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice config = .next after) :
    ConfigurationRep registry program after ∧ after.entry = config.entry ∧
      config.state.materializationRemaining ≤ after.state.materializationRemaining+materializationStepBound := by
  have progress := configuration_progress (fuel := fuel) (choice := choice) represented budget
  rw [stepped] at progress
  exact progress

end Solidity.Execution.Safety
