/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.ExpressionSteps
import Solidity.Core.Execution.Safety.ResourceDemand
import Solidity.Core.Execution.Safety.EntryPreservation

namespace Solidity.Execution.Safety
open Static Aggregates

theorem stepRep_next (step : Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice before = .next after)
    (represented : ConfigurationRep registry program after) (entry : after.entry = before.entry)
    (budget : before.state.materializationRemaining ≤ after.state.materializationRemaining+materializationStepBound) :
    StepRep registry program before (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice before) := by
  rw [step]
  exact ⟨represented,entry,budget⟩

/-- State-preserving administrative steps consume no materialization work.
Checkpoint preservation follows from the actual step, not state equality. -/
theorem stepRep_of_unchanged
    (stepped : ∃ after, Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice before = .next after ∧
      ConfigurationRep registry program after ∧ after.state = before.state) :
    StepRep registry program before (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice before) := by
  obtain ⟨after,step,represented,stateEq⟩ := stepped
  exact stepRep_next step represented (Machine.step_next_entry step) (by rw [stateEq];omega)

theorem stepRep_source {failure : Failure}
    (failed : Machine.transition physicalBackend registry ⟨fuel+2,none⟩ program choice before = .error failure)
    (source : isSourceFailure failure = true) :
    StepRep registry program before (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice before) := by
  obtain ⟨step,represented⟩ := source_failure_progress failed source
  rw [step]
  exact represented

theorem EvaluationContext.value (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (represented : DatumRep program state.heap objects datum type) :
    ConfigurationRep registry program ⟨.value datum,stack,state,entry⟩ := context.configuration (.value represented)

theorem EvaluationContext.extend_heap (context : EvaluationContext registry program oldObjects environment state entry stack kind)
    (physical : HeapRep after newObjects) (invocation : after.invocation = state.heap.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) (remaining : Nat) :
    EvaluationContext registry program newObjects environment
      {state with heap := after,materializationRemaining := remaining} entry stack kind :=
  ⟨context.closed,context.stateRep.extend_heap physical invocation objects remaining,
    context.continuation.extend invocation objects,context.checkpoint⟩

theorem EvaluationContext.replace_state (context : EvaluationContext registry program objects environment state entry stack kind)
    (represented : StateRep program objects environment after) (invocation : after.heap.invocation = state.heap.invocation) :
    EvaluationContext registry program objects environment after entry stack kind :=
  ⟨context.closed,represented,context.continuation.extend invocation (fun _ member => member),context.checkpoint⟩

end Solidity.Execution.Safety
