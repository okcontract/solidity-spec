/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.StepLaws

/-! Actual value/control continuation leaves. Stored source permissions and
represented operands determine the next typed task; child execution or a
successful Boolean operation is never an input premise. -/
namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem boolean_datum (represented : DatumRep program heap objects datum .bool) :
    ∃ condition : Bool, datum = .atom ⟨.bool,condition⟩ := by
  obtain ⟨⟨type,value⟩,rfl,same,_⟩ := represented.atom_of_supported (.inl rfl)
  dsimp only at same
  subst type
  exact ⟨value,rfl⟩

theorem value_mode_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (represented : DatumRep program state.heap objects datum type) :
    StepRep registry program ⟨.value datum,.mode mode :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.mode mode :: stack,state,entry⟩) := by
  let afterState : MachineState Unit := {state with mode}
  have afterRep : StateRep program objects environment afterState :=
    ⟨context.stateRep.heap,context.stateRep.cells,context.stateRep.shape,context.stateRep.nonempty⟩
  apply stepRep_next (after := ⟨.value datum,stack,afterState,entry⟩)
  · rfl
  · exact (context.replace_state afterRep rfl).value represented
  · rfl
  · simp [afterState]

theorem value_discard_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (_represented : DatumRep program state.heap objects datum type) :
    StepRep registry program ⟨.value datum,.discard :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.discard :: stack,state,entry⟩) :=
  stepRep_next rfl (context.configuration (.resume .next)) rfl (by simp)

theorem value_returnValue_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (represented : DatumRep program state.heap objects datum type)
    (allowed : ReturnReady registry type flowContext.returns) :
    StepRep registry program ⟨.value datum,.returnValue :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.returnValue :: stack,state,entry⟩) :=
  stepRep_next rfl (context.configuration (.resume (.values represented allowed))) rfl (by simp)

theorem value_select_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value yes.type))
    (represented : DatumRep program state.heap objects datum .bool)
    (yesCode : ExpressionCode registry program environment yes)
    (noCode : ExpressionCode registry program environment no) (same : yes.type = no.type) :
    StepRep registry program ⟨.value datum,.select yes no :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.select yes no :: stack,state,entry⟩) := by
  obtain ⟨condition,rfl⟩ := boolean_datum represented
  cases condition with
  | false =>
      apply stepRep_next (after := ⟨.eval no,stack,state,entry⟩)
      · rfl
      · apply context.configuration
        rw [same]
        exact .eval noCode
      · rfl
      · simp
  | true => exact stepRep_next rfl (context.configuration (.eval yesCode)) rfl (by simp)

theorem value_branch_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (represented : DatumRep program state.heap objects datum .bool)
    (yesCode : StatementCode registry program environment flowContext yes)
    (noCode : StatementCode registry program environment flowContext no) :
    StepRep registry program ⟨.value datum,.branch yes no :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.branch yes no :: stack,state,entry⟩) := by
  obtain ⟨condition,rfl⟩ := boolean_datum represented
  cases condition with
  | false => exact stepRep_next rfl (context.configuration (.statement noCode)) rfl (by simp)
  | true => exact stepRep_next rfl (context.configuration (.statement yesCode)) rfl (by simp)

theorem value_lazy_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value .bool))
    (represented : DatumRep program state.heap objects datum .bool)
    (rightCode : ExpressionCode registry program environment right) (boolean : right.type = .bool) :
    StepRep registry program ⟨.value datum,.lazy terminal right :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.lazy terminal right :: stack,state,entry⟩) := by
  obtain ⟨condition,rfl⟩ := boolean_datum represented
  by_cases stopped : condition = terminal
  · apply stepRep_next (after := ⟨.value (.atom ⟨.bool,terminal⟩),stack,state,entry⟩)
    · apply step_of_transition
      simp [Machine.transition,Machine.boolean,Datum.asAtom,stopped,Machine.next]
    · exact context.value (.atom (.boolean _ _ _ _))
    · rfl
    · simp
  · apply stepRep_next (after := ⟨.eval right,stack,state,entry⟩)
    · apply step_of_transition
      simp [Machine.transition,Machine.boolean,Datum.asAtom,stopped,Machine.next]
    · apply context.configuration
      simpa only [boolean] using (TaskRep.eval rightCode)
    · rfl
    · simp

theorem value_loopCondition_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (represented : DatumRep program state.heap objects datum .bool)
    (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
    (bodyCode : StatementCode registry program environment flowContext.inLoop body)
    (postCode : StatementCode registry program environment flowContext post) :
    StepRep registry program ⟨.value datum,.loopCondition test body post :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.loopCondition test body post :: stack,state,entry⟩) := by
  obtain ⟨condition,rfl⟩ := boolean_datum represented
  cases condition with
  | false => exact stepRep_next rfl (context.configuration (.resume .next)) rfl (by simp)
  | true =>
      have bodyContext : EvaluationContext registry program objects environment state entry
          (.loopBody test body post :: stack) (.signal flowContext.inLoop) :=
        ⟨context.closed,context.stateRep,.cons (.loopBody testCode boolean bodyCode postCode)
          context.continuation,context.checkpoint⟩
      exact stepRep_next rfl (bodyContext.configuration (.statement bodyCode)) rfl (by simp)

theorem value_doCondition_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (represented : DatumRep program state.heap objects datum .bool)
    (bodyCode : StatementCode registry program environment flowContext.inLoop body)
    (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool) :
    StepRep registry program ⟨.value datum,.doCondition body test :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.doCondition body test :: stack,state,entry⟩) := by
  obtain ⟨condition,rfl⟩ := boolean_datum represented
  cases condition with
  | false => exact stepRep_next rfl (context.configuration (.resume .next)) rfl (by simp)
  | true =>
      have bodyContext : EvaluationContext registry program objects environment state entry
          (.doBody body test :: stack) (.signal flowContext.inLoop) :=
        ⟨context.closed,context.stateRep,.cons (.doBody bodyCode testCode boolean)
          context.continuation,context.checkpoint⟩
      exact stepRep_next rfl (bodyContext.configuration (.statement bodyCode)) rfl (by simp)

end Solidity.Execution.Safety
