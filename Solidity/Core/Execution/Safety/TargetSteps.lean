/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.CommitSteps

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem target_read_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (target : TargetRep registry state.heap objects environment destination type) :
    StepRep registry program ⟨.target destination,.readTarget :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.target destination,.readTarget :: stack,state,entry⟩) := by
  obtain ⟨value,read,represented,typeEq⟩ := TargetWrites.readTarget_total physicalBackend context.stateRep target fuel
  apply stepRep_next (after := ⟨.value (.atom value),stack,state,entry⟩)
  · apply step_of_transition
    simp [Machine.transition,read,Machine.next]
  · exact context.value (by simpa only [typeEq] using (DatumRep.atom represented))
  · rfl
  · dsimp; omega

theorem target_assignLeft_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (target : TargetRep registry state.heap objects environment destination type)
    (right : ExpressionCode registry program environment expression)
    (ready : TransferReady registry expression.type type) :
    StepRep registry program ⟨.target destination,.assignLeft expression none :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.target destination,.assignLeft expression none :: stack,state,entry⟩) := by
  apply stepRep_next (after := ⟨.eval expression,.commitTarget destination none :: stack,state,entry⟩)
  · rfl
  · exact ⟨⟨context.closed,objects,environment,environment,.value expression.type,context.stateRep,.eval right,
      .cons (.commitTarget target ready) context.continuation,context.checkpoint⟩⟩
  · rfl
  · dsimp; omega

theorem target_compoundLeft_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (target : TargetRep registry state.heap objects environment destination type)
    (right : ExpressionCode registry program environment expression)
    (leftSupport : type.scalarSupported = true) (rightSupport : expression.type.scalarSupported = true)
    (token : Frontend.Inference.compoundToken code = true)
    (allowed : Admission.BinaryAllowed code type expression.type type) :
    StepRep registry program ⟨.target destination,.assignLeft expression (some code) :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.target destination,.assignLeft expression (some code) :: stack,state,entry⟩) := by
  apply stepRep_next (after := ⟨.eval expression,.commitTarget destination (some code) :: stack,state,entry⟩)
  · rfl
  · exact ⟨⟨context.closed,objects,environment,environment,.value expression.type,context.stateRep,.eval right,
      .cons (.compoundTarget target leftSupport rightSupport token allowed) context.continuation,context.checkpoint⟩⟩
  · rfl
  · dsimp; omega

theorem target_compoundReadFirst_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (target : TargetRep registry state.heap objects environment destination type)
    (right : ExpressionCode registry program environment expression)
    (leftSupport : type.scalarSupported = true) (rightSupport : expression.type.scalarSupported = true)
    (token : Frontend.Inference.compoundToken code = true)
    (allowed : Admission.BinaryAllowed code type expression.type type) :
    StepRep registry program ⟨.target destination,.compoundReadFirst expression code :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.target destination,.compoundReadFirst expression code :: stack,state,entry⟩) := by
  obtain ⟨old,read,represented,typeEq⟩ := TargetWrites.readTarget_total physicalBackend context.stateRep target fuel
  apply stepRep_next (after := ⟨.eval expression,.commitOld destination code old :: stack,state,entry⟩)
  · apply step_of_transition
    simp [Machine.transition,read,Machine.next]
  · exact ⟨⟨context.closed,objects,environment,environment,.value expression.type,context.stateRep,.eval right,
      .cons (.commitOld target represented typeEq leftSupport rightSupport token allowed)
        context.continuation,context.checkpoint⟩⟩
  · rfl
  · dsimp; omega

theorem target_commit_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (target : TargetRep registry state.heap objects environment destination type)
    (right : DatumRep program state.heap objects datum source)
    (ready : TransferReady registry source type) :
    StepRep registry program ⟨.target destination,.commitValue datum none :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.target destination,.commitValue datum none :: stack,state,entry⟩) := by
  apply primitive_step
  exact commit_plain_progress _ context target right ready

theorem target_compoundCommit_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (target : TargetRep registry state.heap objects environment destination type)
    (right : DatumRep program state.heap objects datum source)
    (leftSupport : type.scalarSupported = true) (rightSupport : source.scalarSupported = true)
    (token : Frontend.Inference.compoundToken code = true)
    (allowed : Admission.BinaryAllowed code type source type) :
    StepRep registry program ⟨.target destination,.commitValue datum (some code) :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.target destination,.commitValue datum (some code) :: stack,state,entry⟩) := by
  apply primitive_step
  exact commit_compound_progress _ context target target.ready right leftSupport rightSupport token allowed

end Solidity.Execution.Safety
