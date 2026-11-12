/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.StepLaws
import Solidity.Core.Execution.Safety.ConfigurationLaws
import Solidity.Core.Execution.Safety.ReturnSteps

/-! Control continuations preserve the independent configuration invariant.
They inspect actual signal constructors, restore lexical cells/modes, and
derive their actual machine transitions. No child-execution premise occurs.
-/
namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem resume_root_progress
    (stateRep : StateRep program objects environment state)
    (signalRep : SignalRep registry program state.heap objects ⟨[],false⟩ signal) :
    StepRep registry program ⟨.resume signal,[],state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice ⟨.resume signal,[],state,entry⟩) := by
  cases signalRep with
  | next => exact ⟨objects,environment,.nil,stateRep,.nil⟩
  | return_ => exact ⟨objects,environment,.nil,stateRep,.nil⟩
  | break_ allowed => cases allowed
  | continue_ allowed => cases allowed
  | values represented _ =>
      obtain ⟨types,packet⟩ := represented.asPacket
      exact ⟨objects,environment,types,stateRep,packet⟩

theorem resume_next_root_progress (stateRep : StateRep program objects environment state) :
    StepRep registry program ⟨.resume .next,[],state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice ⟨.resume .next,[],state,entry⟩) :=
  ⟨objects,environment,.nil,stateRep,.nil⟩

theorem resume_mode_progress
    (context : EvaluationContext registry program objects environment state entry stack kind)
    (represented : TaskRep registry program state.heap objects environment (.resume signal) environment kind) :
    StepRep registry program ⟨.resume signal,.mode mode :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume signal,.mode mode :: stack,state,entry⟩) := by
  let afterState : MachineState Unit := {state with mode}
  have afterRep : StateRep program objects environment afterState :=
    ⟨context.stateRep.heap,context.stateRep.cells,context.stateRep.shape,context.stateRep.nonempty⟩
  apply stepRep_next (after := ⟨.resume signal,stack,afterState,entry⟩)
  · rfl
  · exact (context.replace_state afterRep rfl).configuration represented
  · rfl
  · simp [afterState]

theorem resume_scope_progress
    (closed : Profile.ClosedProgram registry program)
    (stateRep : StateRep program objects (inner :: outer) state) (outerNonempty : outer ≠ [])
    (represented : SignalRep registry program state.heap objects flowContext signal)
    (continuation : StackRep registry program state.heap objects outer (.signal flowContext) stack)
    (checkpoint : ∃ entryObjects entryEnvironment, StateRep program entryObjects entryEnvironment entry) :
    StepRep registry program ⟨.resume signal,.scope :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume signal,.scope :: stack,state,entry⟩) := by
  obtain ⟨locals,left,afterRep⟩ := stateRep.leave outerNonempty
  apply stepRep_next (after := ⟨.resume signal,stack,{state with locals},entry⟩)
  · apply step_of_transition
    simp [Machine.transition,left,Machine.next]
  · exact ⟨⟨closed,objects,outer,outer,.signal flowContext,afterRep,
      .resume represented,continuation,checkpoint⟩⟩
  · rfl
  · simp

theorem resume_next_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (represented : SignalRep registry program state.heap objects flowContext signal)
    (code : StatementCode registry program environment flowContext rest) :
    StepRep registry program ⟨.resume signal,.next rest :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume signal,.next rest :: stack,state,entry⟩) := by
  cases represented with
  | next =>
      exact stepRep_next rfl (context.configuration (.statement code)) rfl (by simp)
  | return_ =>
      exact stepRep_next rfl (context.configuration (.resume .return_)) rfl (by simp)
  | break_ allowed =>
      exact stepRep_next rfl (context.configuration (.resume (.break_ allowed))) rfl (by simp)
  | continue_ allowed =>
      exact stepRep_next rfl (context.configuration (.resume (.continue_ allowed))) rfl (by simp)
  | values value allowed =>
      exact stepRep_next rfl (context.configuration (.resume (.values value allowed))) rfl (by simp)

theorem resume_prefix_progress
    (closed : Profile.ClosedProgram registry program)
    (stateRep : StateRep program objects environment state)
    (code : BodyCode registry program environment flowContext rest)
    (continuation : StackRep registry program state.heap objects (prefixEnvironment environment rest)
      (.signal flowContext) stack)
    (checkpoint : ∃ entryObjects entryEnvironment, StateRep program entryObjects entryEnvironment entry) :
    StepRep registry program ⟨.resume .next,.next rest :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume .next,.next rest :: stack,state,entry⟩) := by
  apply stepRep_next (after := ⟨.exec rest,stack,state,entry⟩)
  · rfl
  · exact ⟨⟨closed,objects,environment,prefixEnvironment environment rest,.signal flowContext,
      stateRep,.body code,continuation,checkpoint⟩⟩
  · rfl
  · simp

theorem resume_forInit_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (represented : SignalRep registry program state.heap objects flowContext signal)
    (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
    (bodyCode : StatementCode registry program environment flowContext.inLoop body)
    (postCode : StatementCode registry program environment flowContext post) :
    StepRep registry program ⟨.resume signal,.forInit test body post :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume signal,.forInit test body post :: stack,state,entry⟩) := by
  cases represented with
  | next =>
      exact stepRep_next rfl (context.configuration (.loop testCode boolean bodyCode postCode)) rfl (by simp)
  | return_ =>
      exact stepRep_next rfl (context.configuration (.resume .return_)) rfl (by simp)
  | break_ allowed =>
      exact stepRep_next rfl (context.configuration (.resume (.break_ allowed))) rfl (by simp)
  | continue_ allowed =>
      exact stepRep_next rfl (context.configuration (.resume (.continue_ allowed))) rfl (by simp)
  | values value allowed =>
      exact stepRep_next rfl (context.configuration (.resume (.values value allowed))) rfl (by simp)

theorem resume_forInitNext_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
    (bodyCode : StatementCode registry program environment flowContext.inLoop body)
    (postCode : StatementCode registry program environment flowContext post) :
    StepRep registry program ⟨.resume .next,.forInit test body post :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume .next,.forInit test body post :: stack,state,entry⟩) :=
  stepRep_next rfl (context.configuration (.loop testCode boolean bodyCode postCode)) rfl (by simp)

theorem resume_loopBody_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (represented : SignalRep registry program state.heap objects flowContext.inLoop signal)
    (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
    (bodyCode : StatementCode registry program environment flowContext.inLoop body)
    (postCode : StatementCode registry program environment flowContext post) :
    StepRep registry program ⟨.resume signal,.loopBody test body post :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume signal,.loopBody test body post :: stack,state,entry⟩) := by
  have postContext : EvaluationContext registry program objects environment state entry
      (.loopPost test body post :: stack) (.signal flowContext) :=
    ⟨context.closed,context.stateRep,.cons (.loopPost testCode boolean bodyCode postCode)
      context.continuation,context.checkpoint⟩
  cases represented with
  | next => exact stepRep_next rfl (postContext.configuration (.statement postCode)) rfl (by simp)
  | continue_ _ => exact stepRep_next rfl (postContext.configuration (.statement postCode)) rfl (by simp)
  | break_ _ => exact stepRep_next rfl (context.configuration (.resume .next)) rfl (by simp)
  | return_ => exact stepRep_next rfl (context.configuration (.resume .return_)) rfl (by simp)
  | values value allowed =>
      exact stepRep_next rfl (context.configuration (.resume (.values value allowed))) rfl (by simp)

theorem resume_loopPost_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (represented : SignalRep registry program state.heap objects flowContext signal)
    (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
    (bodyCode : StatementCode registry program environment flowContext.inLoop body)
    (postCode : StatementCode registry program environment flowContext post) :
    StepRep registry program ⟨.resume signal,.loopPost test body post :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume signal,.loopPost test body post :: stack,state,entry⟩) := by
  cases represented with
  | next => exact stepRep_next rfl (context.configuration (.loop testCode boolean bodyCode postCode)) rfl (by simp)
  | return_ => exact stepRep_next rfl (context.configuration (.resume .return_)) rfl (by simp)
  | break_ allowed => exact stepRep_next rfl (context.configuration (.resume (.break_ allowed))) rfl (by simp)
  | continue_ allowed => exact stepRep_next rfl (context.configuration (.resume (.continue_ allowed))) rfl (by simp)
  | values value allowed =>
      exact stepRep_next rfl (context.configuration (.resume (.values value allowed))) rfl (by simp)

theorem resume_doBody_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (represented : SignalRep registry program state.heap objects flowContext.inLoop signal)
    (bodyCode : StatementCode registry program environment flowContext.inLoop body)
    (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool) :
    StepRep registry program ⟨.resume signal,.doBody body test :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume signal,.doBody body test :: stack,state,entry⟩) := by
  have testContext : EvaluationContext registry program objects environment state entry
      (.doCondition body test :: stack) (.value .bool) :=
    ⟨context.closed,context.stateRep,.cons (.doCondition bodyCode testCode boolean)
      context.continuation,context.checkpoint⟩
  have representedTest : ConfigurationRep registry program
      ⟨.eval test,.doCondition body test :: stack,state,entry⟩ :=
    testContext.configuration (boolean ▸ TaskRep.eval testCode)
  cases represented with
  | next => exact stepRep_next rfl representedTest rfl (by simp)
  | continue_ _ => exact stepRep_next rfl representedTest rfl (by simp)
  | break_ _ => exact stepRep_next rfl (context.configuration (.resume .next)) rfl (by simp)
  | return_ => exact stepRep_next rfl (context.configuration (.resume .return_)) rfl (by simp)
  | values value allowed =>
      exact stepRep_next rfl (context.configuration (.resume (.values value allowed))) rfl (by simp)

private theorem resume_default_call_progress
    (context : EvaluationContext registry program objects environment state entry
      (.call callerLocals mode returns :: stack) (.signal ⟨returns,false⟩))
    (default : signal = .next ∨ signal = .return_ none) :
    StepRep registry program ⟨.resume signal,.call callerLocals mode returns :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume signal,.call callerLocals mode returns :: stack,state,entry⟩) := by
  cases context.continuation with
  | cons frame continuation =>
      cases frame with
      | call caller callerShape callerNonempty returnCells _ =>
          let start : Config Unit EmptyKey := ⟨.resume signal,.call callerLocals mode returns :: stack,state,entry⟩
          obtain ⟨after,finished,represented,sameEntry,_,_,_,sameBudget⟩ :=
            finishCall_progress start context.closed context.stateRep caller callerShape callerNonempty
              returnCells continuation context.checkpoint
          apply stepRep_next (after := after)
          · apply step_of_transition
            rcases default with rfl | rfl <;> simpa only [Machine.transition] using finished
          · exact represented
          · exact sameEntry
          · change state.materializationRemaining ≤ after.state.materializationRemaining+materializationStepBound
            rw [sameBudget]
            simp [start]

theorem resume_call_progress
    (context : EvaluationContext registry program objects environment state entry
      (.call callerLocals mode returns :: stack) (.signal ⟨returns,false⟩))
    (represented : SignalRep registry program state.heap objects ⟨returns,false⟩ signal) :
    StepRep registry program ⟨.resume signal,.call callerLocals mode returns :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume signal,.call callerLocals mode returns :: stack,state,entry⟩) := by
  cases represented with
  | next => exact resume_default_call_progress context (.inl rfl)
  | return_ => exact resume_default_call_progress context (.inr rfl)
  | break_ allowed => cases allowed
  | continue_ allowed => cases allowed
  | values represented allowed => exact explicitReturn_progress context represented allowed

/-- Every represented control task is terminal or takes an actual represented
machine step. No expression-only continuation can receive a control signal:
that exclusion follows from the independently indexed stack representation. -/
theorem resume_progress (witness : ConfigurationWitness registry program config)
    (taskEq : config.task = .resume signal) :
    StepRep registry program config (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice config) := by
  rcases config with ⟨task,stack,state,entry⟩
  change task = .resume signal at taskEq
  subst task
  rcases witness with ⟨closed,objects,environment,resultEnvironment,kind,stateRep,taskRep,stackRep,checkpoint⟩
  cases taskRep with
  | resume represented =>
      cases stackRep with
      | signal => exact resume_root_progress stateRep represented
      | cons frame continuation =>
          cases frame with
          | mode =>
              exact resume_mode_progress ⟨closed,stateRep,continuation,checkpoint⟩ (.resume represented)
          | scope outerNonempty =>
              exact resume_scope_progress closed stateRep outerNonempty represented continuation checkpoint
          | next code => exact resume_next_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented code
          | forInit test boolean body post =>
              exact resume_forInit_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented test boolean body post
          | loopBody test boolean body post =>
              exact resume_loopBody_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented test boolean body post
          | loopPost test boolean body post =>
              exact resume_loopPost_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented test boolean body post
          | doBody body test boolean =>
              exact resume_doBody_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented body test boolean
          | call caller callerShape callerNonempty returnCells returnReady =>
              exact resume_call_progress
                ⟨closed,stateRep,.cons (.call caller callerShape callerNonempty returnCells returnReady) continuation,checkpoint⟩ represented
  | next =>
      cases stackRep with
      | next => exact resume_next_root_progress stateRep
      | cons frame continuation =>
          cases frame with
          | mode => exact resume_mode_progress ⟨closed,stateRep,continuation,checkpoint⟩ .next
          | «prefix» code => exact resume_prefix_progress closed stateRep code continuation checkpoint
          | forInitNext test boolean body post =>
              exact resume_forInitNext_progress ⟨closed,stateRep,continuation,checkpoint⟩ test boolean body post

end Solidity.Execution.Safety
