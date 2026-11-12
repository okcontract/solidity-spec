/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.CaptureSteps
import Solidity.Core.Execution.Safety.EvalCalls
import Solidity.Core.Execution.Safety.StepLaws

namespace Solidity.Execution.Safety
open Static Aggregates
open SourceTyping (bind_checked ensure_checked)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem checked_successor (code : ExpressionCode registry program environment expression) :
    ∃ fuel incoming after, Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment ∧
      Admission.checkExpression registry (fuel+1) incoming expression = .ok after := by
  obtain ⟨fuel,incoming,after,shape,checked⟩ := code.admitted
  cases fuel with
  | zero => cases checked
  | succ fuel => exact ⟨fuel,incoming,after,shape,checked⟩

theorem eval_arithmetic_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value value.type))
    (code : ExpressionCode registry program environment (.arithmetic mode value)) :
    StepRep registry program ⟨.eval (.arithmetic mode value),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval (.arithmetic mode value),stack,state,entry⟩) := by
  cases code.form with
  | arithmetic form =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := checked_successor code
      have childCode : ExpressionCode registry program environment value :=
        ⟨form,sourceFuel,incoming,after,shape,checked⟩
      let afterState : MachineState Unit := {state with mode}
      have afterRep : StateRep program objects environment afterState :=
        ⟨context.stateRep.heap,context.stateRep.cells,context.stateRep.shape,context.stateRep.nonempty⟩
      apply stepRep_next (after := ⟨.eval value,.mode state.mode :: stack,afterState,entry⟩)
      · rfl
      · exact ⟨⟨context.closed,objects,environment,environment,.value value.type,afterRep,
          .eval childCode,.cons .mode context.continuation,context.checkpoint⟩⟩
      · rfl
      · simp [afterState]

private theorem localize_transfer (form : Profile.Target program target)
    (permission : TransferRule (Admission.localTarget target) source target.type kind) :
    TransferRule true source target.type kind := by
  cases locality : Admission.localTarget target with
  | true => simpa only [locality] using permission
  | false =>
      have scalar : target.type.scalarSupported = true := by
        cases form with
        | «local» _ => simp [Admission.localTarget] at locality
        | heap physical => simpa only [LValue.type,physical.1] using (show (SType.uint 31).scalarSupported = true from rfl)
        | index _ _ _ => rfl
      have noReference := SupportedTransfers.scalar_reference_none scalar
      cases kind <;> simp_all [TransferRule]

theorem eval_assign_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value target.type))
    (code : ExpressionCode registry program environment (.assign target right)) :
    StepRep registry program ⟨.eval (.assign target right),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval (.assign target right),stack,state,entry⟩) := by
  cases code.form with
  | assign targetForm rightForm =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := checked_successor code
      obtain ⟨rightAfter,targetAfter,kind,rightChecked,targetChecked,permission,_⟩ := SourceTyping.assign_checked checked
      obtain ⟨rightAfter,rightChecked,_⟩ := Admission.independent_checked rightChecked
      obtain ⟨targetAfter,targetChecked,_⟩ := Admission.independent_checked targetChecked
      have rightCode : ExpressionCode registry program environment right :=
        ⟨rightForm,sourceFuel,{incoming with orderIndependent := true},rightAfter,shape,rightChecked⟩
      have targetCode : TargetCode registry program environment target :=
        ⟨targetForm,sourceFuel,{incoming with orderIndependent := true},targetAfter,true,shape,targetChecked⟩
      have ready : TransferReady registry right.type target.type :=
        ⟨rightCode.transfer_source_ready targetCode.ready.1 permission,targetCode.ready,kind,
          localize_transfer targetForm permission⟩
      by_cases first : choice % 2 = 0
      · apply stepRep_next (after := ⟨.eval right,.assignRight target none :: stack,state,entry⟩)
        · apply step_of_transition; simp [Machine.transition,first,Machine.next]
        · exact ⟨⟨context.closed,objects,environment,environment,.value right.type,context.stateRep,
            .eval rightCode,.cons (.assignRight targetCode ready) context.continuation,context.checkpoint⟩⟩
        · rfl
        · simp
      · apply stepRep_next (after := ⟨.capture target,.assignLeft right none :: stack,state,entry⟩)
        · apply step_of_transition; simp [Machine.transition,first,Machine.next]
        · exact ⟨⟨context.closed,objects,environment,environment,.target target.type,context.stateRep,
            .capture targetCode,.cons (.assignLeft rightCode ready) context.continuation,context.checkpoint⟩⟩
        · rfl
        · simp

theorem eval_compound_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value target.type))
    (codeRep : ExpressionCode registry program environment (.compound code target right)) :
    StepRep registry program ⟨.eval (.compound code target right),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval (.compound code target right),stack,state,entry⟩) := by
  cases codeRep.form with
  | compound targetForm rightForm leftSupport rightSupport =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := checked_successor codeRep
      obtain ⟨token,rightAfter,targetAfter,rightChecked,targetChecked,operation,_⟩ := SourceTyping.compound_checked checked
      obtain ⟨rightAfter,rightChecked,_⟩ := Admission.independent_checked rightChecked
      obtain ⟨_,targetChecked,_⟩ := Admission.independent_checked targetChecked
      obtain ⟨targetAfter,targetChecked,_⟩ := bind_checked targetChecked
      have rightCode : ExpressionCode registry program environment right :=
        ⟨rightForm,sourceFuel,{incoming with orderIndependent := true},rightAfter,shape,rightChecked⟩
      have targetCode : TargetCode registry program environment target :=
        ⟨targetForm,sourceFuel,{incoming with orderIndependent := true},targetAfter,true,shape,targetChecked⟩
      by_cases rightFirst : choice % 3 = 0
      · apply stepRep_next (after := ⟨.eval right,.assignRight target (some code) :: stack,state,entry⟩)
        · apply step_of_transition; simp [Machine.transition,rightFirst,Machine.next]
        · exact ⟨⟨context.closed,objects,environment,environment,.value right.type,context.stateRep,
            .eval rightCode,.cons (.compoundRight targetCode leftSupport rightSupport token operation)
              context.continuation,context.checkpoint⟩⟩
        · rfl
        · simp
      · by_cases readFirst : choice % 3 = 1
        · apply stepRep_next (after := ⟨.capture target,.compoundReadFirst right code :: stack,state,entry⟩)
          · apply step_of_transition; simp [Machine.transition,readFirst,Machine.next]
          · exact ⟨⟨context.closed,objects,environment,environment,.target target.type,context.stateRep,
              .capture targetCode,.cons (.compoundReadFirst rightCode leftSupport rightSupport token operation)
                context.continuation,context.checkpoint⟩⟩
          · rfl
          · simp
        · apply stepRep_next (after := ⟨.capture target,.assignLeft right (some code) :: stack,state,entry⟩)
          · apply step_of_transition; simp [Machine.transition,rightFirst,readFirst,Machine.next]
          · exact ⟨⟨context.closed,objects,environment,environment,.target target.type,context.stateRep,
              .capture targetCode,.cons (.compoundLeft rightCode leftSupport rightSupport token operation)
                context.continuation,context.checkpoint⟩⟩
          · rfl
          · simp

theorem eval_update_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value target.type))
    (codeRep : ExpressionCode registry program environment (.update code target)) :
    StepRep registry program ⟨.eval (.update code target),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval (.update code target),stack,state,entry⟩) := by
  cases codeRep.form with
  | update targetForm _ nondelete =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := checked_successor codeRep
      obtain ⟨targetAfter,readAfter,targetChecked,_,allowed,_⟩ := SourceTyping.update_checked checked nondelete
      have targetCode : TargetCode registry program environment target :=
        ⟨targetForm,sourceFuel,incoming,targetAfter,true,shape,targetChecked⟩
      exact stepRep_next rfl
        ⟨⟨context.closed,objects,environment,environment,.target target.type,context.stateRep,
          .capture targetCode,.cons (.update nondelete allowed) context.continuation,context.checkpoint⟩⟩ rfl (by simp)

private theorem implicit_bool (allowed : Static.Implicit type .bool) : type = .bool := by
  cases type <;> simp_all [Static.Implicit]

private theorem lazy_types (allowed : Admission.BinaryAllowed code left right result)
    (lazy : code = .and ∨ code = .or) : left = .bool ∧ right = .bool ∧ result = .bool := by
  rcases lazy with rfl | rfl
  all_goals
    cases allowed with
    | asymmetric order _ => simp [BinaryCode.asymmetric] at order
    | common _ type selected operation =>
        cases operation
        rcases selected with ⟨permission,same⟩ | ⟨_,permission,same⟩
        · rw [← same] at permission
          exact ⟨same.symm,implicit_bool permission,rfl⟩
        · rw [← same] at permission
          exact ⟨implicit_bool permission,same.symm,rfl⟩

theorem eval_lazy_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value result))
    (codeRep : ExpressionCode registry program environment (.binary code result left right))
    (lazy : code = .and ∨ code = .or) :
    StepRep registry program ⟨.eval (.binary code result left right),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval (.binary code result left right),stack,state,entry⟩) := by
  cases codeRep.form with
  | binary leftForm rightForm _ _ _ =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := checked_successor codeRep
      obtain ⟨allowed,childrenAfter,children,_⟩ := SourceTyping.binary_checked checked
      obtain ⟨leftBool,rightBool,resultBool⟩ := lazy_types allowed lazy
      have enabled : (code == .and || code == .or) = true := by rcases lazy with rfl | rfl <;> decide
      simp only [enabled,↓reduceIte] at children
      obtain ⟨leftAfter,leftChecked,children⟩ := bind_checked children
      obtain ⟨rightAfter,rightChecked,_⟩ := bind_checked children
      have leftCode : ExpressionCode registry program environment left :=
        ⟨leftForm,sourceFuel,incoming,leftAfter,shape,leftChecked⟩
      have rightShape : Environment.Equivalent (Profile.scopesEnvironment leftAfter.scopes) environment := by
        rw [SourceTyping.checkExpression_scopes leftForm leftChecked]
        exact shape
      have rightCode : ExpressionCode registry program environment right :=
        ⟨rightForm,sourceFuel,leftAfter,rightAfter,rightShape,rightChecked⟩
      have continuation : StackRep registry program state.heap objects environment (.value .bool) stack :=
        resultBool ▸ context.continuation
      apply stepRep_next (after := ⟨.eval left,.lazy (code == .or) right :: stack,state,entry⟩)
      · rcases lazy with rfl | rfl <;> rfl
      · exact ⟨⟨context.closed,objects,environment,environment,.value .bool,context.stateRep,
          leftBool ▸ TaskRep.eval leftCode,.cons (.lazy rightCode rightBool) continuation,context.checkpoint⟩⟩
      · rfl
      · simp

theorem eval_assert_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (.tuple .nil)))
    (code : ExpressionCode registry program environment (.assert_ condition)) :
    StepRep registry program ⟨.eval (.assert_ condition),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval (.assert_ condition),stack,state,entry⟩) := by
  cases code.form with
  | assert_ form =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := checked_successor code
      obtain ⟨childAfter,child,checked⟩ := bind_checked checked
      obtain ⟨done,permission,_⟩ := bind_checked checked
      cases done
      have boolean : condition.type = .bool := by simpa using ensure_checked permission
      have childCode : ExpressionCode registry program environment condition :=
        ⟨form,sourceFuel,incoming,childAfter,shape,child⟩
      apply stepRep_next
      · rfl
      · apply context.gather
        · intro expression member
          cases List.mem_singleton.mp member
          exact childCode
        · simpa only [List.map_cons,List.map_nil,boolean] using (CompletionRep.assert_ (registry := registry))
      · rfl
      · simp

theorem eval_require_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (.tuple .nil)))
    (code : ExpressionCode registry program environment (.require_ .empty condition [])) :
    StepRep registry program ⟨.eval (.require_ .empty condition []),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval (.require_ .empty condition []),stack,state,entry⟩) := by
  cases code.form with
  | require_ form =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := checked_successor code
      obtain ⟨done,permission,checked⟩ := bind_checked checked
      cases done
      obtain ⟨childrenAfter,children,_⟩ := bind_checked checked
      have boolean : condition.type = .bool := by simpa using ensure_checked permission
      obtain ⟨childFuel,childAfter,child⟩ := SourceTyping.children_checked (expression := condition) children (by simp)
      have childCode : ExpressionCode registry program environment condition :=
        ⟨form,childFuel,{incoming with orderIndependent := true},childAfter,shape,child⟩
      apply stepRep_next
      · rfl
      · apply context.gather
        · intro expression member
          cases List.mem_singleton.mp member
          exact childCode
        · simpa only [List.map_cons,List.map_nil,boolean] using (CompletionRep.require_ (registry := registry))
      · rfl
      · simp

theorem eval_revert_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (.tuple .nil))) :
    StepRep registry program ⟨.eval (.revertWith .empty []),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval (.revertWith .empty []),stack,state,entry⟩) := by
  apply stepRep_next
  · rfl
  · exact context.gather (by simp) .revertWith
  · rfl
  · simp

theorem eval_code_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value expression.type))
    (code : ExpressionCode registry program environment expression) :
    StepRep registry program ⟨.eval expression,stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval expression,stack,state,entry⟩) := by
  cases code.form with
  | literal _ _ => exact stepRep_of_unchanged (literal_progress context code)
  | «local» _ => exact stepRep_of_unchanged (local_eval_progress context code)
  | read _ => exact stepRep_of_unchanged (read_progress context code)
  | arithmetic _ => exact eval_arithmetic_progress context code
  | cast _ _ _ => exact stepRep_of_unchanged (cast_progress context code)
  | unary _ _ => exact stepRep_of_unchanged (unary_progress context code)
  | @binary left right operation result _ _ _ _ _ =>
      by_cases conjunction : operation = .and
      · exact eval_lazy_progress context code (.inl conjunction)
      · by_cases disjunction : operation = .or
        · exact eval_lazy_progress context code (.inr disjunction)
        · exact stepRep_of_unchanged (binary_eager_progress context code (by simp [conjunction,disjunction]))
  | conditional _ _ _ => exact stepRep_of_unchanged (conditional_progress context code)
  | tuple _ => exact stepRep_of_unchanged (tuple_progress context code)
  | assign _ _ => exact eval_assign_progress context code
  | compound _ _ _ _ => exact eval_compound_progress context code
  | @update target updateCode _ _ nondelete =>
      cases updateCode with
      | delete => exact False.elim (nondelete rfl)
      | inc post => exact eval_update_progress context code
      | dec post => exact eval_update_progress context code
  | call _ _ _ _ => exact eval_call_progress context code
  | namedCall _ _ _ _ => exact eval_namedCall_progress context code
  | assert_ _ => exact eval_assert_progress context code
  | require_ _ => exact eval_require_progress context code
  | revertWith => exact eval_revert_progress context
  | newArray _ => exact stepRep_of_unchanged (newArray_progress context code)
  | length _ array =>
      obtain ⟨pointer,sourceType⟩ := array
      have context' : EvaluationContext registry program objects environment state entry stack (.value (.uint 31)) := by
        simpa only [Expr.type,sourceType,WordArena.arrayType] using context
      exact stepRep_of_unchanged (length_progress context' code)
  | index _ _ _ => exact stepRep_of_unchanged (index_progress context code)

/-- Expression entry itself does not materialize storage. Physical accesses,
calls and construction run through the typed tasks selected by this step. -/
theorem eval_progress (witness : ConfigurationWitness registry program config)
    (taskEq : config.task = .eval expression) :
    StepRep registry program config (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice config) := by
  rcases config with ⟨task,stack,state,entry⟩
  change task = .eval expression at taskEq
  subst task
  rcases witness with ⟨closed,objects,environment,resultEnvironment,kind,stateRep,taskRep,stackRep,checkpoint⟩
  cases taskRep with
  | eval code => exact eval_code_progress ⟨closed,stateRep,stackRep,checkpoint⟩ code

end Solidity.Execution.Safety
