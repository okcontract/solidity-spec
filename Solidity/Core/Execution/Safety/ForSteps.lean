/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.ExpressionSteps
import Solidity.Core.Execution.Safety.SourceControlScopes
import Solidity.Core.Execution.Safety.SourceControlLoops

/-! Entry of an admitted for loop into its real initializer scope. Every child
permission is extracted from the actual parent checker equation, including its
normal/dead initializer join and loop-body/post contexts. -/
namespace Solidity.Execution.Safety
open Static Aggregates
open SourceTyping (bind_checked ensure_checked)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem for_optional_code
    (shape : Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment)
    (forms : ∀ expression ∈ test,Profile.Expression program expression)
    (checked : Admission.checkOptional registry fuel incoming test = .ok after)
    (boolean : test.all (fun expression => expression.type == .bool) = true) :
    ExpressionCode registry program environment (test.getD (.literal ⟨.bool,true⟩)) ∧
      (test.getD (.literal ⟨.bool,true⟩)).type = .bool ∧
      Environment.Equivalent (Profile.scopesEnvironment after.scopes) environment := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases test with
      | none =>
          have same : incoming = after := Except.ok.inj checked
          subst after
          exact ⟨⟨.literal rfl trivial,2,incoming,incoming,shape,rfl⟩,rfl,shape⟩
      | some expression =>
          have form := forms expression rfl
          have checked : Admission.checkExpression registry fuel incoming expression = .ok after := checked
          refine ⟨⟨form,fuel,incoming,after,shape,checked⟩,by simpa using boolean,?_⟩
          rw [SourceTyping.checkExpression_scopes form checked]
          exact shape

private theorem for_post_checked (form : Profile.Post program post)
    (checked : Admission.checkStatement registry fuel incoming returns loops unchecked post = .ok flow) :
    Admission.checkStatement registry fuel incoming returns otherLoops unchecked post = .ok flow := by
  cases fuel with
  | zero => cases checked
  | succ fuel => cases form <;> simpa only [Admission.checkStatement] using checked

private theorem for_declaration_checked
    (checked : Admission.checkStatement registry fuel incoming returns loops unchecked
      (.declare binders initializer : Stmt EmptyKey) = .ok flow) :
    Admission.checkStatement registry fuel incoming [] 0 false (.declare binders initializer) = .ok flow := by
  cases fuel with
  | zero => cases checked
  | succ fuel => exact checked

private theorem for_scope (environment : Environment) (nonempty : environment ≠ [])
    (initializer : Stmt EmptyKey) {flowContext : Control} :
    FrameRep registry program heap objects (initializerEnvironment (Environment.enter environment) initializer)
      (.signal flowContext) .scope environment (.signal flowContext) := by
  have suffix := SourceControl.initializerEnvironment_tail (Environment.enter environment) initializer
  change (initializerEnvironment (Environment.enter environment) initializer).tail = environment at suffix
  cases current : initializerEnvironment (Environment.enter environment) initializer with
  | nil => simp only [current,List.tail_nil] at suffix; exact False.elim (nonempty suffix.symm)
  | cons inner rest =>
      have same : rest = environment := by simpa only [current,List.tail_cons] using suffix
      subst rest
      exact .scope nonempty

theorem for_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext (.for_ initializer test post body)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
      ⟨.exec (.for_ initializer test post body),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧
      after.state.materializationRemaining = state.materializationRemaining := by
  cases code.form with
  | for_ initForm testForms postForm bodyForm =>
      obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := code.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          simp only [Admission.checkStatement] at checked
          obtain ⟨initialized,initChecked,rest⟩ := bind_checked checked
          obtain ⟨_,_,rest⟩ := bind_checked rest
          obtain ⟨current,testChecked,rest⟩ := bind_checked rest
          obtain ⟨done,booleanChecked,rest⟩ := bind_checked rest
          cases done
          obtain ⟨bodyFlow,bodyChecked,rest⟩ := bind_checked rest
          obtain ⟨_,_,rest⟩ := bind_checked rest
          obtain ⟨postFlow,postChecked,_⟩ := bind_checked rest
          let entered : MachineState Unit := {state with locals := state.locals.enter}
          let innerEnvironment := Environment.enter environment
          let initializedEnvironment := initializerEnvironment innerEnvironment initializer
          have enteredRep : StateRep program objects innerEnvironment entered := context.stateRep.enter
          have initialShape : Environment.Equivalent (Profile.scopesEnvironment incoming.enter.scopes) innerEnvironment := shape.enter
          have initializedShape := SourceControl.initializer_scopes initForm initChecked
          have fallback : Profile.scopesEnvironment initialized.dead.relax.scopes =
              initializerEnvironment (Profile.scopesEnvironment incoming.enter.scopes) initializer := initializedShape.dead
          have beforeTestShape : Environment.Equivalent
              (Profile.scopesEnvironment (initialized.normal.getD initialized.dead.relax).scopes) initializedEnvironment :=
            (Environment.Equivalent.of_eq (SourceControl.getD_environment initializedShape.normal fallback)).trans
              (initializerEnvironment_equivalent initializer initialShape)
          obtain ⟨testCode,boolean,currentShape⟩ :=
            for_optional_code beforeTestShape testForms testChecked (ensure_checked booleanChecked)
          have bodyCode : StatementCode registry program initializedEnvironment flowContext.inLoop body := by
            refine ⟨bodyForm,⟨sourceFuel,current,unchecked,bodyFlow,currentShape,?_⟩,code.returnsReady⟩
            have same := SourceControl.checkStatement_loops (registry := registry) (fuel := sourceFuel)
              (context := current) (returns := flowContext.returns) (unchecked := unchecked) (statement := body)
              (loopsA := (if flowContext.loop then 1 else 0)+1) (loopsB := 1) (by omega)
            rw [same] at bodyChecked
            exact bodyChecked
          have bodyShape := SourceControl.statement_scopes bodyForm bodyChecked
          have postShape : Environment.Equivalent
              (Profile.scopesEnvironment ((Admission.mergeNormal bodyFlow.normal
                (Admission.meetContexts bodyFlow.continues)).getD current.relax).scopes) initializedEnvironment :=
            (Environment.Equivalent.of_eq (SourceControl.getD_environment (alternative := current.relax)
              (SourceControl.mergeNormal_environment bodyShape.normal
                (SourceControl.meetContexts_environment bodyShape.continues)) rfl)).trans currentShape
          have postCode : StatementCode registry program initializedEnvironment flowContext post :=
            ⟨Profile.post_statement postForm,
              ⟨sourceFuel,_,unchecked,postFlow,postShape,for_post_checked postForm postChecked⟩,code.returnsReady⟩
          have outerScope : FrameRep registry program state.heap objects initializedEnvironment (.signal flowContext)
              .scope environment (.signal flowContext) :=
            for_scope environment context.stateRep.nonempty_environment initializer
          let after : Config Unit EmptyKey :=
            ⟨.exec initializer,.forInit (test.getD (.literal ⟨.bool,true⟩)) body post :: .scope :: stack,entered,entry⟩
          refine ⟨after,rfl,?_,rfl⟩
          cases initForm with
          | statement initForm =>
              have initCode : StatementCode registry program innerEnvironment flowContext initializer :=
                ⟨initForm,⟨sourceFuel,incoming.enter,unchecked,initialized,initialShape,initChecked⟩,code.returnsReady⟩
              have continuation : StackRep registry program state.heap objects initializedEnvironment (.signal flowContext)
                  (.forInit (test.getD (.literal ⟨.bool,true⟩)) body post :: .scope :: stack) :=
                .cons (.forInit testCode boolean bodyCode postCode) (.cons outerScope context.continuation)
              have environmentSame : initializedEnvironment = innerEnvironment := SourceControl.statement_initializer initForm _
              rw [environmentSame] at continuation
              exact ⟨⟨context.closed,objects,innerEnvironment,innerEnvironment,.signal flowContext,enteredRep,
                .statement initCode,continuation,context.checkpoint⟩⟩
          | declaration initForm =>
              obtain ⟨binder,initial,_,sourceEq,_,_⟩ := SourceControl.declaration_environment initForm initChecked
              cases sourceEq
              have initCode : DeclarationCode registry program innerEnvironment (.declare [some binder] initial) :=
                ⟨initForm,sourceFuel,incoming.enter,initialized,initialShape,for_declaration_checked initChecked⟩
              exact ⟨⟨context.closed,objects,innerEnvironment,initializedEnvironment,.nextOnly,enteredRep,
                .declaration initCode,.cons (.forInitNext testCode boolean bodyCode postCode)
                  (.cons outerScope context.continuation),context.checkpoint⟩⟩

end Solidity.Execution.Safety
