/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.ExpressionSteps
import Solidity.Core.Execution.Safety.SourceControlScopes
import Solidity.Core.Execution.Safety.SourceControlLoops
import Solidity.Core.Execution.Safety.LocalSteps
import Solidity.Core.Execution.Safety.SupportedTransfers
import Solidity.Core.Execution.Safety.ForSteps

namespace Solidity.Execution.Safety
open Static Aggregates
open SourceTyping (bind_checked ensure_checked)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

/-- Statement dispatch itself consumes no materialization budget. Child
evaluation and primitive resource bounds are handled by their own steps. -/
def StatementProgress (registry : Registry) (program : Program EmptyKey) (fuel choice : Nat)
    (config : Config Unit EmptyKey) : Prop :=
  (∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice config = .next after ∧
    ConfigurationRep registry program after ∧
    after.state.materializationRemaining = config.state.materializationRemaining) ∨
  (∃ failure, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice config =
    .done (.failed failure config.entry) ∧ isSourceFailure failure = true)

private theorem expression_after (same : Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment)
    (form : Profile.Expression program expression)
    (checked : Admission.checkExpression registry fuel incoming expression = .ok after) :
    Environment.Equivalent (Profile.scopesEnvironment after.scopes) environment := by
  rw [SourceTyping.checkExpression_scopes form checked]
  exact same

private theorem flow_after (same : Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment)
    (form : Profile.Statement program statement)
    (checked : Admission.checkStatement registry fuel incoming returns loops unchecked statement = .ok flow) :
    Environment.Equivalent (Profile.scopesEnvironment (flow.normal.getD flow.dead.relax).scopes) environment := by
  have shaped := SourceControl.statement_scopes form checked
  have fallback : Profile.scopesEnvironment flow.dead.relax.scopes = Profile.scopesEnvironment incoming.scopes := shaped.dead
  exact (Environment.Equivalent.of_eq (SourceControl.getD_environment
    (alternative := flow.dead.relax) shaped.normal fallback)).trans same

private theorem scope_frame (environment : Environment) (nonempty : environment ≠ [])
    (shaped : innerEnvironment.tail = environment) {flowContext : Control} :
    FrameRep registry program heap objects innerEnvironment (.signal flowContext) .scope environment (.signal flowContext) := by
  cases innerEnvironment with
  | nil => exact False.elim (nonempty shaped.symm)
  | cons inner rest =>
      have equal : rest = environment := shaped
      subst rest
      exact .scope nonempty

private theorem arguments_ready (sources : List SType) (returns : List Binder)
    (sourceShape : ∀ type ∈ sources, Profile.OutputType type)
    (targetReady : ∀ binder ∈ returns, TypeReady registry binder.type)
    (length : sources.length = returns.length)
    (checked : (sources.zip returns).forM (fun (source,binder) =>
      Admission.transfer registry fuel true source binder.type) = .ok ()) :
    ArgumentsReady registry sources (returns.map Binder.type) := by
  induction sources generalizing returns with
  | nil =>
      have empty : returns = [] := List.eq_nil_of_length_eq_zero length.symm
      subst returns
      exact .nil
  | cons source sources induction =>
      cases returns with
      | nil => simp at length
      | cons binder returns =>
          obtain ⟨done,first,rest⟩ := bind_checked checked
          cases done
          have target := targetReady binder (by simp)
          unfold Admission.transfer at first
          obtain ⟨kind,planned,_⟩ := bind_checked first
          have permission := planTransfer_rule planned
          have formed := SupportedEligibility.planTransfer_wellFormed planned
          refine .cons ⟨⟨Profile.transfer_source_supported (sourceShape source (by simp)) target.1 permission,
            formed.1⟩,target,kind,permission⟩ ?_
          apply induction
          · intro type member; exact sourceShape type (by simp [member])
          · intro other member; exact targetReady other (by simp [member])
          · simpa using length
          · exact rest

private theorem post_checked (form : Profile.Post program post)
    (checked : Admission.checkStatement registry fuel incoming returns loops unchecked post = .ok flow) :
    Admission.checkStatement registry fuel incoming returns otherLoops unchecked post = .ok flow := by
  cases fuel with
  | zero => cases checked
  | succ fuel => cases form <;> simpa only [Admission.checkStatement] using checked

private theorem declared_fresh {incoming after : Admission.Context} {binder : Binder}
    (same : Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment)
    (checked : incoming.declare binder initialized = .ok after) :
    Environment.find environment binder.id = none := by
  unfold Admission.Context.declare at checked
  obtain ⟨done,permission,_⟩ := bind_checked checked
  cases done
  have absent : incoming.find binder.id = none := by
    have permission := ensure_checked permission
    cases found : incoming.find binder.id <;> simp_all
  rw [← same.find,context_environment_find,absent]
  rfl

theorem declaration_progress
    (closed : Profile.ClosedProgram registry program)
    (stateRep : StateRep program objects environment state)
    (continuation : StackRep registry program state.heap objects (Environment.declare environment binder) .nextOnly stack)
    (checkpoint : ∃ entryObjects entryEnvironment, StateRep program entryObjects entryEnvironment entry)
    (code : DeclarationCode registry program environment (.declare [some binder] initializer)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.declare [some binder] initializer),stack,state,entry⟩ := by
  obtain ⟨sourceFuel,incoming,flow,shape,checked⟩ := code.admitted
  cases sourceFuel with
  | zero => cases checked
  | succ sourceFuel =>
      simp only [Admission.checkStatement] at checked
      obtain ⟨after,declared,_⟩ := bind_checked checked
      cases code.form with
      | default supported =>
          obtain ⟨typeChecked,_,declared⟩ := SourceControl.default_declaration_checked declared
          have ready : TypeReady registry binder.type :=
            ⟨supported,SupportedEligibility.checkType_wellFormed typeChecked⟩
          obtain ⟨value,defaulted,represented⟩ := SupportedTransfers.defaultLocal_total program registry fuel
            state.materializationRemaining state.heap objects binder.type ready stateRep.heap
          obtain ⟨locals,written,stateAfter⟩ := local_declare_total stateRep (declared_fresh shape declared) represented rfl
          let final : MachineState Unit := {state with locals}
          left
          refine ⟨⟨.resume .next,stack,final,entry⟩,step_of_transition ?_,?_,rfl⟩
          · simp [Machine.transition,List.foldlM,Machine.declareDefault,Effects.declareLocal,defaulted,written,
              Machine.next,final]
          · exact ⟨⟨closed,objects,Environment.declare environment binder,Environment.declare environment binder,
              .nextOnly,stateAfter,.next,continuation,checkpoint⟩⟩
      | value supported form =>
          rename_i value
          obtain ⟨evaluated,source,child,components,transferred,declared⟩ :=
            SourceControl.initialized_declaration_checked declared
          have sourceCode : ExpressionCode registry program environment value :=
            ⟨form,sourceFuel,incoming,evaluated,shape,child⟩
          have evaluatedShape := expression_after shape form child
          have fresh := declared_fresh evaluatedShape declared
          unfold Admission.transfer at transferred
          obtain ⟨kind,planned,_⟩ := bind_checked transferred
          have ready : TypeReady registry binder.type :=
            ⟨supported,(SupportedEligibility.planTransfer_wellFormed planned).2⟩
          have permission := planTransfer_rule planned
          have sourceReady : TypeReady registry source :=
            ⟨Profile.transfer_source_supported (Profile.component_output value form source (by simp [components]))
              supported permission,(SupportedEligibility.planTransfer_wellFormed planned).1⟩
          have allowed : ReturnReady registry value.type [binder] := by
            change ArgumentsReady registry (Admission.resultComponents value.type) [binder.type]
            rw [components]
            exact .cons ⟨sourceReady,ready,kind,permission⟩ .nil
          left
          refine ⟨⟨.eval value,.declare [some binder] :: stack,state,entry⟩,rfl,?_,rfl⟩
          exact ⟨⟨closed,objects,environment,environment,.value value.type,stateRep,.eval sourceCode,
            .cons (.declare ready allowed fresh) continuation,checkpoint⟩⟩

private theorem checked_successor (code : StatementCode registry program environment flowContext statement) :
    ∃ fuel incoming unchecked flow,
      Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment ∧
      Admission.checkStatement registry (fuel+1) incoming flowContext.returns
        (if flowContext.loop then 1 else 0) unchecked statement = .ok flow := by
  obtain ⟨fuel,incoming,unchecked,flow,shape,checked⟩ := code.admitted
  cases fuel with
  | zero => cases checked
  | succ fuel => exact ⟨fuel,incoming,unchecked,flow,shape,checked⟩

theorem skip_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec .skip,stack,state,entry⟩ := by
  exact .inl ⟨⟨.resume .next,stack,state,entry⟩,rfl,context.configuration (.resume .next),rfl⟩

theorem expression_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext (.expr expression)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.expr expression),stack,state,entry⟩ := by
  cases code.form with
  | expr form =>
      obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := checked_successor code
      obtain ⟨after,child,_⟩ := bind_checked checked
      have childCode : ExpressionCode registry program environment expression :=
        ⟨form,sourceFuel,incoming,after,shape,child⟩
      refine .inl ⟨⟨.eval expression,.discard :: stack,state,entry⟩,rfl,?_,rfl⟩
      exact ⟨⟨context.closed,objects,environment,environment,.value expression.type,
        context.stateRep,.eval childCode,.cons .discard context.continuation,context.checkpoint⟩⟩

theorem sequence_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext (.seq first rest)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.seq first rest),stack,state,entry⟩ := by
  cases code.form with
  | seq firstForm restForm =>
      obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := checked_successor code
      obtain ⟨a,firstChecked,checked⟩ := bind_checked checked
      obtain ⟨b,restChecked,_⟩ := bind_checked checked
      have firstCode : StatementCode registry program environment flowContext first :=
        ⟨firstForm,⟨sourceFuel,incoming,unchecked,a,shape,firstChecked⟩,code.returnsReady⟩
      have restCode : StatementCode registry program environment flowContext rest :=
        ⟨restForm,⟨sourceFuel,_,unchecked,b,flow_after shape firstForm firstChecked,restChecked⟩,code.returnsReady⟩
      refine .inl ⟨⟨.exec first,.next rest :: stack,state,entry⟩,rfl,?_,rfl⟩
      exact ⟨⟨context.closed,objects,environment,environment,.signal flowContext,context.stateRep,
        .statement firstCode,.cons (.next restCode) context.continuation,context.checkpoint⟩⟩

theorem block_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext (.block body)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.block body),stack,state,entry⟩ := by
  cases code.form with
  | block form =>
      obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := checked_successor code
      obtain ⟨childFlow,child,_⟩ := bind_checked checked
      have bodyCode : BodyCode registry program (Environment.enter environment) flowContext body :=
        ⟨form,⟨sourceFuel,incoming.enter,unchecked,childFlow,shape.enter,child⟩,code.returnsReady⟩
      refine .inl ⟨⟨.exec body,.scope :: stack,{state with locals := state.locals.enter},entry⟩,rfl,?_,rfl⟩
      exact ⟨⟨context.closed,objects,Environment.enter environment,prefixEnvironment (Environment.enter environment) body,
        .signal flowContext,context.stateRep.enter,.body bodyCode,
        .cons (scope_frame environment context.stateRep.nonempty_environment
          (SourceControl.prefixEnvironment_tail (Environment.enter environment) body)) context.continuation,context.checkpoint⟩⟩

theorem branch_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext (.if_ test yes no)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.if_ test yes no),stack,state,entry⟩ := by
  cases code.form with
  | if_ testForm yesForm noForm =>
      obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := checked_successor code
      obtain ⟨afterTest,testChecked,checked⟩ := bind_checked checked
      obtain ⟨done,permission,checked⟩ := bind_checked checked
      cases done
      obtain ⟨a,yesChecked,checked⟩ := bind_checked checked
      obtain ⟨b,noChecked,_⟩ := bind_checked checked
      have boolean : test.type = .bool := by simpa using ensure_checked permission
      have afterShape := expression_after shape testForm testChecked
      have testCode : ExpressionCode registry program environment test :=
        ⟨testForm,sourceFuel,incoming,afterTest,shape,testChecked⟩
      have yesCode : StatementCode registry program environment flowContext yes :=
        ⟨yesForm,⟨sourceFuel,afterTest,unchecked,a,afterShape,yesChecked⟩,code.returnsReady⟩
      have noCode : StatementCode registry program environment flowContext no :=
        ⟨noForm,⟨sourceFuel,afterTest,unchecked,b,afterShape,noChecked⟩,code.returnsReady⟩
      refine .inl ⟨⟨.eval test,.branch yes no :: stack,state,entry⟩,rfl,?_,rfl⟩
      exact ⟨⟨context.closed,objects,environment,environment,.value .bool,context.stateRep,
        boolean ▸ TaskRep.eval testCode,.cons (.branch yesCode noCode) context.continuation,context.checkpoint⟩⟩

theorem break_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext .break_) :
    StatementProgress registry program (fuel+2) choice ⟨.exec .break_,stack,state,entry⟩ := by
  obtain ⟨_,_,_,_,_,checked⟩ := checked_successor code
  obtain ⟨done,permission,_⟩ := bind_checked checked
  cases done
  have allowed : flowContext.loop = true := by
    have permission := ensure_checked permission
    cases loop : flowContext.loop <;> simp_all
  exact .inl ⟨⟨.resume .break_,stack,state,entry⟩,rfl,context.configuration (.resume (.break_ allowed)),rfl⟩

theorem continue_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext .continue_) :
    StatementProgress registry program (fuel+2) choice ⟨.exec .continue_,stack,state,entry⟩ := by
  obtain ⟨_,_,_,_,_,checked⟩ := checked_successor code
  obtain ⟨done,permission,_⟩ := bind_checked checked
  cases done
  have allowed : flowContext.loop = true := by
    have permission := ensure_checked permission
    cases loop : flowContext.loop <;> simp_all
  exact .inl ⟨⟨.resume .continue_,stack,state,entry⟩,rfl,context.configuration (.resume (.continue_ allowed)),rfl⟩

theorem return_none_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.return_ none),stack,state,entry⟩ :=
  .inl ⟨⟨.resume (.return_ none),stack,state,entry⟩,rfl,context.configuration (.resume .return_),rfl⟩

theorem return_value_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext (.return_ (some value))) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.return_ (some value)),stack,state,entry⟩ := by
  cases code.form with
  | return_ forms =>
      have form := forms value (by simp)
      obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := checked_successor code
      obtain ⟨after,child,checked⟩ := bind_checked checked
      obtain ⟨done,count,checked⟩ := bind_checked checked
      cases done
      obtain ⟨done,transfers,_⟩ := bind_checked checked
      cases done
      have allowed : ReturnReady registry value.type flowContext.returns :=
        arguments_ready _ _ (Profile.component_output value form) code.returnsReady
          (by simpa using ensure_checked count) transfers
      have childCode : ExpressionCode registry program environment value :=
        ⟨form,sourceFuel,incoming,after,shape,child⟩
      refine .inl ⟨⟨.eval value,.returnValue :: stack,state,entry⟩,rfl,?_,rfl⟩
      exact ⟨⟨context.closed,objects,environment,environment,.value value.type,context.stateRep,
        .eval childCode,.cons (.returnValue allowed) context.continuation,context.checkpoint⟩⟩

theorem arithmetic_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext (.arithmetic mode body)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.arithmetic mode body),stack,state,entry⟩ := by
  cases code.form with
  | arithmetic form =>
      obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := checked_successor code
      obtain ⟨done,_,child⟩ := bind_checked checked
      cases done
      have bodyCode : StatementCode registry program environment flowContext body :=
        ⟨form,⟨sourceFuel,incoming,mode == .unchecked,flow,shape,child⟩,code.returnsReady⟩
      refine .inl ⟨⟨.exec body,.mode state.mode :: stack,{state with mode},entry⟩,rfl,?_,rfl⟩
      exact ⟨⟨context.closed,objects,environment,environment,.signal flowContext,
        ⟨context.stateRep.heap,context.stateRep.cells,context.stateRep.shape,context.stateRep.nonempty⟩,
        .statement bodyCode,.cons .mode context.continuation,context.checkpoint⟩⟩

private theorem nested_loop_checked
    (checked : Admission.checkStatement registry fuel incoming returns (loops+1) unchecked statement = .ok flow) :
    Admission.checkStatement registry fuel incoming returns 1 unchecked statement = .ok flow :=
  (SourceControl.checkStatement_loops (loopsA := loops+1) (loopsB := 1) (by omega)).symm.trans checked

private theorem loop_incoming_environment {incoming : Admission.Context}
    (same : Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment)
    (shaped : SourceControl.ShapeFlow (Profile.scopesEnvironment incoming.scopes) flow) :
    Environment.Equivalent (Profile.scopesEnvironment
      ((Admission.mergeNormal flow.normal (Admission.meetContexts flow.continues)).getD incoming.relax).scopes) environment := by
  apply Environment.Equivalent.trans _ same
  apply Environment.Equivalent.of_eq
  exact SourceControl.getD_environment
    (SourceControl.mergeNormal_environment shaped.normal (SourceControl.meetContexts_environment shaped.continues)) rfl

theorem while_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext (.while_ test body)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.while_ test body),stack,state,entry⟩ := by
  cases code.form with
  | while_ testForm bodyForm =>
      obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := checked_successor code
      obtain ⟨afterTest,testChecked,checked⟩ := bind_checked checked
      obtain ⟨done,permission,checked⟩ := bind_checked checked
      cases done
      obtain ⟨bodyFlow,bodyChecked,_⟩ := bind_checked checked
      have boolean : test.type = .bool := by simpa using ensure_checked permission
      have testCode : ExpressionCode registry program environment test :=
        ⟨testForm,sourceFuel,incoming,afterTest,shape,testChecked⟩
      have bodyCode : StatementCode registry program environment flowContext.inLoop body :=
        ⟨bodyForm,⟨sourceFuel,afterTest,unchecked,bodyFlow,expression_after shape testForm testChecked,
          by simpa [Control.inLoop] using nested_loop_checked bodyChecked⟩,code.returnsReady⟩
      have postCode : StatementCode registry program environment flowContext .skip :=
        ⟨.skip,⟨1,incoming,false,Admission.Flow.next incoming,shape,rfl⟩,code.returnsReady⟩
      exact .inl ⟨⟨.loopTest test body .skip,stack,state,entry⟩,rfl,
        context.configuration (.loop testCode boolean bodyCode postCode),rfl⟩

theorem loop_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext (.loop test body post)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.loop test body post),stack,state,entry⟩ := by
  cases code.form with
  | loop testForm bodyForm postForm =>
      obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := checked_successor code
      obtain ⟨afterTest,testChecked,checked⟩ := bind_checked checked
      obtain ⟨done,permission,checked⟩ := bind_checked checked
      cases done
      obtain ⟨bodyFlow,bodyChecked,checked⟩ := bind_checked checked
      obtain ⟨done,_,checked⟩ := bind_checked checked
      cases done
      obtain ⟨postFlow,postChecked,_⟩ := bind_checked checked
      have boolean : test.type = .bool := by simpa using ensure_checked permission
      have afterShape := expression_after shape testForm testChecked
      have testCode : ExpressionCode registry program environment test :=
        ⟨testForm,sourceFuel,incoming,afterTest,shape,testChecked⟩
      have bodyCode : StatementCode registry program environment flowContext.inLoop body :=
        ⟨bodyForm,⟨sourceFuel,afterTest,unchecked,bodyFlow,afterShape,
          by simpa [Control.inLoop] using nested_loop_checked bodyChecked⟩,code.returnsReady⟩
      have postCode : StatementCode registry program environment flowContext post :=
        ⟨Profile.post_statement postForm,⟨sourceFuel,_,unchecked,postFlow,
          loop_incoming_environment afterShape (SourceControl.statement_scopes bodyForm bodyChecked),
          post_checked postForm postChecked⟩,code.returnsReady⟩
      exact .inl ⟨⟨.loopTest test body post,stack,state,entry⟩,rfl,
        context.configuration (.loop testCode boolean bodyCode postCode),rfl⟩

theorem doWhile_statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext (.doWhile body test)) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.doWhile body test),stack,state,entry⟩ := by
  cases code.form with
  | doWhile bodyForm testForm =>
      obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := checked_successor code
      obtain ⟨bodyFlow,bodyChecked,checked⟩ := bind_checked checked
      obtain ⟨done,_,checked⟩ := bind_checked checked
      cases done
      obtain ⟨afterTest,testChecked,checked⟩ := bind_checked checked
      obtain ⟨done,permission,_⟩ := bind_checked checked
      cases done
      have boolean : test.type = .bool := by simpa using ensure_checked permission
      have bodyCode : StatementCode registry program environment flowContext.inLoop body :=
        ⟨bodyForm,⟨sourceFuel,incoming,unchecked,bodyFlow,shape,
          by simpa [Control.inLoop] using nested_loop_checked bodyChecked⟩,code.returnsReady⟩
      have testCode : ExpressionCode registry program environment test :=
        ⟨testForm,sourceFuel,_,afterTest,
          loop_incoming_environment shape (SourceControl.statement_scopes bodyForm bodyChecked),testChecked⟩
      refine .inl ⟨⟨.exec body,.doBody body test :: stack,state,entry⟩,rfl,?_,rfl⟩
      exact ⟨⟨context.closed,objects,environment,environment,.signal flowContext.inLoop,context.stateRep,
        .statement bodyCode,.cons (.doBody bodyCode testCode boolean) context.continuation,context.checkpoint⟩⟩

theorem revert_statement_progress :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.revert bytes),stack,state,entry⟩ :=
  .inr ⟨.revert bytes,rfl,rfl⟩

private theorem body_prefix_progress
    (closed : Profile.ClosedProgram registry program)
    (stateRep : StateRep program objects environment state)
    (continuation : StackRep registry program state.heap objects (prefixEnvironment environment (.seq declaration rest))
      (.signal flowContext) stack)
    (checkpoint : ∃ entryObjects entryEnvironment, StateRep program entryObjects entryEnvironment entry)
    (code : BodyCode registry program environment flowContext (.seq declaration rest))
    (declarationForm : Profile.Declaration program declaration) (restForm : Profile.Body program rest) :
    StatementProgress registry program (fuel+2) choice ⟨.exec (.seq declaration rest),stack,state,entry⟩ := by
  obtain ⟨sourceFuel,incoming,unchecked,flow,shape,checked⟩ := code.admitted
  cases sourceFuel with
  | zero => cases checked
  | succ sourceFuel =>
      obtain ⟨a,firstChecked,checked⟩ := bind_checked checked
      obtain ⟨b,restChecked,_⟩ := bind_checked checked
      obtain ⟨binder,initializer,after,rfl,rfl,afterShape⟩ :=
        SourceControl.declaration_environment declarationForm firstChecked
      have declChecked : Admission.checkStatement registry sourceFuel incoming [] 0 false
          (.declare [some binder] initializer) = .ok (Admission.Flow.next after) := by
        cases sourceFuel with
        | zero => cases firstChecked
        | succ sourceFuel => simpa only [Admission.checkStatement] using firstChecked
      have declarationCode : DeclarationCode registry program environment (.declare [some binder] initializer) :=
        ⟨declarationForm,sourceFuel,incoming,Admission.Flow.next after,shape,declChecked⟩
      have afterShape : Environment.Equivalent (Profile.scopesEnvironment after.scopes) (Environment.declare environment binder) :=
        (Environment.Equivalent.of_eq afterShape).trans (shape.declare binder)
      have restCode : BodyCode registry program (Environment.declare environment binder) flowContext rest :=
        ⟨restForm,⟨sourceFuel,after,unchecked,b,afterShape,restChecked⟩,code.returnsReady⟩
      refine .inl ⟨⟨.exec (.declare [some binder] initializer),.next rest :: stack,state,entry⟩,rfl,?_,rfl⟩
      exact ⟨⟨closed,objects,environment,Environment.declare environment binder,.nextOnly,stateRep,
        .declaration declarationCode,.cons (.prefix restCode) continuation,checkpoint⟩⟩

/-- Actual dispatch for every statement in the admitted safety profile. The
source permissions and all child-code invariants are extracted from admission.
Only the independent current state and saved-continuation representations are
supplied by the configuration invariant. -/
theorem statement_progress
    (context : EvaluationContext registry program objects environment state entry stack (.signal flowContext))
    (code : StatementCode registry program environment flowContext statement) :
    StatementProgress registry program (fuel+2) choice ⟨.exec statement,stack,state,entry⟩ := by
  cases code.form with
  | skip => exact skip_statement_progress context
  | expr _ => exact expression_statement_progress context code
  | seq _ _ => exact sequence_statement_progress context code
  | block _ => exact block_statement_progress context code
  | if_ _ _ _ => exact branch_statement_progress context code
  | while_ _ _ => exact while_statement_progress context code
  | loop _ _ _ => exact loop_statement_progress context code
  | doWhile _ _ => exact doWhile_statement_progress context code
  | for_ _ _ _ _ => exact .inl (for_progress context code)
  | break_ => exact break_statement_progress context code
  | continue_ => exact continue_statement_progress context code
  | @return_ value _ =>
      cases value with
      | none => exact return_none_statement_progress context
      | some value => exact return_value_statement_progress context code
  | arithmetic _ => exact arithmetic_statement_progress context code
  | revert => exact revert_statement_progress

theorem body_progress
    (closed : Profile.ClosedProgram registry program)
    (stateRep : StateRep program objects environment state)
    (continuation : StackRep registry program state.heap objects (prefixEnvironment environment body)
      (.signal flowContext) stack)
    (checkpoint : ∃ entryObjects entryEnvironment, StateRep program entryObjects entryEnvironment entry)
    (code : BodyCode registry program environment flowContext body) :
    StatementProgress registry program (fuel+2) choice ⟨.exec body,stack,state,entry⟩ := by
  cases code.form with
  | statement form =>
      rw [SourceControl.statement_prefix form environment] at continuation
      exact statement_progress ⟨closed,stateRep,continuation,checkpoint⟩
        ⟨form,code.admitted,code.returnsReady⟩
  | declaration declaration rest => exact body_prefix_progress closed stateRep continuation checkpoint code declaration rest

end Solidity.Execution.Safety
