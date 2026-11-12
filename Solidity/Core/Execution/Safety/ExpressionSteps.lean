/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Administrative
import Solidity.Core.Execution.Safety.SourceScopes
import Solidity.Core.Execution.Safety.CodeLaws

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

structure EvaluationContext (registry : Registry) (program : Program EmptyKey)
    (objects : List WordArena.Object) (environment : Environment)
    (state entry : MachineState Unit) (stack : List (Frame EmptyKey)) (kind : Kind) : Prop where
  closed : Profile.ClosedProgram registry program
  stateRep : StateRep program objects environment state
  continuation : StackRep registry program state.heap objects environment kind stack
  checkpoint : ∃ entryObjects entryEnvironment, StateRep program entryObjects entryEnvironment entry

def EvaluationContext.witness (context : EvaluationContext registry program objects environment
    state entry stack kind) (taskRep : TaskRep registry program state.heap objects environment task environment kind) :
    ConfigurationWitness registry program ⟨task,stack,state,entry⟩ :=
  ⟨context.closed,objects,environment,environment,kind,context.stateRep,taskRep,
    context.continuation,context.checkpoint⟩

theorem EvaluationContext.configuration (context : EvaluationContext registry program objects environment
    state entry stack kind) (taskRep : TaskRep registry program state.heap objects environment task environment kind) :
    ConfigurationRep registry program ⟨task,stack,state,entry⟩ :=
  ⟨context.witness taskRep⟩

theorem EvaluationContext.gather {expressions : List (Expr EmptyKey)} (context : EvaluationContext registry program objects environment
    state entry stack kind) (children : ∀ expression ∈ expressions, ExpressionCode registry program environment expression)
    (completion : CompletionRep registry finish (expressions.map Expr.type) kind) :
    ConfigurationRep registry program
      ⟨.collect (expressions.zipIdx.map fun (expression,index) => (index,expression)) [] finish,stack,state,entry⟩ :=
  context.configuration (.collect (TypedPackets.CollectRep.initial expressions children) completion)

theorem literal_progress (context : EvaluationContext registry program objects environment state entry stack (.value value.type))
    (code : ExpressionCode registry program environment (.literal value)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.eval (.literal value),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases code.form with
  | literal supported closed =>
      refine ⟨⟨.value (.atom value),stack,state,entry⟩,rfl,?_,rfl⟩
      exact context.configuration (.value (.atom (.scalar supported closed)))

theorem unary_progress (context : EvaluationContext registry program objects environment state entry stack (.value value.type))
    (codeRep : ExpressionCode registry program environment (.unary code value)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.eval (.unary code value),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases codeRep.form with
  | unary form supported =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := codeRep.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          obtain ⟨childAfter,child,permission,_⟩ := SourceTyping.unary_checked checked
          have childCode : ExpressionCode registry program environment value :=
            ⟨form,sourceFuel,incoming,childAfter,shape,child⟩
          refine ⟨⟨.collect ([(value : Expr EmptyKey)].zipIdx.map fun (value,index) => (index,value)) [] (.unary code),
            stack,state,entry⟩,rfl,?_,rfl⟩
          apply context.gather
          · intro expression member
            rcases List.mem_singleton.mp member with rfl
            exact childCode
          · exact .unary supported permission

theorem binary_eager_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value result))
    (codeRep : ExpressionCode registry program environment (.binary code result left right))
    (eager : (code != .and && code != .or) = true) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.eval (.binary code result left right),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases codeRep.form with
  | binary leftForm rightForm leftSupport rightSupport resultSupport =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := codeRep.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          have allowed := (SourceTyping.binary_checked checked).1
          have children : ∀ expression ∈ [left,right], ExpressionCode registry program environment expression := by
            intro expression member
            obtain ⟨childFuel,childAfter,child⟩ := SourceTyping.binary_eager_children checked eager member
            refine ⟨?_,childFuel,{incoming with orderIndependent := true},childAfter,shape,child⟩
            rcases List.mem_cons.mp member with rfl | member
            · exact leftForm
            · cases List.mem_singleton.mp member
              exact rightForm
          let after : Config Unit EmptyKey :=
            ⟨.collect ([left,right].zipIdx.map fun (expression,index) => (index,expression)) [] (.binary code result),stack,state,entry⟩
          refine ⟨after,?_,context.gather children (.binary leftSupport rightSupport resultSupport allowed),rfl⟩
          apply step_of_transition
          have both : code ≠ .and ∧ code ≠ .or := by simpa using eager
          cases code <;> simp_all [Machine.transition,Machine.gather,Machine.next,after]

private theorem expressions_member (forms : Profile.Expressions program expressions) (member : expression ∈ expressions) :
    Profile.Expression program expression := by
  induction expressions with
  | nil => cases member
  | cons head tail induction =>
      cases forms with
      | cons first rest =>
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact induction rest member

private theorem expressionTypes_ofList (expressions : List (Expr EmptyKey)) :
    expressionTypes expressions = Types.ofList (expressions.map Expr.type) := by
  induction expressions with
  | nil => rfl
  | cons expression expressions induction => simp [expressionTypes,Types.ofList,induction]

theorem tuple_progress (context : EvaluationContext registry program objects environment state entry stack (.value (.tuple (expressionTypes expressions))))
    (codeRep : ExpressionCode registry program environment (.tuple expressions)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.eval (.tuple expressions),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases codeRep.form with
  | tuple forms =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := codeRep.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          have children : ∀ expression ∈ expressions, ExpressionCode registry program environment expression := by
            intro expression member
            obtain ⟨childFuel,childAfter,child⟩ := SourceTyping.children_checked checked member
            exact ⟨expressions_member forms member,childFuel,{incoming with orderIndependent := true},childAfter,shape,child⟩
          refine ⟨⟨.collect (expressions.zipIdx.map fun (expression,index) => (index,expression)) [] .tuple,stack,state,entry⟩,
            rfl,?_,rfl⟩
          apply context.gather children
          rw [expressionTypes_ofList]
          exact .tuple _

theorem conditional_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value yes.type))
    (codeRep : ExpressionCode registry program environment (.conditional test yes no)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.eval (.conditional test yes no),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases codeRep.form with
  | conditional testForm yesForm noForm =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := codeRep.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          obtain ⟨testAfter,yesAfter,noAfter,testChecked,boolean,yesChecked,noChecked,same,_⟩ :=
            SourceTyping.conditional_checked checked
          have testCode : ExpressionCode registry program environment test :=
            ⟨testForm,sourceFuel,incoming,testAfter,shape,testChecked⟩
          have afterShape : Environment.Equivalent (Profile.scopesEnvironment testAfter.scopes) environment :=
            (Environment.Equivalent.of_eq
              (congrArg Profile.scopesEnvironment (SourceTyping.checkExpression_scopes testForm testChecked))).trans shape
          have yesCode : ExpressionCode registry program environment yes :=
            ⟨yesForm,sourceFuel,testAfter,yesAfter,afterShape,yesChecked⟩
          have noCode : ExpressionCode registry program environment no :=
            ⟨noForm,sourceFuel,testAfter,noAfter,afterShape,noChecked⟩
          refine ⟨⟨.eval test,.select yes no :: stack,state,entry⟩,rfl,?_,rfl⟩
          exact ⟨⟨context.closed,objects,environment,environment,.value test.type,context.stateRep,
            .eval testCode,boolean ▸ .cons (.select yesCode noCode same) context.continuation,context.checkpoint⟩⟩

theorem cast_progress (context : EvaluationContext registry program objects environment state entry stack (.value target))
    (codeRep : ExpressionCode registry program environment (.cast mode target source)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.eval (.cast mode target source),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases codeRep.form with
  | cast form sourceSupport targetSupport =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := codeRep.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          obtain ⟨childAfter,child,permission,_⟩ := SourceTyping.scalar_cast_checked checked sourceSupport
          have childCode : ExpressionCode registry program environment source :=
            ⟨form,sourceFuel,incoming,childAfter,shape,child⟩
          refine ⟨⟨.collect ([source].zipIdx.map fun (value,index) => (index,value)) [] (.cast mode target),stack,state,entry⟩,
            rfl,?_,rfl⟩
          apply context.gather
          · intro expression member
            cases List.mem_singleton.mp member
            exact childCode
          · exact .cast sourceSupport targetSupport permission childCode.formed codeRep.formed

theorem newArray_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (WordArena.arrayType true)))
    (codeRep : ExpressionCode registry program environment (.newArray (.uint 31) count)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.eval (.newArray (.uint 31) count),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases codeRep.form with
  | newArray form =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := codeRep.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          obtain ⟨childAfter,child,unsigned,_,_⟩ := SourceTyping.newArray_checked checked
          obtain ⟨width,countType⟩ := SourceTyping.unsigned_type unsigned
          have childCode : ExpressionCode registry program environment count :=
            ⟨form,sourceFuel,incoming,childAfter,shape,child⟩
          refine ⟨⟨.collect ([count].zipIdx.map fun (value,index) => (index,value)) [] (.newArray (.uint 31)),stack,state,entry⟩,
            rfl,?_,rfl⟩
          apply context.gather
          · intro expression member
            cases List.mem_singleton.mp member
            exact childCode
          · simpa only [List.map_cons,List.map_nil,countType] using (CompletionRep.newArray (registry := registry) width)

theorem length_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (.uint 31)))
    (codeRep : ExpressionCode registry program environment (.length source)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.eval (.length source),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases codeRep.form with
  | length form array =>
      obtain ⟨pointer,arrayType⟩ := array
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := codeRep.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          obtain ⟨childAfter,child,_,_⟩ := SourceTyping.length_checked checked
          have childCode : ExpressionCode registry program environment source :=
            ⟨form,sourceFuel,incoming,childAfter,shape,child⟩
          refine ⟨⟨.collect ([source].zipIdx.map fun (value,index) => (index,value)) [] .length,stack,state,entry⟩,
            rfl,?_,rfl⟩
          apply context.gather
          · intro expression member
            cases List.mem_singleton.mp member
            exact childCode
          · simpa only [List.map_cons,List.map_nil,arrayType] using (CompletionRep.length (registry := registry) pointer)

theorem index_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (.uint 31)))
    (codeRep : ExpressionCode registry program environment (.index (.uint 31) source index)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.eval (.index (.uint 31) source index),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases codeRep.form with
  | index sourceForm array indexForm =>
      obtain ⟨pointer,arrayType⟩ := array
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := codeRep.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          obtain ⟨childrenAfter,checkedChildren,unsigned,_,_⟩ := SourceTyping.index_checked checked
          obtain ⟨width,indexType⟩ := SourceTyping.unsigned_type unsigned
          have children : ∀ expression ∈ [source,index], ExpressionCode registry program environment expression := by
            intro expression member
            obtain ⟨childFuel,childAfter,child⟩ := SourceTyping.children_checked checkedChildren member
            refine ⟨?_,childFuel,{incoming with orderIndependent := true},childAfter,shape,child⟩
            rcases List.mem_cons.mp member with rfl | member
            · exact sourceForm
            · cases List.mem_singleton.mp member
              exact indexForm
          refine ⟨⟨.collect ([source,index].zipIdx.map fun (value,index) => (index,value)) [] (.readIndex (.uint 31)),stack,state,entry⟩,
            rfl,?_,rfl⟩
          apply context.gather children
          simpa only [List.map_cons,List.map_nil,arrayType,indexType] using
            (CompletionRep.readIndex (registry := registry) pointer width)

theorem read_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value target.type))
    (codeRep : ExpressionCode registry program environment (.read target)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.eval (.read target),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases codeRep.form with
  | read form =>
      obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := codeRep.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          have targetCode : TargetCode registry program environment target :=
            ⟨form,sourceFuel,incoming,after,false,shape,checked⟩
          refine ⟨⟨.capture target,.readTarget :: stack,state,entry⟩,rfl,?_,rfl⟩
          exact ⟨⟨context.closed,objects,environment,environment,.target target.type,context.stateRep,
            .capture targetCode,.cons .readTarget context.continuation,context.checkpoint⟩⟩

end Solidity.Execution.Safety
