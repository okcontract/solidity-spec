/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.StepLaws

/-! Call-expression entry gathers the checked raw operands. Named argument
selection changes later parameter positions, never the set of evaluated
occurrences or the point at which conversions happen. -/
namespace Solidity.Execution.Safety
open Static Aggregates
open SourceTyping (bind_checked)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem call_formed_member (formed : Static.wellFormedTypes registry types = true)
    (member : type ∈ typesList types) : Static.wellFormed registry type = true := by
  cases types with
  | nil => cases member
  | cons first rest =>
      simp only [Static.wellFormedTypes,Bool.and_eq_true] at formed
      obtain ⟨head,tail⟩ := formed
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact call_formed_member tail member
termination_by sizeOf types

private theorem call_parameter_ready (checked : Admission.checkSignature registry fuel signature = .ok ())
    (supported : ∀ type ∈ typesList signature.parameters,Supported type) :
    ∀ type ∈ typesList signature.parameters,TypeReady registry type := by
  unfold Admission.checkSignature at checked
  obtain ⟨done,_,checked⟩ := bind_checked checked
  cases done
  obtain ⟨done,parameters,_⟩ := bind_checked checked
  cases done
  exact fun type member => ⟨supported type member,
    call_formed_member (SourceFormation.checkTypes_wellFormed parameters) member⟩

private theorem call_child_codes
    (same : Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment)
    (calleeForm : Profile.Expression program callee) (argumentsForm : Profile.Expressions program arguments)
    (checked : Admission.checkExpressions registry fuel incoming (callee :: arguments) = .ok after) :
    ∀ expression ∈ callee :: arguments,ExpressionCode registry program environment expression := by
  intro expression member
  obtain ⟨childFuel,childAfter,childChecked⟩ := SourceTyping.children_checked checked member
  refine ⟨?_,childFuel,{incoming with orderIndependent := true},childAfter,same,childChecked⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact calleeForm
  · exact Profile.expressions_member argumentsForm member

private theorem call_function_ready {signature : FunctionSignature} (code : ExpressionCode registry program environment callee)
    (allowed : Static.Implicit callee.type signature.type) : TypeReady registry callee.type := by
  refine ⟨?_,code.formed⟩
  rcases Profile.expression_output callee code.form with supported | ⟨members,shape⟩
  · exact supported
  · rw [shape] at allowed
    simp [Static.Implicit,FunctionSignature.type] at allowed

private theorem call_arguments_ready (arguments : List (Expr EmptyKey)) (types : List SType)
    (children : ∀ expression ∈ arguments,ExpressionCode registry program environment expression)
    (targets : ∀ type ∈ types,TypeReady registry type) (arity : arguments.length = types.length)
    (permissions : ∀ argument type,(argument,type) ∈ arguments.zip types →
      ∃ kind,TransferRule true argument.type type kind) :
    ArgumentsReady registry (arguments.map Expr.type) types := by
  induction arguments generalizing types with
  | nil =>
      have empty : types = [] := List.eq_nil_of_length_eq_zero arity.symm
      subst types
      exact .nil
  | cons argument arguments ih =>
      cases types with
      | nil => simp at arity
      | cons type types =>
          obtain ⟨kind,permission⟩ := permissions argument type (by simp)
          have target := targets type (by simp)
          exact .cons ⟨(children argument (by simp)).transfer_source_ready target.1 permission,target,kind,permission⟩
            (ih types (fun expression member => children expression (by simp [member]))
              (fun type member => targets type (by simp [member])) (by simpa using arity)
              (fun expression type member => permissions expression type (by simp [member])))

private theorem call_selects_map {α β : Type} {source selected : List α} {order : List Nat}
    (selection : ArgumentOrder.Selects source order selected) (f : α → β) :
    ArgumentOrder.Selects (source.map f) order (selected.map f) := by
  induction selection with
  | nil => exact .nil
  | cons entry rest ih =>
      exact .cons (by simp only [List.getElem?_map,entry,Option.map_some]) ih

private theorem call_selects_member (selection : ArgumentOrder.Selects source order selected)
    (member : value ∈ selected) : value ∈ source := by
  induction selection with
  | nil => cases member
  | cons entry rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_of_getElem? entry
      · exact ih member

theorem eval_call_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value signature.resultType))
    (code : ExpressionCode registry program environment (.call signature callee arguments)) :
    StepRep registry program ⟨.eval (.call signature callee arguments),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval (.call signature callee arguments),stack,state,entry⟩) := by
  cases code.form with
  | call calleeForm argumentsForm parametersSupported returnsSupported =>
      obtain ⟨sourceFuel,incoming,after,same,checked⟩ := code.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          obtain ⟨signatureChecked,allowed,_,childrenChecked,arity,permissions,_⟩ := SourceTyping.call_checked checked
          have children := call_child_codes same calleeForm argumentsForm childrenChecked
          have functionReady := call_function_ready (children callee (by simp)) allowed
          have argumentsReady := call_arguments_ready arguments (typesList signature.parameters)
            (fun expression member => children expression (by simp [member]))
            (call_parameter_ready signatureChecked parametersSupported) arity permissions
          let final : Config Unit EmptyKey :=
            ⟨.collect ((callee :: arguments).zipIdx.map fun (expression,index) => (index,expression)) [] (.call signature),
              stack,state,entry⟩
          apply stepRep_next (after := final) rfl
          · exact context.gather children (.call functionReady allowed argumentsReady)
          · rfl
          · simp only [final]
            omega

theorem eval_namedCall_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value signature.resultType))
    (code : ExpressionCode registry program environment (.namedCall signature callee arguments order)) :
    StepRep registry program ⟨.eval (.namedCall signature callee arguments order),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.eval (.namedCall signature callee arguments order),stack,state,entry⟩) := by
  cases code.form with
  | namedCall calleeForm argumentsForm parametersSupported returnsSupported =>
      obtain ⟨sourceFuel,incoming,after,same,checked⟩ := code.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          obtain ⟨signatureChecked,allowed,_,ordered,childrenChecked,selected,arity,permissions,_⟩ :=
            SourceTyping.named_call_checked checked
          have children := call_child_codes same calleeForm argumentsForm childrenChecked
          have functionReady := call_function_ready (children callee (by simp)) allowed
          obtain ⟨orderValid,selection⟩ := (ArgumentOrder.select_iff _ _ _).mp selected
          have orderedChildren : ∀ expression ∈ ordered,ExpressionCode registry program environment expression := by
            intro expression member
            exact children expression (List.mem_cons_of_mem callee (call_selects_member selection member))
          have argumentsReady := call_arguments_ready ordered (typesList signature.parameters) orderedChildren
            (call_parameter_ready signatureChecked parametersSupported) arity permissions
          have selectedTypes : ArgumentOrder.select order (arguments.map Expr.type) = .ok (ordered.map Expr.type) :=
            (ArgumentOrder.select_iff _ _ _).mpr ⟨by simpa only [List.length_map] using orderValid,
              call_selects_map selection Expr.type⟩
          let final : Config Unit EmptyKey :=
            ⟨.collect ((callee :: arguments).zipIdx.map fun (expression,index) => (index,expression)) []
              (.namedCall signature order),stack,state,entry⟩
          apply stepRep_next (after := final) rfl
          · exact context.gather children (.namedCall functionReady allowed
              (by simpa only [List.length_map] using orderValid) ⟨_,selectedTypes,argumentsReady⟩)
          · rfl
          · simp only [final]
            omega

end Solidity.Execution.Safety
