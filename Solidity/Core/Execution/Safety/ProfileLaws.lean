/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Profile

namespace Solidity.Execution.Safety.Profile
open Static Aggregates

def OutputType (type : SType) : Prop := Supported type ∨ ∃ members, type = .tuple members

theorem target_supported (form : Target program target) : Supported target.type := by
  cases form with
  | «local» supported => exact supported
  | heap physical =>
      simp only [LValue.type]
      rw [physical.1]
      exact .inl rfl
  | index _ _ _ => exact .inl rfl

theorem call_output {signature : FunctionSignature} (returnsSupported : ∀ type ∈ typesList signature.returns, Supported type) :
    OutputType signature.resultType := by
  cases shape : signature.returns with
  | nil => exact .inr ⟨.nil,by simp [FunctionSignature.resultType,shape]⟩
  | cons type rest =>
      cases rest with
      | nil => exact .inl (by simpa [FunctionSignature.resultType,shape] using returnsSupported type (by simp [shape,typesList]))
      | cons next rest => exact .inr ⟨.cons type (.cons next rest),by simp [FunctionSignature.resultType,shape]⟩

theorem expression_output (expression : Expr EmptyKey) (form : Expression program expression) : OutputType expression.type := by
  cases form with
  | literal supported _ => exact .inl (.inl supported)
  | «local» supported => exact .inl supported
  | read target => exact .inl (target_supported target)
  | @arithmetic value mode source =>
      exact expression_output value source
  | cast _ _ supported => exact .inl (.inl supported)
  | unary _ supported => exact .inl (.inl supported)
  | binary _ _ _ _ supported => exact .inl (.inl supported)
  | @conditional test yesValue noValue testForm yes noForm =>
      exact expression_output yesValue yes
  | tuple _ => exact .inr ⟨_,rfl⟩
  | assign target _ => exact .inl (target_supported target)
  | compound _ _ supported _ => exact .inl (.inl supported)
  | @update target code targetForm supported nondelete =>
      cases code <;> simp_all [Expr.type,OutputType,Supported]
  | call _ _ _ supported => exact call_output supported
  | namedCall _ _ _ supported => exact call_output supported
  | assert_ _ => exact .inr ⟨.nil,rfl⟩
  | require_ _ => exact .inr ⟨.nil,rfl⟩
  | revertWith => exact .inr ⟨.nil,rfl⟩
  | newArray _ => exact .inl (.inr ⟨true,rfl⟩)
  | length _ array =>
      obtain ⟨pointer,shape⟩ := array
      left; left
      simp [Expr.type,shape,WordArena.arrayType,SType.scalarSupported]
  | index _ _ _ => exact .inl (.inl rfl)
termination_by sizeOf expression

theorem transfer_source_supported (sourceShape : OutputType source) (targetSupported : Supported target)
    (permission : TransferRule localBinding source target kind) : Supported source := by
  rcases sourceShape with supported | ⟨members,rfl⟩
  · exact supported
  · cases kind <;> try {simp [TransferRule,referenceLocation] at permission}
    case scalarConversion =>
      simp only [TransferRule,referenceLocation] at permission
      have implicit := permission.2.2
      rcases targetSupported with supported | ⟨pointer,rfl⟩
      · cases target <;> simp_all [Static.Implicit,SType.scalarSupported]
      · simp [Static.Implicit,WordArena.arrayType] at implicit

theorem post_statement (form : Post program statement) : Statement program statement := by
  cases form with
  | skip => exact .skip
  | expr expression => exact .expr expression

theorem expressions_member (forms : Expressions program expressions) (member : expression ∈ expressions) :
    Expression program expression := by
  induction expressions with
  | nil => cases member
  | cons head tail induction =>
      cases forms with
      | cons first rest =>
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact induction rest member

theorem supported_components (supported : Supported type) : Admission.resultComponents type = [type] := by
  rcases supported with scalar | ⟨pointer,rfl⟩
  · cases type <;> simp_all [SType.scalarSupported,Admission.resultComponents]
  · rfl

private theorem components_of_supported (supported : Supported type) :
    ∀ component ∈ Admission.resultComponents type, OutputType component := by
  rw [supported_components supported]
  intro component member
  cases List.mem_singleton.mp member
  exact .inl supported

theorem call_components {signature : FunctionSignature}
    (returnsSupported : ∀ type ∈ typesList signature.returns, Supported type) :
    Admission.resultComponents signature.resultType = typesList signature.returns := by
  cases shape : signature.returns with
  | nil => simp [FunctionSignature.resultType,shape,Admission.resultComponents,typesList]
  | cons type rest =>
      cases rest with
      | nil =>
          simpa only [FunctionSignature.resultType,shape,typesList] using
            supported_components (returnsSupported type (by simp [shape,typesList]))
      | cons next rest => simp [FunctionSignature.resultType,shape,Admission.resultComponents,typesList]

private theorem typesList_expressionTypes (expressions : List (Expr EmptyKey)) :
    typesList (expressionTypes expressions) = expressions.map Expr.type := by
  induction expressions with
  | nil => rfl
  | cons first rest induction => simp [typesList,expressionTypes,induction]

theorem component_output (expression : Expr EmptyKey) (form : Expression program expression) :
    ∀ component ∈ Admission.resultComponents expression.type, OutputType component := by
  cases form with
  | literal supported _ => exact components_of_supported (.inl supported)
  | «local» supported => exact components_of_supported supported
  | read target => exact components_of_supported (target_supported target)
  | @arithmetic value mode source => exact component_output value source
  | cast _ _ supported => exact components_of_supported (.inl supported)
  | unary _ supported => exact components_of_supported (.inl supported)
  | binary _ _ _ _ supported => exact components_of_supported (.inl supported)
  | @conditional test yesValue noValue testForm yes noForm => exact component_output yesValue yes
  | tuple forms =>
      intro component member
      change component ∈ typesList (expressionTypes _) at member
      rw [typesList_expressionTypes] at member
      obtain ⟨child,found,rfl⟩ := List.mem_map.mp member
      exact expression_output child (expressions_member forms found)
  | assign target _ => exact components_of_supported (target_supported target)
  | compound _ _ supported _ => exact components_of_supported (.inl supported)
  | @update target code targetForm supported nondelete =>
      cases code with
      | delete => exact False.elim (nondelete rfl)
      | inc post | dec post => exact components_of_supported (.inl supported)
  | call _ _ _ supported =>
      intro component member
      simp only [Expr.type] at member
      rw [call_components supported] at member
      exact .inl (supported component member)
  | namedCall _ _ _ supported =>
      intro component member
      simp only [Expr.type] at member
      rw [call_components supported] at member
      exact .inl (supported component member)
  | assert_ _ | require_ _ | revertWith => simp [Expr.type,Admission.resultComponents,typesList]
  | newArray _ => exact components_of_supported (.inr ⟨true,rfl⟩)
  | length _ array =>
      obtain ⟨pointer,shape⟩ := array
      simp only [Expr.type,shape,WordArena.arrayType]
      exact components_of_supported (.inl rfl)
  | index _ _ _ => exact components_of_supported (.inl rfl)
termination_by sizeOf expression

end Solidity.Execution.Safety.Profile
