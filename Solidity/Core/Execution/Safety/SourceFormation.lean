/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.SourceTyping
import Solidity.Core.Execution.Safety.SupportedEligibility

/-! Result-type metadata is justified by actual admission, including nominal
registry entries and internal-function mutability. Structural profile membership
does not grant source permissions or replace the checker. -/
namespace Solidity.Execution.Safety.SourceFormation
open Static Aggregates Admission SourceTyping
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem checkTypes_wellFormed (checked : checkTypes registry fuel types = .ok ()) :
    Static.wellFormedTypes registry types = true := by
  cases types with
  | nil => rfl
  | cons first rest =>
      obtain ⟨done,firstChecked,restChecked⟩ := bind_checked checked
      cases done
      simp [Static.wellFormedTypes,SupportedEligibility.checkType_wellFormed firstChecked,
        checkTypes_wellFormed restChecked]
termination_by sizeOf types

theorem checkSignature_wellFormed (checked : checkSignature registry fuel signature = .ok ()) :
    Static.wellFormed registry signature.type = true ∧
      Static.wellFormedTypes registry signature.returns = true := by
  unfold checkSignature at checked
  obtain ⟨done,mutabilityChecked,rest⟩ := bind_checked checked
  cases done
  obtain ⟨done,parametersChecked,returnsChecked⟩ := bind_checked rest
  cases done
  have mutability := ensure_checked mutabilityChecked
  have parameters := checkTypes_wellFormed parametersChecked
  have returns := checkTypes_wellFormed returnsChecked
  exact ⟨by simp [FunctionSignature.type,Static.wellFormed,mutability,parameters,returns],returns⟩

theorem signature_result_wellFormed {signature : FunctionSignature}
    (formed : Static.wellFormedTypes registry signature.returns = true) :
    Static.wellFormed registry signature.resultType = true := by
  cases signature with
  | mk mutability parameters returns =>
      cases returns with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => simpa [FunctionSignature.resultType,Static.wellFormedTypes] using formed
          | cons next tail => exact formed

private theorem scalar_group_wellFormed
    (checked : groupTransfer registry fuel source target = .ok ())
    (sourceSupport : source.scalarSupported = true) (targetSupport : target.scalarSupported = true) :
    Static.wellFormed registry target = true := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      simp only [groupTransfer,(scalar_shape sourceSupport).2.1,(scalar_shape targetSupport).2.1] at checked
      unfold transfer at checked
      obtain ⟨kind,planned,_⟩ := bind_checked checked
      exact (SupportedEligibility.planTransfer_wellFormed planned).2

private theorem cast_wellFormed
    (checked : checkExpression registry (fuel+1) incoming (.cast mode target value) = .ok after)
    (sourceSupport : value.type.scalarSupported = true) (targetSupport : target.scalarSupported = true) :
    Static.wellFormed registry target = true := by
  cases mode with
  | implicit =>
      simp only [checkExpression] at checked
      obtain ⟨childAfter,_,rest⟩ := bind_checked checked
      obtain ⟨done,transferred,_⟩ := bind_checked rest
      cases done
      exact scalar_group_wellFormed transferred sourceSupport targetSupport
  | explicit kind =>
      cases kind <;>
        simp only [checkExpression] at checked
      all_goals
        obtain ⟨childAfter,_,rest⟩ := bind_checked checked
        obtain ⟨done,_,rest⟩ := bind_checked rest
        cases done
        obtain ⟨done,targetChecked,_⟩ := bind_checked rest
        cases done
        exact SupportedEligibility.checkType_wellFormed targetChecked

private theorem binary_wellFormed (allowed : Admission.BinaryAllowed code left right result) :
    Static.wellFormed registry result = true := by
  have resultFormed : ∀ {code left right result}, ScalarBinary code left right result →
      Static.wellFormed registry result = true := by
    intro code left right result operation
    cases operation <;> rfl
  cases allowed with
  | asymmetric _ operation => exact resultFormed operation
  | common _ _ _ operation => exact resultFormed operation

private theorem expressions_member (forms : Profile.Expressions program values) (member : value ∈ values) :
    Profile.Expression program value := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      cases forms with
      | cons first rest =>
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact ih rest member

private theorem expressionTypes_wellFormed (values : List (Expr Key))
    (formed : ∀ value ∈ values, Static.wellFormed registry value.type = true) :
    Static.wellFormedTypes registry (expressionTypes values) = true := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      simp only [expressionTypes,Static.wellFormedTypes,Bool.and_eq_true]
      exact ⟨formed first (by simp),ih fun value member => formed value (by simp [member])⟩

private theorem update_type (code : UpdateCode) (target : LValue Key) (nondelete : code ≠ .delete) :
    (Expr.update code target).type = target.type := by
  cases code <;> simp_all [Expr.type]

private theorem formation (program : Program EmptyKey) (registry : Registry) (fuel : Nat) :
    (∀ expression, Profile.Expression program expression → ∀ incoming after,
      checkExpression registry fuel incoming expression = .ok after → Static.wellFormed registry expression.type = true) ∧
    (∀ target, Profile.Target program target → ∀ writable incoming after,
      checkLValue registry fuel incoming target writable = .ok after → Static.wellFormed registry target.type = true) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      cases fuel with
      | zero =>
          constructor
          · intro expression form incoming after checked; cases checked
          · intro target form writable incoming after checked; cases checked
      | succ fuel =>
          constructor
          · intro expression form incoming after checked
            cases form with
            | literal supported closed =>
                simp only [checkExpression] at checked
                obtain ⟨done,typeChecked,_⟩ := bind_checked checked
                cases done
                exact SupportedEligibility.checkType_wellFormed typeChecked
            | «local» supported =>
                simp only [checkExpression] at checked
                obtain ⟨done,_,rest⟩ := bind_checked checked
                cases done
                obtain ⟨done,typeChecked,_⟩ := bind_checked rest
                cases done
                exact SupportedEligibility.checkType_wellFormed typeChecked
            | read targetForm => exact (ih fuel (by omega)).2 _ targetForm _ _ _ checked
            | arithmetic source =>
                have formed := (ih fuel (by omega)).1 _ source _ _ checked
                exact formed
            | cast source scalarSource scalarTarget => exact cast_wellFormed checked scalarSource scalarTarget
            | unary source scalar =>
                obtain ⟨childAfter,child,_,_⟩ := unary_checked checked
                have formed := (ih fuel (by omega)).1 _ source _ _ child
                exact formed
            | binary left right leftScalar rightScalar resultScalar =>
                exact binary_wellFormed (binary_checked checked).1
            | conditional test yes no =>
                obtain ⟨testAfter,yesAfter,noAfter,_,_,yesChecked,_,_,_⟩ := conditional_checked checked
                have formed := (ih fuel (by omega)).1 _ yes _ _ yesChecked
                exact formed
            | tuple values =>
                change Static.wellFormedTypes registry (expressionTypes _) = true
                apply expressionTypes_wellFormed
                intro value member
                cases fuel with
                | zero => cases checked
                | succ smaller =>
                    obtain ⟨childAfter,child⟩ := Admission.checkExpressions_each checked member
                    exact (ih smaller (by omega)).1 _ (expressions_member values member) _ _ child
            | assign targetForm valueForm =>
                obtain ⟨_,captured,_,_,capturedChecked,_,_⟩ := assign_checked checked
                obtain ⟨raw,child,_⟩ := independent_checked capturedChecked
                exact (ih fuel (by omega)).2 _ targetForm _ _ _ child
            | compound targetForm valueForm scalarTarget scalarValue =>
                obtain ⟨_,_,captured,_,capturedChecked,_,_⟩ := compound_checked checked
                obtain ⟨raw,child,_⟩ := independent_checked capturedChecked
                obtain ⟨written,writeChecked,_⟩ := bind_checked child
                exact (ih fuel (by omega)).2 _ targetForm _ _ _ writeChecked
            | update targetForm scalar nondelete =>
                obtain ⟨captured,_,capturedChecked,_,_,_⟩ := update_checked checked nondelete
                have targetFormed := (ih fuel (by omega)).2 _ targetForm _ _ _ capturedChecked
                rw [update_type _ _ nondelete]
                exact targetFormed
            | call calleeForm argumentsForm parameters returns =>
                exact signature_result_wellFormed (checkSignature_wellFormed (call_checked checked).1).2
            | namedCall calleeForm argumentsForm parameters returns =>
                exact signature_result_wellFormed (checkSignature_wellFormed (named_call_checked checked).1).2
            | assert_ => rfl
            | require_ => rfl
            | revertWith => rfl
            | newArray => rfl
            | length source array =>
                rcases array with ⟨pointer,arrayType⟩
                simp only [Expr.type,arrayType,WordArena.arrayType,Static.wellFormed]
            | index => rfl
          · intro target form writable incoming after checked
            cases form with
            | «local» supported =>
                exact SupportedEligibility.checkType_wellFormed (local_target_checked checked).2.1
            | heap physical =>
                simp only [LValue.type,physical.1,Static.wellFormed]
            | index => rfl

theorem expression_wellFormed (form : Profile.Expression program expression)
    (checked : checkExpression registry fuel incoming expression = .ok after) :
    Static.wellFormed registry expression.type = true := (formation program registry fuel).1 _ form _ _ checked

theorem target_wellFormed (form : Profile.Target program target)
    (checked : checkLValue registry fuel incoming target writable = .ok after) :
    Static.wellFormed registry target.type = true := (formation program registry fuel).2 _ form _ _ _ checked

end Solidity.Execution.Safety.SourceFormation
