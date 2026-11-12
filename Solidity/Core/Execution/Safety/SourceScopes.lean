/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.SourceTyping

/-! Lexical scope preservation of actual admission in the declared safety
profile. Readiness and unresolved-call flags may change; expression admission
cannot introduce a declaration or switch to another lexical environment. -/
namespace Solidity.Execution.Safety.SourceTyping
open Static Aggregates Admission
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem returned_scopes (checked : (pure incoming : Aggregates.Result Admission.Context) = .ok after) :
    after.scopes = incoming.scopes := congrArg Admission.Context.scopes (Except.ok.inj checked).symm

private theorem metadata_scopes (action : Aggregates.Result α) (incoming : Admission.Context)
    (checked : (action >>= fun _ => pure incoming) = .ok after) : after.scopes = incoming.scopes := by
  obtain ⟨_,_,rest⟩ := bind_checked checked
  exact returned_scopes rest

theorem markTarget_scopes (context : Admission.Context) (target : LValue Key) :
    (markTarget context target).scopes = context.scopes := by
  cases target <;> rfl

private theorem profile_scopes (program : Program EmptyKey) (registry : Registry) (fuel : Nat) :
    (∀ expression, Profile.Expression program expression → ∀ incoming after,
      checkExpression registry fuel incoming expression = .ok after → after.scopes = incoming.scopes) ∧
    (∀ target, Profile.Target program target → ∀ writable incoming after,
      checkLValue registry fuel incoming target writable = .ok after → after.scopes = incoming.scopes) := by
  induction fuel with
  | zero =>
      constructor
      · intro expression form incoming after checked; cases checked
      · intro target form writable incoming after checked; cases checked
  | succ fuel ih =>
      constructor
      · intro expression form incoming after checked
        cases form with
        | literal supported closed =>
            simp only [checkExpression] at checked
            exact metadata_scopes _ _ checked
        | «local» supported =>
            simp only [checkExpression] at checked
            obtain ⟨_,_,rest⟩ := bind_checked checked
            exact metadata_scopes _ _ rest
        | read targetForm => exact ih.2 _ targetForm _ _ _ checked
        | arithmetic source => exact ih.1 _ source _ _ checked
        | cast source scalarSource scalarTarget =>
            obtain ⟨childAfter,child,_,equal⟩ := scalar_cast_checked checked scalarSource
            exact (congrArg Admission.Context.scopes equal).trans (ih.1 _ source _ _ child)
        | unary source scalar =>
            obtain ⟨childAfter,child,_,equal⟩ := unary_checked checked
            exact (congrArg Admission.Context.scopes equal).trans (ih.1 _ source _ _ child)
        | binary left right leftScalar rightScalar resultScalar =>
            obtain ⟨_,childrenAfter,children,equal⟩ := binary_checked checked
            rw [equal]
            split at children
            · obtain ⟨leftAfter,leftChecked,rest⟩ := bind_checked children
              obtain ⟨rightAfter,_,rest⟩ := bind_checked rest
              have same := (Except.ok.inj rest).symm
              calc childrenAfter.scopes = leftAfter.scopes := by rw [same]; rfl
                   _ = incoming.scopes := ih.1 _ left _ _ leftChecked
            · exact group_scopes children
        | conditional test yes no =>
            obtain ⟨testAfter,yesAfter,noAfter,testChecked,_,yesChecked,_,_,equal⟩ := conditional_checked checked
            rw [equal]
            exact (ih.1 _ yes _ _ yesChecked).trans (ih.1 _ test _ _ testChecked)
        | tuple values => exact group_scopes checked
        | assign targetForm valueForm =>
            obtain ⟨right,captured,_,rightChecked,_,_,equal⟩ := assign_checked checked
            obtain ⟨raw,child,same⟩ := independent_checked rightChecked
            rw [equal,markTarget_scopes,Context.join_scopes,same]
            exact ih.1 _ valueForm {incoming with orderIndependent := true} raw child
        | compound targetForm valueForm scalarTarget scalarValue =>
            obtain ⟨_,right,captured,rightChecked,_,_,equal⟩ := compound_checked checked
            obtain ⟨raw,child,same⟩ := independent_checked rightChecked
            rw [equal,markTarget_scopes,Context.join_scopes,same]
            exact ih.1 _ valueForm {incoming with orderIndependent := true} raw child
        | update targetForm scalar nondelete =>
            obtain ⟨captured,_,capturedChecked,_,_,equal⟩ := update_checked checked nondelete
            rw [equal,markTarget_scopes]
            exact ih.2 _ targetForm _ _ _ capturedChecked
        | call calleeForm argumentsForm parameters returns =>
            obtain ⟨_,_,childrenAfter,children,_,_,equal⟩ := call_checked checked
            rw [equal]
            exact group_scopes (after := childrenAfter) children
        | namedCall calleeForm argumentsForm parameters returns =>
            obtain ⟨_,_,childrenAfter,_,children,_,_,_,equal⟩ := named_call_checked checked
            rw [equal]
            exact group_scopes (after := childrenAfter) children
        | assert_ source =>
            simp only [checkExpression] at checked
            obtain ⟨childAfter,child,rest⟩ := bind_checked checked
            exact (metadata_scopes _ _ rest).trans (ih.1 _ source _ _ child)
        | require_ source =>
            simp only [checkExpression] at checked
            obtain ⟨_,_,rest⟩ := bind_checked checked
            obtain ⟨childAfter,children,rest⟩ := bind_checked rest
            exact (metadata_scopes _ _ rest).trans (group_scopes children)
        | revertWith =>
            simp only [checkExpression] at checked
            obtain ⟨childAfter,children,rest⟩ := bind_checked checked
            exact (metadata_scopes _ _ rest).trans (group_scopes children)
        | newArray source =>
            obtain ⟨childAfter,child,_,_,equal⟩ := newArray_checked checked
            exact (congrArg Admission.Context.scopes equal).trans (ih.1 _ source _ _ child)
        | length source array =>
            obtain ⟨childAfter,child,_,equal⟩ := length_checked checked
            exact (congrArg Admission.Context.scopes equal).trans (ih.1 _ source _ _ child)
        | index source array indexForm =>
            obtain ⟨childrenAfter,children,_,_,equal⟩ := index_checked checked
            exact (congrArg Admission.Context.scopes equal).trans (group_scopes children)
      · intro target form writable incoming after checked
        cases form with
        | «local» supported =>
            obtain ⟨_,_,equal⟩ := local_target_checked checked
            exact congrArg Admission.Context.scopes equal
        | heap physical =>
            simp only [checkLValue] at checked
            obtain ⟨_,_,rest⟩ := bind_checked checked
            cases writable with
            | false => exact returned_scopes rest
            | true => exact metadata_scopes _ _ rest
        | index source array indexForm =>
            obtain ⟨childrenAfter,children,_,_,equal⟩ := index_target_checked checked
            exact (congrArg Admission.Context.scopes equal).trans (group_scopes children)

theorem checkExpression_scopes (form : Profile.Expression program expression)
    (checked : checkExpression registry fuel incoming expression = .ok after) :
    after.scopes = incoming.scopes := (profile_scopes program registry fuel).1 _ form _ _ checked

theorem checkLValue_scopes (form : Profile.Target program target)
    (checked : checkLValue registry fuel incoming target writable = .ok after) :
    after.scopes = incoming.scopes := (profile_scopes program registry fuel).2 _ form _ _ _ checked

end Solidity.Execution.Safety.SourceTyping
