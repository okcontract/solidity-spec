/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Profile

/-! Extract independent operation permissions and actual child-check equations
from admission. These lemmas do not run another checker and do not assume that
the corresponding runtime operation succeeds. -/
namespace Solidity.Execution.Safety.SourceTyping
open Static Aggregates Admission
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem bind_checked {first : Aggregates.Result α} {next : α → Aggregates.Result β}
    (checked : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value,rfl,checked⟩

theorem ensure_checked (checked : Admission.ensure condition = .ok ()) : condition = true := by
  cases condition <;> simp_all [Admission.ensure]

private theorem ensure_bind_checked (checked : (Admission.ensure condition >>= fun _ => next) = .ok result) :
    condition = true ∧ next = .ok result := by
  obtain ⟨value,permission,rest⟩ := bind_checked checked
  cases value
  exact ⟨ensure_checked permission,rest⟩

theorem transfer_checked (checked : Admission.transfer registry fuel localBinding source target = .ok ()) :
    ∃ kind, TransferRule localBinding source target kind := by
  unfold Admission.transfer at checked
  obtain ⟨kind,planned,_⟩ := bind_checked checked
  exact ⟨kind,planTransfer_rule planned⟩

private theorem forM_checked (items : List α) (action : α → Aggregates.Result Unit)
    (checked : items.forM action = .ok ()) (member : value ∈ items) : action value = .ok () := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      obtain ⟨done,first,rest⟩ := bind_checked checked
      cases done
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · exact ih rest member

theorem transfers_checked {pairs : List (Expr Key × SType)}
    (checked : pairs.forM (fun pair : Expr Key × SType => transfer registry fuel true pair.1.type pair.2) = .ok ())
    (member : (expression,type) ∈ pairs) : ∃ kind, TransferRule true expression.type type kind :=
  transfer_checked (forM_checked pairs _ checked member)

private theorem type_result_checked (action : Aggregates.Result SType) (context : Admission.Context)
    (checked : (do ensure ((← action) == expected); pure context) = .ok after) :
    action = .ok expected ∧ after = context := by
  cases action with
  | error failure => cases checked
  | ok actual =>
      cases compared : actual == expected with
      | false => simp [ensure,compared] at checked
      | true =>
          have same : actual = expected := by simpa using compared
          have returned : context = after := by simpa [ensure,compared] using checked
          exact ⟨congrArg Except.ok same,returned.symm⟩

theorem children_checked (checked : checkExpressions registry fuel incoming expressions = .ok after)
    (member : expression ∈ expressions) :
    ∃ childFuel childAfter,
      checkExpression registry childFuel {incoming with orderIndependent := true} expression = .ok childAfter := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      obtain ⟨childAfter,child⟩ := checkExpressions_each checked member
      exact ⟨fuel,childAfter,child⟩

theorem group_scopes (checked : checkExpressions registry fuel incoming expressions = .ok after) :
    after.scopes = incoming.scopes := by
  cases fuel with
  | zero => cases checked
  | succ fuel => exact independentChildren_scopes checked

theorem scalar_shape {type : SType} (supported : type.scalarSupported = true) :
    referenceLocation type = none ∧ tupleComponents type = none ∧ isReference type = false := by
  cases type <;> simp_all [SType.scalarSupported,referenceLocation,tupleComponents,isReference]

theorem scalar_transfer_permission (permission : TransferRule localBinding source target kind)
    (supported : source.scalarSupported = true) : Static.Allowed .implicit source target := by
  have sourceScalar := (scalar_shape supported).1
  cases kind <;> simp_all [TransferRule,Static.Allowed]

theorem scalar_group_permission (permission : GroupTransferAllowed source target)
    (supported : source.scalarSupported = true) : Static.Allowed .implicit source target := by
  cases permission with
  | leaf _ _ permission => exact scalar_transfer_permission permission supported
  | tuple sourceGroup _ _ => simp [(scalar_shape supported).2.1] at sourceGroup

theorem cast_implicit_checked
    (checked : checkExpression registry (fuel+1) incoming (.cast .implicit target value) = .ok after) :
    ∃ childAfter, checkExpression registry fuel incoming value = .ok childAfter ∧
      GroupTransferAllowed value.type target ∧ after = childAfter := by
  simp only [checkExpression] at checked
  obtain ⟨childAfter,child,rest⟩ := bind_checked checked
  obtain ⟨done,transferred,rest⟩ := bind_checked rest
  cases done
  exact ⟨childAfter,child,groupTransfer_sound transferred,(Except.ok.inj rest).symm⟩

theorem unary_checked
    (checked : checkExpression registry (fuel+1) incoming (.unary code value) = .ok after) :
    ∃ childAfter, checkExpression registry fuel incoming value = .ok childAfter ∧
      (checkUnary code value.type).isSome = true ∧ after = childAfter := by
  simp only [checkExpression] at checked
  obtain ⟨childAfter,child,rest⟩ := bind_checked checked
  cases fixed : fixedPoint value.type with
  | true => cases code <;> simp [fixed] at rest
  | false =>
      simp only [fixed,Bool.false_eq_true,↓reduceIte] at rest
      obtain ⟨permission,rest⟩ := ensure_bind_checked rest
      exact ⟨childAfter,child,permission,(Except.ok.inj rest).symm⟩

theorem binary_checked
    (checked : checkExpression registry (fuel+1) incoming (.binary code result left right) = .ok after) :
    Admission.BinaryAllowed code left.type right.type result ∧
      ∃ childrenAfter,
        (if code == .and || code == .or then do
          let leftAfter ← checkExpression registry fuel incoming left
          let rightAfter ← checkExpression registry fuel leftAfter right
          pure (leftAfter.meet rightAfter)
        else checkExpressions registry fuel incoming [left,right]) = .ok childrenAfter ∧
          after = childrenAfter := by
  simp only [checkExpression] at checked
  cases lazy : code == .and || code == .or with
  | false =>
      simp only [lazy,Bool.false_eq_true,↓reduceIte] at checked
      obtain ⟨childrenAfter,children,rest⟩ := bind_checked checked
      obtain ⟨operator,equal⟩ := type_result_checked _ _ rest
      refine ⟨scalarBinaryType_sound operator,childrenAfter,?_,equal⟩
      simpa [lazy] using children
  | true =>
      simp only [lazy,↓reduceIte] at checked
      obtain ⟨leftAfter,leftChecked,rest⟩ := bind_checked checked
      obtain ⟨rightAfter,rightChecked,rest⟩ := bind_checked rest
      obtain ⟨operator,equal⟩ := type_result_checked _ _ rest
      refine ⟨scalarBinaryType_sound operator,leftAfter.meet rightAfter,?_,equal⟩
      simp [leftChecked,rightChecked]

theorem binary_eager_children
    (checked : checkExpression registry (fuel+1) incoming (.binary code result left right) = .ok after)
    (eager : (code != .and && code != .or) = true) (member : expression ∈ [left,right]) :
    ∃ childFuel childAfter,
      checkExpression registry childFuel {incoming with orderIndependent := true} expression = .ok childAfter := by
  obtain ⟨_,childrenAfter,children,_⟩ := binary_checked checked
  have lazyFalse : (code == .and || code == .or) = false := by simpa using eager
  simp only [lazyFalse,Bool.false_eq_true,↓reduceIte] at children
  exact children_checked children member

theorem assign_checked
    (checked : checkExpression registry (fuel+1) incoming (.assign target value) = .ok after) :
    ∃ right captured kind,
      independent incoming (fun context => checkExpression registry fuel context value) = .ok right ∧
      independent incoming (fun context => checkLValue registry fuel context target true) = .ok captured ∧
      TransferRule (localTarget target) value.type target.type kind ∧
      after = markTarget (right.join captured) target := by
  simp only [checkExpression] at checked
  obtain ⟨right,rightChecked,rest⟩ := bind_checked checked
  obtain ⟨captured,capturedChecked,rest⟩ := bind_checked rest
  obtain ⟨done,transfer,rest⟩ := bind_checked rest
  cases done
  obtain ⟨kind,permission⟩ := transfer_checked transfer
  exact ⟨right,captured,kind,rightChecked,capturedChecked,permission,(Except.ok.inj rest).symm⟩

theorem length_checked
    (checked : checkExpression registry (fuel+1) incoming (.length value) = .ok after) :
    ∃ childAfter, checkExpression registry fuel incoming value = .ok childAfter ∧
      (match value.type with | .array _ _ _ _ | .bytes _ _ | .fixedBytes _ => True | _ => False) ∧
      after = childAfter := by
  simp only [checkExpression] at checked
  obtain ⟨childAfter,child,rest⟩ := bind_checked checked
  obtain ⟨permission,rest⟩ := ensure_bind_checked rest
  refine ⟨childAfter,child,?_,(Except.ok.inj rest).symm⟩
  cases typeEq : value.type <;> simp_all

theorem index_checked
    (checked : checkExpression registry (fuel+1) incoming (.index result value index) = .ok after) :
    ∃ childrenAfter, checkExpressions registry fuel incoming [value,index] = .ok childrenAfter ∧
      unsignedIndex index.type = true ∧ indexType value.type false = .ok result ∧ after = childrenAfter := by
  simp only [checkExpression] at checked
  obtain ⟨childrenAfter,children,rest⟩ := bind_checked checked
  obtain ⟨unsigned,rest⟩ := ensure_bind_checked rest
  obtain ⟨indexed,equal⟩ := type_result_checked _ _ rest
  exact ⟨childrenAfter,children,unsigned,indexed,equal⟩

theorem newArray_checked
    (checked : checkExpression registry (fuel+1) incoming (.newArray element count) = .ok after) :
    ∃ childAfter, checkExpression registry fuel incoming count = .ok childAfter ∧
      unsignedIndex count.type = true ∧
      checkType registry fuel (.array (atLocation element .memory false) none .memory true) = .ok () ∧
      after = childAfter := by
  simp only [checkExpression] at checked
  obtain ⟨childAfter,child,rest⟩ := bind_checked checked
  obtain ⟨unsigned,rest⟩ := ensure_bind_checked rest
  obtain ⟨done,typeChecked,rest⟩ := bind_checked rest
  cases done
  exact ⟨childAfter,child,unsigned,typeChecked,(Except.ok.inj rest).symm⟩

theorem call_checked
    (checked : checkExpression registry (fuel+1) incoming (.call signature callee arguments) = .ok after) :
    checkSignature registry fuel signature = .ok () ∧ Static.Implicit callee.type signature.type ∧
      ∃ childrenAfter, checkExpressions registry fuel incoming (callee :: arguments) = .ok childrenAfter ∧
        arguments.length = (typesList signature.parameters).length ∧
        (∀ argument type, (argument,type) ∈ arguments.zip (typesList signature.parameters) →
          ∃ kind, TransferRule true argument.type type kind) ∧
        after = {childrenAfter with unresolvedCalls := true} := by
  simp only [checkExpression] at checked
  obtain ⟨done,signatureChecked,rest⟩ := bind_checked checked
  cases done
  obtain ⟨implicit,rest⟩ := ensure_bind_checked rest
  obtain ⟨childrenAfter,children,rest⟩ := bind_checked rest
  obtain ⟨arity,rest⟩ := ensure_bind_checked rest
  obtain ⟨done,transfers,rest⟩ := bind_checked rest
  cases done
  cases rest
  refine ⟨signatureChecked,(Static.implicit_iff _ _).mp implicit,childrenAfter,children,?_,?_,rfl⟩
  · simpa using arity
  · intro argument type member
    exact transfers_checked transfers member

theorem call_children
    (checked : checkExpression registry (fuel+1) incoming (.call signature callee arguments) = .ok after)
    (member : expression ∈ callee :: arguments) :
    ∃ childFuel childAfter,
      checkExpression registry childFuel {incoming with orderIndependent := true} expression = .ok childAfter := by
  obtain ⟨_,_,childrenAfter,children,_,_,_⟩ := call_checked checked
  exact children_checked children member

theorem scalar_cast_checked
    (checked : checkExpression registry (fuel+1) incoming (.cast mode target value) = .ok after)
    (supported : value.type.scalarSupported = true) :
    ∃ childAfter, checkExpression registry fuel incoming value = .ok childAfter ∧
      Static.Allowed mode value.type target ∧ after = childAfter := by
  cases mode with
  | implicit =>
      obtain ⟨childAfter,child,permission,equal⟩ := cast_implicit_checked checked
      exact ⟨childAfter,child,scalar_group_permission permission supported,equal⟩
  | explicit kind =>
      simp only [checkExpression] at checked
      obtain ⟨childAfter,child,rest⟩ := bind_checked checked
      cases kind with
      | ordinary =>
          obtain ⟨_,rest⟩ := ensure_bind_checked rest
          obtain ⟨done,_,rest⟩ := bind_checked rest
          cases done
          simp only [(scalar_shape supported).2.2,Bool.false_eq_true,↓reduceIte] at rest
          obtain ⟨permission,rest⟩ := ensure_bind_checked rest
          exact ⟨childAfter,child,(Static.allows_iff _ _ _).mp permission,(Except.ok.inj rest).symm⟩
      | payable =>
          obtain ⟨_,rest⟩ := ensure_bind_checked rest
          obtain ⟨done,_,rest⟩ := bind_checked rest
          cases done
          obtain ⟨permission,rest⟩ := ensure_bind_checked rest
          exact ⟨childAfter,child,(Static.allows_iff _ _ _).mp permission,(Except.ok.inj rest).symm⟩

theorem conditional_checked
    (checked : checkExpression registry (fuel+1) incoming (.conditional test yes no) = .ok after) :
    ∃ testAfter yesAfter noAfter,
      checkExpression registry fuel incoming test = .ok testAfter ∧ test.type = .bool ∧
      checkExpression registry fuel testAfter yes = .ok yesAfter ∧
      checkExpression registry fuel testAfter no = .ok noAfter ∧
      yes.type = no.type ∧ after = yesAfter.meet noAfter := by
  simp only [checkExpression] at checked
  obtain ⟨testAfter,testChecked,rest⟩ := bind_checked checked
  obtain ⟨boolean,rest⟩ := ensure_bind_checked rest
  obtain ⟨yesAfter,yesChecked,rest⟩ := bind_checked rest
  obtain ⟨noAfter,noChecked,rest⟩ := bind_checked rest
  obtain ⟨same,rest⟩ := ensure_bind_checked rest
  exact ⟨testAfter,yesAfter,noAfter,testChecked,by simpa using boolean,yesChecked,noChecked,
    by simpa using same,(Except.ok.inj rest).symm⟩

theorem compound_checked
    (checked : checkExpression registry (fuel+1) incoming (.compound code target value) = .ok after) :
    Frontend.Inference.compoundToken code = true ∧
      ∃ right captured,
        independent incoming (fun context => checkExpression registry fuel context value) = .ok right ∧
        independent incoming (fun context => do
          let captured ← checkLValue registry fuel context target true
          checkLValue registry fuel captured target false) = .ok captured ∧
        Admission.BinaryAllowed code target.type value.type target.type ∧
        after = markTarget (right.join captured) target := by
  simp only [checkExpression] at checked
  obtain ⟨token,rest⟩ := ensure_bind_checked checked
  obtain ⟨right,rightChecked,rest⟩ := bind_checked rest
  obtain ⟨captured,capturedChecked,rest⟩ := bind_checked rest
  obtain ⟨operator,equal⟩ := type_result_checked _ _ rest
  exact ⟨token,right,captured,rightChecked,capturedChecked,scalarBinaryType_sound operator,equal⟩

theorem update_checked
    (checked : checkExpression registry (fuel+1) incoming (.update code target) = .ok after)
    (nondelete : code ≠ .delete) :
    ∃ captured readAfter,
      checkLValue registry fuel incoming target true = .ok captured ∧
      checkLValue registry fuel captured target false = .ok readAfter ∧
      Static.UpdateAllowed code target.type true ∧ after = markTarget captured target := by
  cases code
  case delete => exact False.elim (nondelete rfl)
  all_goals
    simp only [checkExpression] at checked
    obtain ⟨captured,capturedChecked,rest⟩ := bind_checked checked
    obtain ⟨readAfter,readChecked,rest⟩ := bind_checked rest
    cases fixed : fixedPoint target.type with
    | true => simp [fixed] at rest
    | false =>
        simp only [fixed,Bool.false_eq_true,↓reduceIte,Bind.bind,Except.bind,Pure.pure,Except.pure] at rest
        obtain ⟨permission,rest⟩ := ensure_bind_checked rest
        exact ⟨captured,readAfter,capturedChecked,readChecked,
          (Static.updateAllowed_iff _ _ _).mp permission,(Except.ok.inj rest).symm⟩

theorem named_call_checked
    (checked : checkExpression registry (fuel+1) incoming (.namedCall signature callee arguments order) = .ok after) :
    checkSignature registry fuel signature = .ok () ∧ Static.Implicit callee.type signature.type ∧
      ∃ childrenAfter ordered,
        checkExpressions registry fuel incoming (callee :: arguments) = .ok childrenAfter ∧
        ArgumentOrder.select order arguments = .ok ordered ∧
        ordered.length = (typesList signature.parameters).length ∧
        (∀ argument type, (argument,type) ∈ ordered.zip (typesList signature.parameters) →
          ∃ kind, TransferRule true argument.type type kind) ∧
        after = {childrenAfter with unresolvedCalls := true} := by
  simp only [checkExpression] at checked
  obtain ⟨done,signatureChecked,rest⟩ := bind_checked checked
  cases done
  obtain ⟨implicit,rest⟩ := ensure_bind_checked rest
  obtain ⟨childrenAfter,children,rest⟩ := bind_checked rest
  obtain ⟨ordered,selected,rest⟩ := bind_checked rest
  obtain ⟨arity,rest⟩ := ensure_bind_checked rest
  obtain ⟨done,transfers,rest⟩ := bind_checked rest
  cases done
  refine ⟨signatureChecked,(Static.implicit_iff _ _).mp implicit,childrenAfter,ordered,children,
    selected,by simpa using arity,?_,(Except.ok.inj rest).symm⟩
  intro argument type member
  exact transfers_checked transfers member

theorem unsigned_type {type : SType} (unsigned : unsignedIndex type = true) :
    ∃ width, type = .uint width := by
  cases type <;> simp_all [unsignedIndex]

theorem local_target_checked {Key : SType → Type} {id : LocalId}
    (checked : checkLValue registry (fuel+1) incoming (.local id type : LValue Key) writable = .ok after) :
    incoming.local id type (!writable) = .ok () ∧ checkType registry fuel type = .ok () ∧ after = incoming := by
  simp only [checkLValue] at checked
  obtain ⟨done,bound,rest⟩ := bind_checked checked
  cases done
  obtain ⟨done,typeChecked,rest⟩ := bind_checked rest
  cases done
  exact ⟨bound,typeChecked,(Except.ok.inj rest).symm⟩

theorem index_target_checked
    (checked : checkLValue registry (fuel+1) incoming (.index result value index) writable = .ok after) :
    ∃ childrenAfter, checkExpressions registry fuel incoming [value,index] = .ok childrenAfter ∧
      unsignedIndex index.type = true ∧ indexType value.type writable = .ok result ∧ after = childrenAfter := by
  simp only [checkLValue] at checked
  obtain ⟨childrenAfter,children,rest⟩ := bind_checked checked
  obtain ⟨unsigned,rest⟩ := ensure_bind_checked rest
  obtain ⟨indexed,equal⟩ := type_result_checked _ _ rest
  exact ⟨childrenAfter,children,unsigned,indexed,equal⟩

theorem field_target_checked
    (checked : checkLValue registry (fuel+1) incoming (.field result value index) writable = .ok after) :
    ∃ childAfter, checkExpression registry fuel incoming value = .ok childAfter ∧
      (writable = true → sourceWritable value.type = true) ∧
      fieldType registry value.type index = .ok result ∧ after = childAfter := by
  simp only [checkLValue] at checked
  obtain ⟨childAfter,child,rest⟩ := bind_checked checked
  cases writable with
  | false =>
      obtain ⟨indexed,equal⟩ := type_result_checked _ _ rest
      exact ⟨childAfter,child,by simp,indexed,equal⟩
  | true =>
      obtain ⟨writable,rest⟩ := ensure_bind_checked rest
      obtain ⟨indexed,equal⟩ := type_result_checked _ _ rest
      exact ⟨childAfter,child,fun _ => writable,indexed,equal⟩

end Solidity.Execution.Safety.SourceTyping
