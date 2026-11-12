/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.ScalarProgress

namespace Solidity.Execution.Safety.ScalarProgress.Tests
open Static Core Aggregates ScalarProgress

example (value : BitVec 256) : RuntimeResult (.uint 31)
    (Effects.scalarCast .implicit (.uint 31) ⟨.uint 31,value⟩) :=
  cast_progress _ _ _ rfl rfl (Or.inl rfl)

example (value : Bool) : RuntimeResult .bool (Effects.unary .checked .not ⟨.bool,value⟩) :=
  unary_progress _ _ _ .not

example (left : BitVec 8) (right : BitVec 16) : RuntimeResult (.uint 1)
    (Effects.binary .checked (.arithmetic .add) ⟨.uint 0,left⟩ ⟨.uint 1,right⟩) := by
  apply binary_progress
  · apply Admission.BinaryAllowed.common rfl (.uint 1) _ .uintArithmetic
    exact Or.inr ⟨by change ¬Implicit (.uint 1) (.uint 0); simp [Static.Implicit],
      by change Implicit (.uint 0) (.uint 1); simp [Static.Implicit],rfl⟩
  · rfl
  · rfl

private def panicCode : Aggregates.Result α → Option UInt8
  | .error (.panic code) => some code
  | _ => none

example : panicCode (Effects.unary .checked .neg ⟨.sint 0,128#8⟩) = some 0x11 := by
  decide +kernel

example : panicCode (Effects.scalarCast (.explicit .ordinary) (.enumType 0 1) ⟨.uint 0,2#8⟩) =
    some 0x21 := by decide +kernel

example (value : BitVec 256) : UpdateRuntimeResult (.uint 31)
    (Effects.scalarUpdate .checked (.inc true) ⟨.uint 31,value⟩) :=
  update_progress _ _ _ (by decide) ⟨rfl,True.intro⟩

example : panicCode (Effects.scalarUpdate .checked (.inc false) ⟨.uint 0,255#8⟩) = some 0x11 := by
  decide +kernel

example : (checkUnary .neg (.uint 31)).isSome = false := rfl
example : (checkBinary (.arithmetic .add) .bool .bool) = none := rfl
example : SType.scalarSupported (.array (.uint 31) none .memory true) = false := rfl
example : SType.scalarSupported (.fixedPoint false 31 1) = false := rfl

private def pureSignature : FunctionSignature := ⟨.pure,.nil,.cons (.uint 31) .nil⟩
private def viewSignature : FunctionSignature := ⟨.view,.nil,.cons (.uint 31) .nil⟩
private def nonpayableSignature : FunctionSignature := ⟨.nonpayable,.nil,.cons (.uint 31) .nil⟩
private def definition : FunctionDefinition EmptyKey := {
  mutability := .pure,parameters := [],returns := [⟨0,.uint 31,none⟩],
  body := .return_ (some (.literal ⟨.uint 31,7#256⟩)) }
private def program : Program EmptyKey := ⟨[(7,definition)]⟩
private theorem closed : ClosedHandle program pureSignature (some 7) := by
  intro identity same
  cases Option.some.inj same
  exact ⟨definition,rfl,rfl⟩

example : ClosedHandle program nonpayableSignature (some 7) :=
  closedHandle_transport (closedHandle_transport (expected := viewSignature) closed rfl) rfl

example : Effects.scalarCast .implicit viewSignature.type ⟨pureSignature.type,some 7⟩ =
      .ok ⟨viewSignature.type,some 7⟩ ∧ ClosedFunction program ⟨viewSignature.type,some 7⟩ :=
  function_implicit_closed closed (by
    simp [Static.Allowed,Static.Implicit,pureSignature,viewSignature,FunctionSignature.type,Mutability.Allows])

example : ClosedHandle program viewSignature none := null_closed _ _

example : ¬ClosedHandle program pureSignature (some 8) := by
  intro impossible
  obtain ⟨definition,lookup,_⟩ := impossible 8 rfl
  cases lookup

example (registry : Registry) (config : Config Unit EmptyKey) :
    Machine.invoke physicalBackend registry {} program config pureSignature ⟨pureSignature.type,none⟩ [] =
      .error (.panic 0x51) := by
  exact null_no_arguments _ _ _ _ _ _ _

end Solidity.Execution.Safety.ScalarProgress.Tests
