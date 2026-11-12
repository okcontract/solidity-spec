/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.TypedState

/-! Scalar primitive progress with physical value representation. Internal
function results retain concrete table lookup; other scalar results need no
heap packet. No public progress theorem assumes operation success. -/
namespace Solidity.Execution.Safety.ScalarRepresentation
open Static Core Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def RuntimeValueResult (program : Program Key) (heap : Heap) (objects : List WordArena.Object)
    (expected : SType) (result : Aggregates.Result Value) : Prop :=
  (∃ value, result = .ok value ∧ value.type = expected ∧ ValueRep program heap objects value) ∨
    (∃ failure, result = .error failure ∧ isSourceFailure failure = true)

def RuntimeUpdateValueResult (program : Program Key) (heap : Heap) (objects : List WordArena.Object)
    (expected : SType) (result : Aggregates.Result Effects.ScalarUpdate) : Prop :=
  (∃ changed returned, result = .ok changed ∧ changed.next.type = expected ∧
    ValueRep program heap objects changed.next ∧ changed.result = some returned ∧
    returned.type = expected ∧ ValueRep program heap objects returned) ∨
    (∃ failure, result = .error failure ∧ isSourceFailure failure = true)

def NonInternal : SType → Prop
  | .function .internal _ _ _ => False
  | _ => True

theorem closed_value (represented : ValueRep program heap objects value) :
    ScalarProgress.ClosedFunction program value := by
  cases represented with
  | scalar _ closed => exact closed
  | array => trivial
  | emptyArray => trivial

theorem closed_noninternal (typed : value.type = type) (noninternal : NonInternal type) :
    ScalarProgress.ClosedFunction program value := by
  cases value with
  | mk actual data =>
      cases typed
      cases actual <;> try trivial
      case function visibility mutability parameters returns =>
        cases visibility <;> simp_all [NonInternal,ScalarProgress.ClosedFunction]

private theorem lift_noninternal (progress : ScalarProgress.RuntimeResult expected result)
    (supported : expected.scalarSupported = true) (noninternal : NonInternal expected) :
    RuntimeValueResult program heap objects expected result := by
  rcases progress with ⟨value,completed,typed⟩ | failed
  · exact .inl ⟨value,completed,typed,.scalar (by rw [typed]; exact supported)
      (closed_noninternal typed noninternal)⟩
  · exact .inr failed

private theorem cast_internal (mode : ConversionMode) (expected : FunctionSignature) (source : Value)
    (represented : ValueRep program heap objects source)
    (allowed : Static.Allowed mode source.type expected.type) :
    RuntimeValueResult program heap objects expected.type (Effects.scalarCast mode expected.type source) := by
  cases mode with
  | explicit kind =>
      cases kind <;> simp [Static.Allowed,Static.SourceCast,Static.CastTarget,FunctionSignature.type] at allowed
  | implicit =>
      cases source with
      | mk sourceType data =>
          cases sourceType with
          | function visibility mutability parameters returns =>
              cases visibility with
              | external => simp [Static.Allowed,Static.Implicit,FunctionSignature.type] at allowed
              | internal =>
                  have closed := ScalarProgress.function_implicit_closed
                    (actual := ⟨mutability,parameters,returns⟩) (expected := expected)
                    (closed_value represented) allowed
                  exact .inl ⟨⟨expected.type,data⟩,closed.1,rfl,.scalar rfl closed.2⟩
          | _ => simp [Static.Allowed,Static.Implicit,FunctionSignature.type] at allowed

theorem cast_progress (mode : ConversionMode) (target : SType) (source : Value)
    (represented : ValueRep program heap objects source)
    (sourceSupported : source.type.scalarSupported = true) (targetSupported : target.scalarSupported = true)
    (allowed : Static.Allowed mode source.type target) :
    RuntimeValueResult program heap objects target (Effects.scalarCast mode target source) := by
  cases target with
  | function visibility mutability parameters returns =>
      cases visibility with
      | internal => exact cast_internal mode ⟨mutability,parameters,returns⟩ source represented allowed
      | external =>
          exact lift_noninternal
            (ScalarProgress.cast_progress mode _ source sourceSupported targetSupported allowed) targetSupported trivial
  | _ =>
      exact lift_noninternal
        (ScalarProgress.cast_progress mode _ source sourceSupported targetSupported allowed) targetSupported trivial

private theorem unary_properties (operation : ScalarUnary code type) :
    type.scalarSupported = true ∧ NonInternal type := by
  cases operation <;> exact ⟨rfl,True.intro⟩

private theorem binary_properties (operation : ScalarBinary code left right result) :
    result.scalarSupported = true ∧ NonInternal result := by
  cases operation <;> exact ⟨rfl,True.intro⟩

theorem unary_progress (mode : ArithmeticMode) (code : UnaryCode) (source : Value)
    (operation : ScalarUnary code source.type) :
    RuntimeValueResult program heap objects source.type (Effects.unary mode code source) := by
  have properties := unary_properties operation
  exact lift_noninternal (ScalarProgress.unary_progress mode code source operation) properties.1 properties.2

theorem unary_checked_progress (mode : ArithmeticMode) (code : UnaryCode) (source : Value)
    (allowed : (checkUnary code source.type).isSome = true) :
    RuntimeValueResult program heap objects source.type (Effects.unary mode code source) := by
  obtain ⟨operation⟩ := (checkUnary_iff _ _).mp allowed
  exact unary_progress mode code source operation

theorem binary_progress (mode : ArithmeticMode) (code : BinaryCode) (left right : Value)
    (allowed : Admission.BinaryAllowed code left.type right.type expected)
    (leftSupported : left.type.scalarSupported = true) (rightSupported : right.type.scalarSupported = true) :
    RuntimeValueResult program heap objects expected (Effects.binary mode code left right) := by
  have properties : expected.scalarSupported = true ∧ NonInternal expected := by
    cases allowed with
    | asymmetric _ operation => exact binary_properties operation
    | common _ _ _ operation => exact binary_properties operation
  exact lift_noninternal (ScalarProgress.binary_progress mode code left right allowed leftSupported rightSupported)
    properties.1 properties.2

private theorem uint_update_presence (width : Width) (mode : ArithmeticMode) (code : UpdateCode)
    (old : BitVec width.bits) (nondelete : code ≠ .delete)
    (completed : Effects.scalarUpdate mode code ⟨.uint width,old⟩ = .ok changed) :
    ∃ returned, changed.result = some returned := by
  cases code with
  | delete => exact False.elim (nondelete rfl)
  | inc post =>
      cases computed : unsigned width mode .add old (1#width.bits) <;>
        simp [Effects.scalarUpdate,Static.updateScalar,SType.scalarSupported,Static.updateAllowed,
          computed,Effects.liftConversion] at completed
      cases completed
      exact ⟨_,rfl⟩
  | dec post =>
      cases computed : unsigned width mode .sub old (1#width.bits) <;>
        simp [Effects.scalarUpdate,Static.updateScalar,SType.scalarSupported,Static.updateAllowed,
          computed,Effects.liftConversion] at completed
      cases completed
      exact ⟨_,rfl⟩

private theorem sint_update_presence (width : Width) (mode : ArithmeticMode) (code : UpdateCode)
    (old : BitVec width.bits) (nondelete : code ≠ .delete)
    (completed : Effects.scalarUpdate mode code ⟨.sint width,old⟩ = .ok changed) :
    ∃ returned, changed.result = some returned := by
  cases code with
  | delete => exact False.elim (nondelete rfl)
  | inc post =>
      cases computed : signed width mode .add old (1#width.bits) <;>
        simp [Effects.scalarUpdate,Static.updateScalar,SType.scalarSupported,Static.updateAllowed,
          computed,Effects.liftConversion] at completed
      cases completed
      exact ⟨_,rfl⟩
  | dec post =>
      cases computed : signed width mode .sub old (1#width.bits) <;>
        simp [Effects.scalarUpdate,Static.updateScalar,SType.scalarSupported,Static.updateAllowed,
          computed,Effects.liftConversion] at completed
      cases completed
      exact ⟨_,rfl⟩

theorem update_presence (mode : ArithmeticMode) (code : UpdateCode) (source : Value)
    (nondelete : code ≠ .delete) (allowed : Static.UpdateAllowed code source.type true)
    (completed : Effects.scalarUpdate mode code source = .ok changed) :
    ∃ returned, changed.result = some returned := by
  cases source with
  | mk type old =>
      cases code
      case delete => exact False.elim (nondelete rfl)
      all_goals
        cases type <;> try {simp [Static.UpdateAllowed] at allowed}
        case uint width => exact uint_update_presence width mode _ old nondelete completed
        case sint width => exact sint_update_presence width mode _ old nondelete completed

theorem update_progress (mode : ArithmeticMode) (code : UpdateCode) (source : Value)
    (nondelete : code ≠ .delete) (allowed : Static.UpdateAllowed code source.type true) :
    RuntimeUpdateValueResult program heap objects source.type (Effects.scalarUpdate mode code source) := by
  have support : source.type.scalarSupported = true := by
    cases code <;> cases type : source.type <;> simp_all [Static.UpdateAllowed,SType.scalarSupported]
  have shape : NonInternal source.type := by
    cases code <;> cases type : source.type <;> simp_all [Static.UpdateAllowed,NonInternal]
  rcases ScalarProgress.update_progress mode code source nondelete allowed with
    ⟨changed,completed,nextType,resultTypes⟩ | failed
  · obtain ⟨returned,present⟩ := update_presence mode code source nondelete allowed completed
    have returnedType := resultTypes returned (by simp [present])
    exact .inl ⟨changed,returned,completed,nextType,
      .scalar (by rw [nextType]; exact support) (closed_noninternal nextType shape),
      present,returnedType,.scalar (by rw [returnedType]; exact support) (closed_noninternal returnedType shape)⟩
  · exact .inr failed

end Solidity.Execution.Safety.ScalarRepresentation
