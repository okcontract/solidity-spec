/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.SourceProgress
import Solidity.Core.Execution.Admission
import Solidity.Core.Execution.MachineProofs

/-! Primitive progress from independent scalar and expression typing permissions. No hypothesis
asserts successful execution of a scalar operation. The profile is the
`scalarSupported` value domain; nominal registry validity and heap/reference
representation belong to the enclosing admitted-state invariant. -/
namespace Solidity.Execution.Safety.ScalarProgress
open Static Core Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def RuntimeResult (expected : SType) (result : Aggregates.Result Value) : Prop :=
  (∃ value, result = .ok value ∧ value.type = expected) ∨
    (∃ failure, result = .error failure ∧ isSourceFailure failure = true)

def UpdateRuntimeResult (expected : SType) (result : Aggregates.Result Effects.ScalarUpdate) : Prop :=
  (∃ changed, result = .ok changed ∧ changed.next.type = expected ∧
    ∀ value ∈ changed.result, value.type = expected) ∨
    (∃ failure, result = .error failure ∧ isSourceFailure failure = true)

theorem failureOfBytes_source (bytes : List UInt8) :
    isSourceFailure (Effects.failureOfBytes bytes) = true := by
  dsimp only [Effects.failureOfBytes]
  split <;> rfl

theorem RuntimeResult.ok (value : Value) : RuntimeResult value.type (.ok value) :=
  .inl ⟨value,rfl,rfl⟩

theorem RuntimeResult.error (expected : SType) (failure : Failure)
    (source : isSourceFailure failure = true) : RuntimeResult expected (.error failure) :=
  .inr ⟨failure,rfl,source⟩

theorem RuntimeResult.excludes_model_failure {expected : SType} {result : Aggregates.Result Value}
    {failure : Failure} (safe : RuntimeResult expected result)
    (model : isSourceFailure failure = false) : result ≠ Except.error failure := by
  rintro rfl
  rcases safe with ⟨value,impossible,_⟩ | ⟨actual,same,source⟩
  · cases impossible
  · cases same
    simp [model] at source

def pack (type : SType) (result : Aggregates.Result type.Value) : Aggregates.Result Value := do
  return ⟨type, ← result⟩

theorem core_progress (type : SType) (result : Core.Result type.Value) :
    RuntimeResult type (pack type (Effects.liftCore result)) := by
  cases result with
  | ok value => exact .inl ⟨⟨type,value⟩,rfl,rfl⟩
  | error bytes => exact .inr ⟨Effects.failureOfBytes bytes,rfl,failureOfBytes_source bytes⟩

theorem conversion_progress (type : SType) (result : Except ConversionFailure type.Value)
    (safe : Static.RuntimeResult result) :
    RuntimeResult type (pack type (Effects.liftConversion result)) := by
  cases result with
  | ok value => exact .inl ⟨⟨type,value⟩,rfl,rfl⟩
  | error failure =>
      cases failure with
      | rejected => exact False.elim (safe.1 rfl)
      | unsupported => exact False.elim (safe.2 rfl)
      | panic bytes => exact .inr ⟨Effects.failureOfBytes bytes,rfl,failureOfBytes_source bytes⟩

theorem cast_progress (mode : ConversionMode) (target : SType) (source : Value)
    (sourceSupported : source.type.scalarSupported = true)
    (targetSupported : target.scalarSupported = true)
    (allowed : Static.Allowed mode source.type target) :
    RuntimeResult target (Effects.scalarCast mode target source) := by
  have permission := (Static.allows_iff _ _ _).mpr allowed
  have safe : Static.RuntimeResult (Static.convert mode source.type target source.value) := by
    simpa [Static.convert,sourceSupported,targetSupported,permission] using
      (Static.RuntimeResult.coerce allowed source.value)
  simpa [Effects.scalarCast,permission,pack] using conversion_progress target _ safe

theorem unary_progress (mode : ArithmeticMode) (code : UnaryCode) (source : Value)
    (operation : ScalarUnary code source.type) :
    RuntimeResult source.type (Effects.unary mode code source) := by
  simpa [Effects.unary,checkUnary_complete operation,Effects.evalUnary,pack] using
    core_progress source.type (operation.eval mode source.value)

theorem unary_checked_progress (mode : ArithmeticMode) (code : UnaryCode) (source : Value)
    (allowed : (checkUnary code source.type).isSome = true) :
    RuntimeResult source.type (Effects.unary mode code source) := by
  obtain ⟨operation⟩ := (checkUnary_iff _ _).mp allowed
  exact unary_progress mode code source operation

theorem common_permissions (selected : Static.Common left right type) :
    Static.Allowed .implicit left type ∧ Static.Allowed .implicit right type := by
  rcases selected with ⟨rightLeft,rfl⟩ | ⟨_,leftRight,rfl⟩
  · exact ⟨Or.inl rfl,rightLeft⟩
  · exact ⟨leftRight,Or.inl rfl⟩

theorem common_supported (selected : Static.Common left right type)
    (leftSupported : left.scalarSupported = true) (rightSupported : right.scalarSupported = true) :
    type.scalarSupported = true := by
  rcases selected with ⟨_,rfl⟩ | ⟨_,_,rfl⟩
  · exact leftSupported
  · exact rightSupported

theorem binary_progress (mode : ArithmeticMode) (code : BinaryCode) (left right : Value)
    (allowed : Admission.BinaryAllowed code left.type right.type result)
    (leftSupported : left.type.scalarSupported = true)
    (rightSupported : right.type.scalarSupported = true) :
    RuntimeResult result (Effects.binary mode code left right) := by
  cases allowed with
  | asymmetric order operation =>
      simpa [Effects.binary,order,checkBinary_complete operation,Effects.evalBinary,pack] using
        core_progress result (operation.eval mode left.value right.value)
  | common order type selected operation =>
      have chosen := (Static.common_iff _ _ _).mpr selected
      have permissions := common_permissions selected
      have supported := common_supported selected leftSupported rightSupported
      rcases cast_progress .implicit type left leftSupported supported permissions.1 with
        ⟨convertedLeft,leftCast,leftType⟩ | ⟨failure,leftCast,source⟩
      · rcases cast_progress .implicit type right rightSupported supported permissions.2 with
          ⟨convertedRight,rightCast,rightType⟩ | ⟨failure,rightCast,source⟩
        · cases convertedLeft with
          | mk leftTypeName leftValue =>
              cases leftType
              cases convertedRight with
              | mk rightTypeName rightValue =>
                  cases rightType
                  simpa [Effects.binary,order,chosen,leftCast,rightCast,
                    checkBinary_complete operation,Effects.evalBinary,pack] using
                    core_progress result (operation.eval mode leftValue rightValue)
        · simpa [Effects.binary,order,chosen,leftCast,rightCast] using
            RuntimeResult.error result failure source
      · simpa [Effects.binary,order,chosen,leftCast] using
          RuntimeResult.error result failure source

theorem binary_checked_progress (mode : ArithmeticMode) (code : BinaryCode) (left right : Value)
    (checked : Admission.scalarBinaryType code left.type right.type = .ok result)
    (leftSupported : left.type.scalarSupported = true)
    (rightSupported : right.type.scalarSupported = true) :
    RuntimeResult result (Effects.binary mode code left right) :=
  binary_progress mode code left right (Admission.scalarBinaryType_sound checked) leftSupported rightSupported

private theorem update_runtime (mode : ArithmeticMode) (code : UpdateCode) (type : SType)
    (old : type.Value) (nondelete : code ≠ .delete) (allowed : Static.UpdateAllowed code type true) :
    Static.RuntimeResult (Static.updateScalar mode code type true old) := by
  cases code with
  | delete => exact False.elim (nondelete rfl)
  | inc post =>
      cases type <;> try {simp [Static.UpdateAllowed] at allowed}
      case uint width =>
        cases changed : unsigned width mode .add old (1#width.bits) <;>
          simp [Static.updateScalar,SType.scalarSupported,Static.updateAllowed,changed,Static.RuntimeResult] <;>
          constructor <;> intro impossible <;> cases impossible
      case sint width =>
        cases changed : signed width mode .add old (1#width.bits) <;>
          simp [Static.updateScalar,SType.scalarSupported,Static.updateAllowed,changed,Static.RuntimeResult] <;>
          constructor <;> intro impossible <;> cases impossible
  | dec post =>
      cases type <;> try {simp [Static.UpdateAllowed] at allowed}
      case uint width =>
        cases changed : unsigned width mode .sub old (1#width.bits) <;>
          simp [Static.updateScalar,SType.scalarSupported,Static.updateAllowed,changed,Static.RuntimeResult] <;>
          constructor <;> intro impossible <;> cases impossible
      case sint width =>
        cases changed : signed width mode .sub old (1#width.bits) <;>
          simp [Static.updateScalar,SType.scalarSupported,Static.updateAllowed,changed,Static.RuntimeResult] <;>
          constructor <;> intro impossible <;> cases impossible

private def packUpdated (type : SType) (changed : Static.Updated type) : Effects.ScalarUpdate :=
  ⟨⟨type,changed.next⟩,changed.result.map fun value => ⟨type,value⟩⟩

private theorem update_conversion_progress (type : SType)
    (result : Except ConversionFailure (Static.Updated type)) (safe : Static.RuntimeResult result) :
    UpdateRuntimeResult type ((Effects.liftConversion result).map (packUpdated type)) := by
  cases result with
  | ok changed =>
      left
      refine ⟨packUpdated type changed,rfl,rfl,?_⟩
      intro value inside
      change value ∈ changed.result.map (fun value => (⟨type,value⟩ : Value)) at inside
      simp only [Option.mem_def,Option.map_eq_some_iff] at inside
      rcases inside with ⟨old,_,rfl⟩
      rfl
  | error failure =>
      cases failure with
      | rejected => exact False.elim (safe.1 rfl)
      | unsupported => exact False.elim (safe.2 rfl)
      | panic bytes => exact .inr ⟨Effects.failureOfBytes bytes,rfl,failureOfBytes_source bytes⟩

theorem update_progress (mode : ArithmeticMode) (code : UpdateCode) (source : Value)
    (nondelete : code ≠ .delete) (allowed : Static.UpdateAllowed code source.type true) :
    UpdateRuntimeResult source.type (Effects.scalarUpdate mode code source) := by
  have safe := update_runtime mode code source.type source.value nondelete allowed
  have result := update_conversion_progress source.type _ safe
  cases code <;> simp_all [Effects.scalarUpdate,packUpdated,Except.map]

/-- A handle is closed by actual lookup and signature agreement; absence is a
well-typed null function, not evidence of an available body. -/
def ClosedHandle (program : Program Key) (signature : FunctionSignature) (handle : Option Nat) : Prop :=
  ∀ identity, handle = some identity → ∃ definition,
    program.lookup identity = .ok definition ∧ definition.signature.accepts signature = true

def ClosedFunction (program : Program Key) : Value → Prop
  | ⟨.function .internal mutability parameters returns,handle⟩ =>
      ClosedHandle program ⟨mutability,parameters,returns⟩ handle
  | _ => True

theorem mutability_trans (first : Mutability.Allows a b) (second : Mutability.Allows b c) :
    Mutability.Allows a c := by
  cases a <;> cases b <;> cases c <;> simp_all [Mutability.Allows]

theorem accepts_trans {actual middle expected : FunctionSignature}
    (first : actual.accepts middle = true) (second : middle.accepts expected = true) :
    actual.accepts expected = true := by
  obtain ⟨firstParameters,firstReturns,firstMutability⟩ := (FunctionSignature.accepts_iff _ _).mp first
  obtain ⟨secondParameters,secondReturns,secondMutability⟩ := (FunctionSignature.accepts_iff _ _).mp second
  exact (FunctionSignature.accepts_iff _ _).mpr
    ⟨firstParameters.trans secondParameters,firstReturns.trans secondReturns,
      mutability_trans firstMutability secondMutability⟩

theorem closedHandle_transport (closed : ClosedHandle program actual handle)
    (permitted : actual.accepts expected = true) : ClosedHandle program expected handle := by
  intro identity present
  obtain ⟨definition,lookup,accepted⟩ := closed identity present
  exact ⟨definition,lookup,accepts_trans accepted permitted⟩

theorem function_allowed_accepts (actual expected : FunctionSignature)
    (allowed : Static.Allowed .implicit actual.type expected.type) :
    actual.accepts expected = true := by
  apply (FunctionSignature.accepts_iff _ _).mpr
  cases actual with
  | mk actualMutability actualParameters actualReturns =>
      cases expected with
      | mk expectedMutability expectedParameters expectedReturns =>
          simp only [Static.Allowed,Static.Implicit,FunctionSignature.type] at allowed
          rcases allowed with same | ⟨_,parameters,returns,mutability⟩
          · cases same
            exact ⟨rfl,rfl,Or.inl rfl⟩
          · exact ⟨parameters,returns,mutability⟩

theorem function_cast_closed (closed : ClosedHandle program actual handle)
    (permitted : actual.accepts expected = true) :
    Effects.scalarCast .implicit expected.type ⟨actual.type,handle⟩ = .ok ⟨expected.type,handle⟩ ∧
      ClosedFunction program ⟨expected.type,handle⟩ :=
  ⟨Machine.callee_conversion actual expected handle permitted,closedHandle_transport closed permitted⟩

theorem function_implicit_closed {actual expected : FunctionSignature}
    (closed : ClosedHandle program actual handle)
    (allowed : Static.Allowed .implicit actual.type expected.type) :
    Effects.scalarCast .implicit expected.type ⟨actual.type,handle⟩ = .ok ⟨expected.type,handle⟩ ∧
      ClosedFunction program ⟨expected.type,handle⟩ :=
  function_cast_closed closed (function_allowed_accepts actual expected allowed)

theorem null_closed (program : Program Key) (signature : FunctionSignature) :
    ClosedHandle program signature none := by
  intro identity impossible
  cases impossible

/-- Parameter conversions retain their own outcomes before the null dispatch
panic. This equation has no successful-parameter-conversion premise. -/
theorem null_invoke (backend : Backend σ Key) (registry : Registry) (limits : Limits) (program : Program Key)
    (config : Config σ Key) (signature : FunctionSignature) (arguments : Packet) :
    Machine.invoke backend registry limits program config signature ⟨signature.type,none⟩ arguments =
      (Machine.prepareArguments registry limits config.state (typesList signature.parameters) arguments >>=
        fun _ => .error (.panic 0x51)) := by
  have reflexive : signature.accepts signature = true :=
    (FunctionSignature.accepts_iff _ _).mpr ⟨rfl,rfl,Or.inl rfl⟩
  have conversion := Machine.callee_conversion signature signature none reflexive
  unfold Machine.invoke
  rw [conversion]
  cases signature
  simp [FunctionSignature.type]
  rfl

theorem null_no_arguments (backend : Backend σ Key) (registry : Registry) (limits : Limits) (program : Program Key)
    (config : Config σ Key) (mutability : Mutability) (returns : Types) :
    Machine.invoke backend registry limits program config ⟨mutability,.nil,returns⟩
      ⟨.function .internal mutability .nil returns,none⟩ [] = .error (.panic 0x51) := by
  simpa [FunctionSignature.type,Machine.prepareArguments,typesList] using
    null_invoke backend registry limits program config ⟨mutability,.nil,returns⟩ []

end Solidity.Execution.Safety.ScalarProgress
