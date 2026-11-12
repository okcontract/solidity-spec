/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Translations
import Solidity.Core.Execution.Effects
import Solidity.Core.Aggregates.Copy.Laws

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def scalar (type : Core.Ty) (value : type.Value) : Value :=
  ⟨SType.ofCore type, scalarValue type value⟩

theorem ofCore_supported (type : Core.Ty) : (SType.ofCore type).scalarSupported = true := by
  cases type <;> rfl

theorem ofCore_eligible (registry : Registry) (fuel : Nat) (type : Core.Ty) :
    Aggregates.eligibleType registry (fuel+1) (SType.ofCore type) = .ok () := by
  cases type <;> rfl

theorem scalarCast_self (mode : ConversionMode) (type : Core.Ty) (value : type.Value)
    (allowed : Allowed mode (SType.ofCore type) (SType.ofCore type)) :
    Effects.scalarCast mode (SType.ofCore type) (scalar type value) = .ok (scalar type value) := by
  have permission := (allows_iff _ _ _).mpr allowed
  have conversion := convert_identity mode (SType.ofCore type) (scalarValue type value)
    (ofCore_supported type) allowed
  simp [Effects.scalarCast, scalar, permission, conversion, Effects.liftConversion]

theorem scalarCast_implicit_self (type : Core.Ty) (value : type.Value) :
    Effects.scalarCast .implicit (SType.ofCore type) (scalar type value) = .ok (scalar type value) :=
  scalarCast_self _ _ _ (Or.inl rfl)

theorem scalar_bind (registry : Registry) (fuel budget : Nat) (heap : Aggregates.Heap)
    (type : Core.Ty) (value : type.Value) :
    Aggregates.Copy.bind registry (fuel+1) budget heap (SType.ofCore type) (scalar type value) =
      .ok (scalar type value, heap, budget) := by
  apply Aggregates.Copy.bind_scalar
  · simp only [Aggregates.planTransfer, scalar, ofCore_eligible]
    cases type <;> simp [Aggregates.selectTransfer, Aggregates.referenceLocation, Static.implicit] <;> rfl
  · have conversion := convert_identity .implicit (SType.ofCore type) (scalarValue type value)
      (ofCore_supported type) (Or.inl rfl)
    simp [Aggregates.Copy.convertScalar, scalar, conversion]

theorem convert_scalar_self (registry : Registry) (fuel budget : Nat) (heap : Aggregates.Heap)
    (type : Core.Ty) (value : type.Value) :
    Effects.convert registry (fuel+1) budget heap .implicit (SType.ofCore type) (scalar type value) =
      .ok (scalar type value, heap, budget) := scalar_bind registry fuel budget heap type value

theorem read_local (registry : Registry) (fuel : Nat) (heap : Aggregates.Heap)
    (environment : Core.Env types) (var : Core.Var types type) :
    Effects.readCaptured registry (fuel+1) (localEnv environment) heap (.local (localId var) (SType.ofCore type)) =
      .ok (scalar type (environment.get var)) := by
  simp only [Effects.readCaptured, ofCore_eligible, localEnv_read]
  cases type <;> rfl

theorem read_local_given (registry : Registry) (fuel : Nat) (heap : Aggregates.Heap)
    (locals : Locals) (id : LocalId) (type : Core.Ty) (value : type.Value)
    (read : locals.read id (SType.ofCore type) = .ok (scalar type value)) :
    Effects.readCaptured registry (fuel+1) locals heap (.local id (SType.ofCore type)) =
      .ok (scalar type value) := by
  simp only [Effects.readCaptured, ofCore_eligible, read]
  cases type <;> rfl

def binaryCode : Core.Binary a b result → BinaryCode
  | .uintArithmetic _ _ code | .sintArithmetic _ _ code => .arithmetic code
  | .uintBits _ code | .sintBits _ code | .bytesBits _ code => .bits code
  | .uintCompare _ code | .sintCompare _ code => .compare code
  | .equal _ => .compare .eq
  | .uintShl _ _ | .sintShl _ _ => .shl
  | .uintShr _ _ | .sintShr _ _ => .shr

def binaryMode (operation : Core.Binary a b result) (fallback : ArithmeticMode := .checked) : ArithmeticMode :=
  match operation with
  | .uintArithmetic _ mode _ | .sintArithmetic _ mode _ => mode
  | _ => fallback

theorem binary_effect (operation : Core.Binary a b result) (left : a.Value) (right : b.Value)
    (fallback : ArithmeticMode := .checked) :
    Effects.binary (binaryMode operation fallback) (binaryCode operation) (scalar a left) (scalar b right) =
      (Effects.liftCore (operation.eval left right)).map (scalar result) := by
  cases operation <;> try cases a
  all_goals
    simp [Effects.binary, binaryCode, binaryMode, scalar, Static.common, Static.implicit,
      Effects.scalarCast, Static.allows, Static.convert,
      SType.scalarSupported, Static.coerce, Static.checkBinary, Static.checkHomogeneous,
      BinaryCode.asymmetric, Effects.evalBinary, Static.ScalarBinary.eval, Core.Binary.eval,
      scalarValue, SType.ofCore, Effects.liftConversion, Effects.liftCore, Except.map, Core.Ty.equal,
      compareUnsigned, compareSigned]

theorem not_effect (value : Bool) (mode : ArithmeticMode) :
    Effects.unary mode .not (scalar .bool value) = .ok (scalar .bool (!value)) := rfl

theorem uintNot_effect (width : Width) (value : BitVec width.bits) (mode : ArithmeticMode) :
    Effects.unary mode .bitnot (scalar (.uint width) value) = .ok (scalar (.uint width) (~~~value)) := rfl

theorem sintNot_effect (width : Width) (value : BitVec width.bits) (mode : ArithmeticMode) :
    Effects.unary mode .bitnot (scalar (.sint width) value) = .ok (scalar (.sint width) (~~~value)) := rfl

theorem bytesNot_effect (width : Width) (value : BitVec width.bits) (mode : ArithmeticMode) :
    Effects.unary mode .bitnot (scalar (.fixedBytes width) value) = .ok (scalar (.fixedBytes width) (~~~value)) := rfl

theorem negate_effect (width : Width) (value : BitVec width.bits) (mode : ArithmeticMode) :
    Effects.unary mode .neg (scalar (.sint width) value) =
      (Effects.liftCore ((Core.Unary.negate width mode).eval value)).map (scalar (.sint width)) := by
  cases result : signedResult width mode (-value.toInt) <;> rfl

theorem uintCast_effect (registry : Registry) (fuel budget : Nat) (heap : Aggregates.Heap)
    (src dst : Width) (value : BitVec src.bits) :
    Effects.convert registry fuel budget heap (.explicit .ordinary) (.uint dst) (scalar (.uint src) value) =
      .ok (scalar (.uint dst) (BitVec.ofNat dst.bits value.toNat), heap, budget) := by
  simp [Effects.convert, scalar, Aggregates.Value.reference, Effects.scalarCast, Static.allows,
    Static.sourceCast, Static.castTarget, Static.explicitRule, Static.convert,
    SType.scalarSupported, Static.coerce_uint, scalarValue, SType.ofCore, Effects.liftConversion]

theorem sintCast_effect (registry : Registry) (fuel budget : Nat) (heap : Aggregates.Heap)
    (src dst : Width) (value : BitVec src.bits) :
    Effects.convert registry fuel budget heap (.explicit .ordinary) (.sint dst) (scalar (.sint src) value) =
      .ok (scalar (.sint dst) (BitVec.ofInt dst.bits value.toInt), heap, budget) := by
  simp [Effects.convert, scalar, Aggregates.Value.reference, Effects.scalarCast, Static.allows,
    Static.sourceCast, Static.castTarget, Static.explicitRule, Static.convert,
    SType.scalarSupported, Static.coerce_sint, scalarValue, SType.ofCore, Effects.liftConversion]

theorem signed_effect (registry : Registry) (fuel budget : Nat) (heap : Aggregates.Heap)
    (width : Width) (value : BitVec width.bits) :
    Effects.convert registry fuel budget heap (.explicit .ordinary) (.sint width) (scalar (.uint width) value) =
      .ok (scalar (.sint width) value, heap, budget) := by
  simp [Effects.convert, scalar, Aggregates.Value.reference, Effects.scalarCast, Static.allows,
    Static.sourceCast, Static.castTarget, Static.explicitRule, Static.convert,
    SType.scalarSupported, Static.coerce, scalarValue, SType.ofCore, Effects.liftConversion]

theorem unsigned_effect (registry : Registry) (fuel budget : Nat) (heap : Aggregates.Heap)
    (width : Width) (value : BitVec width.bits) :
    Effects.convert registry fuel budget heap (.explicit .ordinary) (.uint width) (scalar (.sint width) value) =
      .ok (scalar (.uint width) value, heap, budget) := by
  simp [Effects.convert, scalar, Aggregates.Value.reference, Effects.scalarCast, Static.allows,
    Static.sourceCast, Static.castTarget, Static.explicitRule, Static.convert,
    SType.scalarSupported, Static.coerce, scalarValue, SType.ofCore, Effects.liftConversion]

theorem address_effect (registry : Registry) (fuel budget : Nat) (heap : Aggregates.Heap)
    (value : BitVec 160) :
    Effects.convert registry fuel budget heap (.explicit .ordinary) (.address false) (scalar (.uint 19) value) =
      .ok (scalar .address value, heap, budget) := by
  have width : (19 : Width).val = 19 := rfl
  simp [Effects.convert, scalar, Aggregates.Value.reference, Effects.scalarCast, Static.allows,
    Static.sourceCast, Static.castTarget, Static.explicitRule, Static.convert,
    SType.scalarSupported, Static.coerce, scalarValue, SType.ofCore, Effects.liftConversion, width]
  exact BitVec.setWidth_eq value

theorem uintOfAddress_effect (registry : Registry) (fuel budget : Nat) (heap : Aggregates.Heap)
    (value : BitVec 160) :
    Effects.convert registry fuel budget heap (.explicit .ordinary) (.uint 19) (scalar .address value) =
      .ok (scalar (.uint 19) value, heap, budget) := by
  have width : (19 : Width).val = 19 := rfl
  simp [Effects.convert, scalar, Aggregates.Value.reference, Effects.scalarCast, Static.allows,
    Static.sourceCast, Static.castTarget, Static.explicitRule, Static.convert,
    SType.scalarSupported, Static.coerce, scalarValue, SType.ofCore, Effects.liftConversion, width]
  exact BitVec.setWidth_eq value

end Solidity.Execution.Compatibility
