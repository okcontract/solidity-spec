/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.StaticTypes

namespace Solidity.Static
open Core

inductive ConversionMode where
  | implicit
  | explicit : CastKind → ConversionMode
  deriving DecidableEq, Repr

def Allowed (mode : ConversionMode) (sourceTy to : SType) : Prop :=
  match mode with
  | .implicit => Implicit sourceTy to
  | .explicit kind => SourceCast kind sourceTy to

def allows (mode : ConversionMode) (sourceTy to : SType) : Bool :=
  match mode with
  | .implicit => implicit sourceTy to
  | .explicit kind => sourceCast kind sourceTy to

theorem allows_iff (mode : ConversionMode) (sourceTy to : SType) :
    allows mode sourceTy to = true ↔ Allowed mode sourceTy to := by
  cases mode <;> simp [allows, Allowed, implicit_iff, sourceCast_iff]

inductive ConversionFailure where
  | rejected
  | unsupported
  | panic (bytes : List UInt8)
  deriving DecidableEq, Repr

/-- Byte strings resize at the right-hand end, whereas integers extend or
truncate their most significant bits. This distinction is source-observable. -/
def bytesResize (src dst : Width) (value : BitVec src.bits) : BitVec dst.bits :=
  if src.bits ≤ dst.bits then value.setWidth dst.bits <<< (dst.bits-src.bits)
  else (value >>> (src.bits-dst.bits)).setWidth dst.bits

/-- Low-level value conversion. Only `convert` or a theorem discharging Allowed
may expose it as a source cast; its mere existence grants no conversion rule. -/
def coerce (sourceTy to : SType) (value : sourceTy.Value) : Except ConversionFailure to.Value :=
  if same : sourceTy = to then .ok (same ▸ value) else
  match sourceTy, to, value with
  | .uint _, .uint dst, value => .ok (value.setWidth dst.bits)
  | .sint _, .sint dst, value => .ok (BitVec.ofInt dst.bits value.toInt)
  | .uint _, .sint dst, value => .ok (value.setWidth dst.bits)
  | .sint _, .uint dst, value => .ok (value.setWidth dst.bits)
  | .uint _, .fixedBytes dst, value => .ok (value.setWidth dst.bits)
  | .fixedBytes _, .uint dst, value => .ok (value.setWidth dst.bits)
  | .fixedBytes src, .fixedBytes dst, value => .ok (bytesResize src dst value)
  | .uint _, .address _, value | .fixedBytes _, .address _, value => .ok (value.setWidth 160)
  | .address _, .uint dst, value | .address _, .fixedBytes dst, value => .ok (value.setWidth dst.bits)
  | .address _, .address _, value | .address _, .contract _ _ _, value |
    .contract _ _ _, .address _, value | .contract _ _ _, .contract _ _ _, value => .ok value
  | .uint _, .enumType _ members, value =>
      if bound : value.toNat < members.val + 1 then .ok ⟨value.toNat, bound⟩
      else .error (.panic (Contract.panic 0x21))
  | .sint _, .enumType _ members, value =>
      if _nonnegative : 0 ≤ value.toInt then
        if bound : value.toInt.toNat < members.val + 1 then .ok ⟨value.toInt.toNat, bound⟩
        else .error (.panic (Contract.panic 0x21))
      else .error (.panic (Contract.panic 0x21))
  | .enumType _ _, .uint dst, value => .ok (BitVec.ofNat dst.bits value.val)
  | .function va _ _ _, .function vb _ _ _, value =>
      if equal : va = vb then .ok (equal ▸ value) else .error .unsupported
  | _, _, _ => .error .unsupported

def convert (mode : ConversionMode) (sourceTy to : SType) (value : sourceTy.Value) : Except ConversionFailure to.Value :=
  if !sourceTy.scalarSupported || !to.scalarSupported then .error .unsupported
  else if allows mode sourceTy to then coerce sourceTy to value else .error .rejected

theorem convert_rejects (mode : ConversionMode) (sourceTy to : SType) (value : sourceTy.Value)
    (source : sourceTy.scalarSupported = true) (target : to.scalarSupported = true)
    (invalid : ¬ Allowed mode sourceTy to) : convert mode sourceTy to value = .error .rejected := by
  have failed : allows mode sourceTy to = false := by
    cases h : allows mode sourceTy to with
    | false => rfl
    | true => exact False.elim (invalid ((allows_iff mode sourceTy to).mp h))
  simp [convert, source, target, failed]

theorem convert_identity (mode : ConversionMode) (type : SType) (value : type.Value)
    (supported : type.scalarSupported = true) (valid : Allowed mode type type) :
    convert mode type type value = .ok value := by
  simp [convert, supported, (allows_iff mode type type).mpr valid, coerce]

/-- Nominal construction is explicit; no general coercion between a value type
and its underlying elementary value is introduced. -/
def wrap (identity : Nat) (base : Elementary) (value : base.core.Value) :
    (SType.valueType identity base).Value := value

def unwrap (identity : Nat) (base : Elementary) (value : (SType.valueType identity base).Value) :
    base.core.Value := value

theorem unwrap_wrap (identity : Nat) (base : Elementary) (value : base.core.Value) :
    unwrap identity base (wrap identity base value) = value := rfl

theorem wrap_unwrap (identity : Nat) (base : Elementary) (value : (SType.valueType identity base).Value) :
    wrap identity base (unwrap identity base value) = value := rfl

theorem unsigned_widen_exact (src dst : Width) (value : BitVec src.bits) (wide : src.val ≤ dst.val) :
    (value.setWidth dst.bits).toNat = value.toNat := by
  have bits : src.bits ≤ dst.bits := by simp only [Width.bits]; omega
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le value.isLt (Nat.pow_le_pow_right (by decide) bits)

theorem signed_widen_exact (src dst : Width) (value : BitVec src.bits) (wide : src.val ≤ dst.val) :
    (BitVec.ofInt dst.bits value.toInt).toInt = value.toInt := by
  have bits : src.bits-1 ≤ dst.bits-1 := by simp only [Width.bits]; omega
  have bounds : (2 : Int)^(src.bits-1) ≤ (2 : Int)^(dst.bits-1) :=
    by exact_mod_cast (Nat.pow_le_pow_right (by decide) bits : (2 : Nat)^(src.bits-1) ≤ 2^(dst.bits-1))
  exact BitVec.toInt_ofInt_eq_self dst.bits_pos (by have := BitVec.le_toInt value; omega)
    (by have := BitVec.toInt_lt (x := value); omega)

/-- Internal conversion coverage is weaker than source permission: this relation
only says a value operation exists. `Allowed` remains the admission condition. -/
def Coercible (a b : SType) : Prop := a = b ∨ match a, b with
  | .uint _, .uint _ | .uint _, .sint _ | .uint _, .fixedBytes _ |
    .uint _, .address _ | .uint _, .enumType _ _ |
    .sint _, .sint _ | .sint _, .uint _ | .sint _, .enumType _ _ |
    .fixedBytes _, .uint _ | .fixedBytes _, .fixedBytes _ | .fixedBytes _, .address _ |
    .address _, .uint _ | .address _, .fixedBytes _ | .address _, .address _ |
    .address _, .contract _ _ _ | .contract _ _ _, .address _ |
    .contract _ _ _, .contract _ _ _ | .enumType _ _, .uint _ => True
  | .function va _ _ _, .function vb _ _ _ => va = vb
  | _, _ => False

theorem allowed_coercible (mode : ConversionMode) (a b : SType) (valid : Allowed mode a b) :
    Coercible a b := by
  cases mode with
  | implicit =>
      cases a <;> cases b <;> simp_all [Allowed, Implicit, Coercible]
      all_goals grind
  | explicit kind =>
      cases kind <;> cases a <;> cases b <;>
        simp_all [Allowed, SourceCast, CastTarget, ExplicitRule, Implicit, Coercible]
      all_goals grind

theorem coerce_supported (a b : SType) (value : a.Value) (valid : Coercible a b) :
    coerce a b value ≠ .error .unsupported := by
  unfold coerce
  split
  next => simp
  next different =>
    simp only [Coercible, different, false_or] at valid
    cases a <;> cases b <;> simp_all
    all_goals split <;> simp_all
    all_goals split <;> simp_all

theorem convert_supported (mode : ConversionMode) (a b : SType) (value : a.Value)
    (source : a.scalarSupported = true) (target : b.scalarSupported = true)
    (valid : Allowed mode a b) : convert mode a b value ≠ .error .unsupported := by
  simp only [convert, source, target, Bool.not_true, Bool.or_self, Bool.false_eq_true,
    ↓reduceIte, (allows_iff _ _ _).mpr valid]
  exact coerce_supported a b value (allowed_coercible mode a b valid)

theorem bytesResize_same (width : Width) (value : BitVec width.bits) :
    bytesResize width width value = value := by simp [bytesResize]

theorem unsigned_narrow_mod (src dst : Width) (value : BitVec src.bits) :
    (value.setWidth dst.bits).toNat = value.toNat % 2^dst.bits := BitVec.toNat_setWidth _ _

theorem signed_conversion_mod (width : Width) (value : Int) :
    (BitVec.ofInt width.bits value).toNat = (value % (2 : Int)^width.bits).toNat :=
  BitVec.toNat_ofInt value

theorem coerce_ne_rejected (a b : SType) (value : a.Value) : coerce a b value ≠ .error .rejected := by
  unfold coerce
  split
  next => simp
  next =>
    cases a <;> cases b <;> simp
    all_goals split <;> simp_all
    all_goals split <;> simp_all

theorem coerce_uint (src dst : Width) (value : BitVec src.bits) :
    coerce (.uint src) (.uint dst) value = .ok (value.setWidth dst.bits) := by
  by_cases same : src = dst
  · subst dst; simp [coerce]
  · simp [coerce, same]

theorem coerce_sint (src dst : Width) (value : BitVec src.bits) :
    coerce (.sint src) (.sint dst) value = .ok (BitVec.ofInt dst.bits value.toInt) := by
  by_cases same : src = dst
  · subst dst; simp [coerce]
  · simp [coerce, same]

theorem coerce_fixedBytes (src dst : Width) (value : BitVec src.bits) :
    coerce (.fixedBytes src) (.fixedBytes dst) value = .ok (bytesResize src dst value) := by
  by_cases same : src = dst
  · subst dst; simp [coerce, bytesResize_same]
  · simp [coerce, same]

theorem implicit_uint_exact (src dst : Width) (value : BitVec src.bits) (wide : src.val ≤ dst.val) :
    ((convert .implicit (.uint src) (.uint dst) value).map BitVec.toNat) = .ok value.toNat := by
  have allowed : implicit (.uint src) (.uint dst) = true :=
    (implicit_iff _ _).mpr (Or.inr wide)
  simp [convert, SType.scalarSupported, allows, allowed, coerce_uint, Except.map, unsigned_widen_exact src dst value wide]

theorem implicit_sint_exact (src dst : Width) (value : BitVec src.bits) (wide : src.val ≤ dst.val) :
    ((convert .implicit (.sint src) (.sint dst) value).map BitVec.toInt) = .ok value.toInt := by
  have allowed : implicit (.sint src) (.sint dst) = true :=
    (implicit_iff _ _).mpr (Or.inr wide)
  simp [convert, SType.scalarSupported, allows, allowed, coerce_sint, Except.map, signed_widen_exact src dst value wide]

end Solidity.Static
