/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Scalar
import Init.Data.Rat
import Solidity.Policy

/-! Exact compile-time rational constants. This module precedes conversion to
runtime scalar types; constant errors are elaboration errors, never panics.
Parsing and mixed literal/runtime type inference are separate obligations. -/
namespace Solidity.Frontend.Literal
open Core

inductive Error where
  | zeroDivisor | fractionalOperand | negativeShift | precisionLimit | notRepresentable
  deriving DecidableEq, Repr

inductive Unary where
  | neg | bitnot
  deriving DecidableEq, Repr

inductive Binary where
  | add | sub | mul | div | mod | pow | bitand | bitor | bitxor | shl | shr
  deriving DecidableEq, Repr

/-- The 0.8.36 rational-expression policy checks the normalized result after
binary operations. Its published 4096-bit bound is expressed as a highest-bit
index (so 2^4096 itself passes this check). This is compile-time admission,
independent of runtime scalar overflow. -/
def withinPrecision (value : Rat) : Bool :=
  value.num == 0 || (value.num.natAbs.log2 ≤ Policy.Solc0836.rationalMaxBitIndex &&
    value.den.log2 ≤ Policy.Solc0836.rationalMaxBitIndex)

/-- Pinned conservative exponent precheck. Bases 0 and 1 are special; otherwise
exponent * bit-length(base) must fit the 4096-bit work bound. -/
def fitsExponent (base exponent : Nat) : Bool :=
  base ≤ 1 || (base.log2 ≤ Policy.Solc0836.rationalWorkBits &&
    exponent * (base.log2 + 1) ≤ Policy.Solc0836.rationalWorkBits)

def Unary.eval (op : Unary) (value : Rat) : Except Error Rat :=
  match op with
  | .neg => .ok (-value)
  | .bitnot => if value.den = 1 then .ok (Rat.ofInt (~~~value.num)) else .error .fractionalOperand

/-- Infinite two's-complement bit operations. Nat xor clears the intersection
in the mixed-sign cases; negative integers are represented as complements of
nonnegative naturals, independently of any runtime width. -/
def intBits (op : Core.Bitwise) : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (match op with
    | .bitand => a &&& b | .bitor => a ||| b | .bitxor => a ^^^ b)
  | .ofNat a, .negSucc b => match op with
    | .bitand => .ofNat (a ^^^ (a &&& b))
    | .bitor => .negSucc (b ^^^ (a &&& b))
    | .bitxor => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => match op with
    | .bitand => .ofNat (b ^^^ (a &&& b))
    | .bitor => .negSucc (a ^^^ (a &&& b))
    | .bitxor => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => match op with
    | .bitand => .negSucc (a ||| b)
    | .bitor => .negSucc (a &&& b)
    | .bitxor => .ofNat (a ^^^ b)

/-- Bit observation of an unbounded two's-complement integer. -/
def intBit : Int → Nat → Bool
  | .ofNat value, index => value.testBit index
  | .negSucc value, index => !(value.testBit index)

def bitwiseBit (op : Core.Bitwise) (a b : Bool) : Bool :=
  match op with
  | .bitand => a && b | .bitor => a || b | .bitxor => xor a b

/-- Every bit of the signed constant operation agrees with the corresponding
Boolean operation, including arbitrarily high sign-extension bits. -/
theorem intBits_spec (op : Core.Bitwise) (a b : Int) (index : Nat) :
    intBit (intBits op a b) index = bitwiseBit op (intBit a index) (intBit b index) := by
  cases a <;> cases b <;> rename_i x y
  all_goals
    cases op <;> simp only [intBits, intBit, bitwiseBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    all_goals cases x.testBit index <;> cases y.testBit index <;> decide

/-- Raw rational computation. The syntax-level binary evaluator below applies
normalized-result precision checks as well. See the local Types.zig rational
computation and the pinned reference ConstantEvaluator for the matching rules. -/
def Binary.compute (op : Binary) (x y : Rat) : Except Error Rat :=
  match op with
  | .add => .ok (x + y)
  | .sub => .ok (x - y)
  | .mul => .ok (x * y)
  | .div => if y.num = 0 then .error .zeroDivisor else .ok (x / y)
  | .mod => if y.num = 0 then .error .zeroDivisor else
      let q := x / y
      .ok (x - Rat.ofInt (q.num.tdiv q.den) * y)
  | .pow =>
      if y.den ≠ 1 then .error .fractionalOperand
      else if y.num = 0 then .ok 1
      -- Solidity 0.8.36 defines zero to every nonzero literal exponent as zero,
      -- including negative exponents. Do not replace this by rational inversion.
      else if x.num = 0 || x = 1 then .ok x
      else if x = -1 then .ok (if y.num.natAbs % 2 = 0 then 1 else -1)
      else if y.num.natAbs < 2^Policy.Solc0836.arithmeticExponentBits && fitsExponent x.num.natAbs y.num.natAbs &&
          fitsExponent x.den y.num.natAbs then .ok (x ^ y.num)
      else .error .precisionLimit
  | .bitand | .bitor | .bitxor =>
      if x.den ≠ 1 ∨ y.den ≠ 1 then .error .fractionalOperand else
      .ok (Rat.ofInt (match op with
        | .bitand => intBits .bitand x.num y.num
        | .bitor => intBits .bitor x.num y.num
        | _ => intBits .bitxor x.num y.num))
  | .shl | .shr =>
      if x.den ≠ 1 ∨ y.den ≠ 1 then .error .fractionalOperand
      else if y.num < 0 then .error .negativeShift
      else if y.num.toNat ≥ 2^Policy.Solc0836.arithmeticExponentBits then .error .precisionLimit
      else if x.num = 0 then .ok 0
      else if op == .shl then
        if x.num.natAbs.log2 + 1 + y.num.toNat ≤ Policy.Solc0836.rationalWorkBits then
          .ok (Rat.ofInt (x.num <<< y.num.toNat)) else .error .precisionLimit
      else if y.num.toNat > x.num.natAbs.log2 then .ok (if x.num < 0 then -1 else 0)
      else .ok (Rat.ofInt (x.num >>> y.num.toNat))

def Binary.eval (op : Binary) (x y : Rat) : Except Error Rat := do
  let result ← op.compute x y
  if withinPrecision result then .ok result else .error .precisionLimit

inductive Expr where
  | number : Rat → Expr
  | unary : Unary → Expr → Expr
  | binary : Binary → Expr → Expr → Expr

def Expr.eval : Expr → Except Error Rat
  | .number value => .ok value
  | .unary op value => do op.eval (← value.eval)
  | .binary op a b => do op.eval (← a.eval) (← b.eval)

theorem Binary.eval_precision (op : Binary) (x y result : Rat)
    (h : op.eval x y = .ok result) : withinPrecision result = true := by
  unfold eval at h
  cases hc : op.compute x y with
  | error error => simp [hc] at h <;> cases h
  | ok value =>
      simp only [hc] at h
      change (if withinPrecision value then Except.ok value else Except.error Error.precisionLimit) = _ at h
      split at h
      next hp => cases h; exact hp
      next => cases h

/-- Literal conversion checks representability; unlike a runtime uint cast it
must not silently truncate an out-of-range constant. -/
def toUnsigned (width : Width) (value : Rat) : Except Error (BitVec width.bits) :=
  if value.den = 1 ∧ 0 ≤ value.num ∧ value.num < (2 : Int) ^ width.bits then
    .ok (BitVec.ofNat width.bits value.num.toNat)
  else .error .notRepresentable

def toSigned (width : Width) (value : Rat) : Except Error (BitVec width.bits) :=
  if value.den = 1 ∧ -(2 : Int) ^ (width.bits - 1) ≤ value.num ∧
      value.num < (2 : Int) ^ (width.bits - 1) then
    .ok (BitVec.ofInt width.bits value.num)
  else .error .notRepresentable

theorem unsigned_exact (width : Width) (value : Rat) (word : BitVec width.bits)
    (h : toUnsigned width value = .ok word) :
    value.den = 1 ∧ (word.toNat : Int) = value.num := by
  unfold toUnsigned at h
  split at h
  next bounds =>
    cases h
    refine ⟨bounds.1, ?_⟩
    have bound : value.num.toNat < 2 ^ width.bits := by
      have hb : value.num < ((2 ^ width.bits : Nat) : Int) := by
        simpa only [Int.natCast_pow] using bounds.2.2
      omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Int.toNat_of_nonneg bounds.2.1]
  next => cases h

theorem signed_exact (width : Width) (value : Rat) (word : BitVec width.bits)
    (h : toSigned width value = .ok word) :
    value.den = 1 ∧ word.toInt = value.num := by
  unfold toSigned at h
  split at h
  next bounds =>
    cases h
    exact ⟨bounds.1, BitVec.toInt_ofInt_eq_self width.bits_pos bounds.2.1 bounds.2.2⟩
  next => cases h

/-- Conversion is precisely integral representability, in both directions. -/
theorem unsigned_iff (width : Width) (value : Rat) (word : BitVec width.bits) :
    toUnsigned width value = .ok word ↔ value.den = 1 ∧ (word.toNat : Int) = value.num := by
  constructor
  · exact unsigned_exact width value word
  · rintro ⟨hd, hv⟩
    have bound : (word.toNat : Int) < (2 : Int) ^ width.bits := by
      exact_mod_cast word.isLt
    simp [toUnsigned, hd, ← hv, bound]

theorem signed_iff (width : Width) (value : Rat) (word : BitVec width.bits) :
    toSigned width value = .ok word ↔ value.den = 1 ∧ word.toInt = value.num := by
  constructor
  · exact signed_exact width value word
  · rintro ⟨hd, hv⟩
    simp [toSigned, hd, ← hv, BitVec.le_toInt, BitVec.toInt_lt]

theorem unsigned_fractional (width : Width) (value : Rat) (h : value.den ≠ 1) :
    toUnsigned width value = .error .notRepresentable := by simp [toUnsigned, h]

theorem signed_fractional (width : Width) (value : Rat) (h : value.den ≠ 1) :
    toSigned width value = .error .notRepresentable := by simp [toSigned, h]

def Expr.unsigned (width : Width) (expr : Expr) : Except Error (BitVec width.bits) :=
  expr.eval >>= toUnsigned width

def Expr.signed (width : Width) (expr : Expr) : Except Error (BitVec width.bits) :=
  expr.eval >>= toSigned width

theorem Expr.unsigned_exact (width : Width) (expr : Expr) (word : BitVec width.bits)
    (h : expr.unsigned width = .ok word) :
    ∃ value, expr.eval = .ok value ∧ value.den = 1 ∧ (word.toNat : Int) = value.num := by
  cases he : expr.eval with
  | error error => simp [unsigned, he] at h <;> cases h
  | ok value =>
      have converted : toUnsigned width value = .ok word := by simpa [unsigned, he] using h
      exact ⟨value, rfl, Literal.unsigned_exact width value word converted⟩

theorem Expr.signed_exact (width : Width) (expr : Expr) (word : BitVec width.bits)
    (h : expr.signed width = .ok word) :
    ∃ value, expr.eval = .ok value ∧ value.den = 1 ∧ word.toInt = value.num := by
  cases he : expr.eval with
  | error error => simp [signed, he] at h <;> cases h
  | ok value =>
      have converted : toSigned width value = .ok word := by simpa [signed, he] using h
      exact ⟨value, rfl, Literal.signed_exact width value word converted⟩

theorem Expr.unsigned_iff (width : Width) (expr : Expr) (word : BitVec width.bits) :
    expr.unsigned width = .ok word ↔
      ∃ value, expr.eval = .ok value ∧ value.den = 1 ∧ (word.toNat : Int) = value.num := by
  constructor
  · exact Expr.unsigned_exact width expr word
  · rintro ⟨value, he, hd, hv⟩
    simp only [unsigned, he]
    exact (Literal.unsigned_iff width value word).mpr ⟨hd, hv⟩

theorem Expr.signed_iff (width : Width) (expr : Expr) (word : BitVec width.bits) :
    expr.signed width = .ok word ↔
      ∃ value, expr.eval = .ok value ∧ value.den = 1 ∧ word.toInt = value.num := by
  constructor
  · exact Expr.signed_exact width expr word
  · rintro ⟨value, he, hd, hv⟩
    simp only [signed, he]
    exact (Literal.signed_iff width value word).mpr ⟨hd, hv⟩

end Solidity.Frontend.Literal
