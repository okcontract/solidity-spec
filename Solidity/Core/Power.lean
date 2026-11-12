/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Scalar

namespace Solidity.Core

/-- Binary exponentiation, with at most 256 recursive steps for a Solidity
exponent. This computes in the fixed-width ring and never materializes a huge
unbounded integer power. -/
def wordPow (base : BitVec bits) (exponent : Nat) : BitVec bits :=
  if _zero : exponent = 0 then 1 else
    let half := wordPow base (exponent / 2)
    if exponent % 2 = 0 then half * half else half * half * base
termination_by exponent

theorem wordPow_spec (base : BitVec bits) (exponent : Nat) : wordPow base exponent = base ^ exponent := by
  induction exponent using Nat.strongRecOn with
  | ind exponent ih =>
    rw [wordPow]
    split
    · rename_i zero
      subst exponent
      rfl
    · rename_i nonzero
      rw [ih (exponent / 2) (by omega)]
      dsimp only
      split
      · rename_i even
        rw [← BitVec.pow_add]
        congr 1
        omega
      · rename_i odd
        rw [← BitVec.pow_add, ← BitVec.pow_succ]
        congr 1
        omega

private theorem cap_mul_left (cap a b : Nat) :
    min cap (min cap a * b) = min cap (a * b) := by
  by_cases zero : b = 0
  · simp [zero]
  · rw [← Nat.mul_min_mul_right, ← Nat.min_assoc,
      Nat.min_eq_left (Nat.le_mul_of_pos_right cap (by omega))]

private theorem cap_mul (cap a b : Nat) :
    min cap (min cap a * min cap b) = min cap (a * b) := by
  rw [cap_mul_left, Nat.mul_comm a, cap_mul_left, Nat.mul_comm b]

/-- Saturate at a caller-supplied bound. For Solidity bases, intermediate integers have at most
 twice the bound's bit length, including for a 256-bit exponent. -/
def boundedPow (cap base exponent : Nat) : Nat :=
  if _zero : exponent = 0 then min cap 1 else
    let half := boundedPow cap base (exponent / 2)
    let square := min cap (half * half)
    if exponent % 2 = 0 then square else min cap (square * base)
termination_by exponent

theorem boundedPow_spec (cap base exponent : Nat) :
    boundedPow cap base exponent = min cap (base ^ exponent) := by
  induction exponent using Nat.strongRecOn with
  | ind exponent ih =>
    rw [boundedPow]
    split
    · rename_i zero; subst exponent; rfl
    · rw [ih (exponent / 2) (by omega)]
      dsimp only
      rw [cap_mul, ← Nat.pow_add]
      split
      · congr 2; omega
      · rw [cap_mul_left, ← Nat.pow_succ]
        congr 2
        omega

theorem boundedPow_lt (cap base exponent : Nat) :
    boundedPow cap base exponent < cap ↔ base ^ exponent < cap := by
  rw [boundedPow_spec]
  omega

/-- Runtime exponentiation takes an unsigned exponent independently of the
base width. Unchecked mode wraps; checked mode panics on overflow. -/
def unsignedPow (width count : Width) (mode : ArithmeticMode)
    (base : BitVec width.bits) (exponent : BitVec count.bits) : Result (BitVec width.bits) :=
  if mode == .unchecked || boundedPow (2^width.bits) base.toNat exponent.toNat < 2^width.bits then
    .ok (wordPow base exponent.toNat)
  else .error (Contract.panic 0x11)

theorem unsignedPow_checked (width count : Width) (base : BitVec width.bits) (exponent : BitVec count.bits) :
    unsignedPow width count .checked base exponent =
      if base.toNat ^ exponent.toNat < 2^width.bits then .ok (base ^ exponent.toNat)
      else .error (Contract.panic 0x11) := by
  simp [unsignedPow, wordPow_spec, boundedPow_lt]

theorem unsignedPow_unchecked (width count : Width) (base : BitVec width.bits) (exponent : BitVec count.bits) :
    unsignedPow width count .unchecked base exponent = .ok (base ^ exponent.toNat) := by
  simp [unsignedPow, wordPow_spec]

private theorem pow_ofInt (value : Int) (exponent : Nat) :
    (BitVec.ofInt bits value) ^ exponent = BitVec.ofInt bits (value ^ exponent) := by
  induction exponent with
  | zero => simp
  | succ n ih => rw [BitVec.pow_succ, ih, Int.pow_succ, BitVec.ofInt_mul]

private theorem int_pow_sign (value : Int) (exponent : Nat) :
    value ^ exponent = if value < 0 ∧ exponent % 2 = 1 then
      -((value.natAbs ^ exponent : Nat) : Int) else ((value.natAbs ^ exponent : Nat) : Int) := by
  by_cases negative : value < 0
  · have eq := Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt negative)
    conv => lhs; rw [eq, Int.neg_pow, ← Int.natCast_pow]
    have parity : exponent % 2 = 0 ∨ exponent % 2 = 1 := by omega
    rcases parity with parity | parity <;> simp [negative, parity]
  · have eq := Int.eq_natAbs_of_nonneg (by omega : 0 ≤ value)
    conv => lhs; rw [eq, ← Int.natCast_pow]
    simp [negative]

def signedPow (width count : Width) (mode : ArithmeticMode)
    (base : BitVec width.bits) (exponent : BitVec count.bits) : Result (BitVec width.bits) :=
  let negative := base.toInt < 0 ∧ exponent.toNat % 2 = 1
  let cap := 2^(width.bits-1) + if negative then 1 else 0
  if mode == .unchecked || boundedPow cap base.toInt.natAbs exponent.toNat < cap then
    .ok (wordPow base exponent.toNat)
  else .error (Contract.panic 0x11)

theorem signedPow_checked (width count : Width) (base : BitVec width.bits) (exponent : BitVec count.bits) :
    signedPow width count .checked base exponent = signedResult width .checked (base.toInt ^ exponent.toNat) := by
  have wrapped : wordPow base exponent.toNat = BitVec.ofInt width.bits (base.toInt ^ exponent.toNat) := by
    calc
      wordPow base exponent.toNat = base ^ exponent.toNat := wordPow_spec _ _
      _ = (BitVec.ofInt width.bits base.toInt) ^ exponent.toNat := by rw [BitVec.ofInt_toInt]
      _ = BitVec.ofInt width.bits (base.toInt ^ exponent.toNat) := pow_ofInt _ _
  have bounds : (base.toInt.natAbs ^ exponent.toNat <
      2^(width.bits-1) + if base.toInt < 0 ∧ exponent.toNat % 2 = 1 then 1 else 0) ↔
      (-(2 : Int)^(width.bits-1) ≤ base.toInt ^ exponent.toNat ∧
        base.toInt ^ exponent.toNat < (2 : Int)^(width.bits-1)) := by
    rw [int_pow_sign base.toInt exponent.toNat]
    have positive : 0 < 2^(width.bits-1) := Nat.two_pow_pos _
    have cast : ((2^(width.bits-1) : Nat) : Int) = (2 : Int)^(width.bits-1) := by simp
    by_cases negative : base.toInt < 0 ∧ exponent.toNat % 2 = 1 <;> simp [negative, -Int.natCast_pow] <;> omega
  simp only [signedPow, boundedPow_lt, wrapped]
  simp only [bounds, signedResult]
  simp

theorem signedPow_unchecked (width count : Width) (base : BitVec width.bits) (exponent : BitVec count.bits) :
    signedPow width count .unchecked base exponent = .ok (base ^ exponent.toNat) := by
  simp [signedPow, wordPow_spec]

end Solidity.Core
