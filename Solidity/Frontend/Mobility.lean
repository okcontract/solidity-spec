/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.StringLiteral
import Solidity.Core.Conversions

namespace Solidity.Frontend
open Core Static Lexical

/-- Runtime integer representability. A fractional rational stays a compile-time
constant; a use requiring fixed-point runtime execution is unsupported by the
pinned compiler and by this executable scalar profile. -/
def FitsInteger (signed : Bool) (width : Width) (value : Rat) : Prop :=
  value.den = 1 ∧ if signed then
    -(2 : Int)^(width.bits-1) ≤ value.num ∧ value.num < (2 : Int)^(width.bits-1)
  else 0 ≤ value.num ∧ value.num < (2 : Int)^width.bits

instance (signed : Bool) (width : Width) (value : Rat) : Decidable (FitsInteger signed width value) :=
  inferInstanceAs (Decidable (_ ∧ _))

def fitsInteger (signed : Bool) (width : Width) (value : Rat) : Bool :=
  value.den == 1 && if signed then
    -(2 : Int)^(width.bits-1) ≤ value.num && value.num < (2 : Int)^(width.bits-1)
  else 0 ≤ value.num && value.num < (2 : Int)^width.bits

theorem fitsInteger_iff (signed : Bool) (width : Width) (value : Rat) :
    fitsInteger signed width value = true ↔ FitsInteger signed width value := by
  cases signed <;> simp [fitsInteger, FitsInteger]

/-- First representable width in the ordered set 8,16,...,256. The relation
records that all preceding widths fail; it is independent of `find?`. -/
def IntegerMobile (value : Rat) (width : Width) : Prop :=
  ∃ before after, List.finRange 32 = before ++ width :: after ∧
    (∀ w ∈ before, ¬ FitsInteger (value.num < 0) w value) ∧
    FitsInteger (value.num < 0) width value

def integerMobile (value : Rat) : Option Width :=
  (List.finRange 32).find? fun width => fitsInteger (value.num < 0) width value

theorem integerMobile_iff (value : Rat) (width : Width) :
    integerMobile value = some width ↔ IntegerMobile value width := by
  simp only [integerMobile, List.find?_eq_some_iff_append, IntegerMobile,
    fitsInteger_iff]
  constructor
  · rintro ⟨yes, before, after, eq, no⟩
    exact ⟨before, after, eq, fun w hw => by simpa [Bool.eq_false_iff, fitsInteger_iff] using no w hw, yes⟩
  · rintro ⟨before, after, eq, no, yes⟩
    exact ⟨yes, before, after, eq, fun w hw => by simpa [Bool.eq_false_iff, fitsInteger_iff] using no w hw⟩

inductive StaticError where
  | rejected
  | unsupported
  | literal (error : Literal.Error)
  | lexical (error : Lexical.Error)
  | unknownName (name : String)
  deriving DecidableEq, Repr

def mobile (value : Rat) : Except StaticError SType :=
  if value.den != 1 then .error .unsupported else
  match integerMobile value with
  | some width => .ok (if value.num < 0 then .sint width else .uint width)
  | none => .error .rejected

/-- Literal conversion is a distinct judgment from machine conversion. Source
constants must fit without truncation, and only original hex tokens (or zero)
can become fixed bytes. -/
def NumberConverts (mode : ConversionMode) (number : Number) (type : SType) : Prop :=
  match mode, type with
  | .explicit .payable, .address true => number.value = 0
  | .explicit .payable, _ => False
  | _, .uint width => FitsInteger false width number.value
  | _, .sint width => FitsInteger true width number.value
  | _, .fixedBytes width => number.value = 0 ∨
      number.hexBytes = some width ∧ FitsInteger false width number.value
  | .explicit .ordinary, .address false => FitsInteger false 19 number.value
  | .explicit .ordinary, .enumType _ members => number.value.den = 1 ∧
      0 ≤ number.value.num ∧ number.value.num < members.val + 1
  | _, _ => False

def numberConverts (mode : ConversionMode) (number : Number) (type : SType) : Bool :=
  match mode, type with
  | .explicit .payable, .address true => number.value == 0
  | .explicit .payable, _ => false
  | _, .uint width => fitsInteger false width number.value
  | _, .sint width => fitsInteger true width number.value
  | _, .fixedBytes width => number.value == 0 ||
      (number.hexBytes == some width && fitsInteger false width number.value)
  | .explicit .ordinary, .address false => fitsInteger false 19 number.value
  | .explicit .ordinary, .enumType _ members => number.value.den == 1 &&
      0 ≤ number.value.num && number.value.num < members.val + 1
  | _, _ => false

theorem numberConverts_iff (mode : ConversionMode) (number : Number) (type : SType) :
    numberConverts mode number type = true ↔ NumberConverts mode number type := by
  cases mode with
  | implicit => cases type <;> simp [numberConverts, NumberConverts, fitsInteger_iff]
  | explicit kind =>
      cases kind <;> cases type <;> simp [numberConverts, NumberConverts, fitsInteger_iff, and_assoc]
      all_goals rename_i payable; cases payable <;> simp [fitsInteger_iff]

def numberValue (number : Number) (type : SType) : Except StaticError type.Value :=
  match type with
  | .uint width | .sint width | .fixedBytes width => .ok (BitVec.ofInt width.bits number.value.num)
  | .address _ => .ok (BitVec.ofInt 160 number.value.num)
  | .enumType _ members =>
      if bound : number.value.num.toNat < members.val+1 then .ok ⟨number.value.num.toNat, bound⟩
      else .error .rejected
  | _ => .error .unsupported

def convertNumber (mode : ConversionMode) (number : Number) (type : SType) : Except StaticError type.Value :=
  if !type.scalarSupported then .error .unsupported
  else if numberConverts mode number type then numberValue number type else .error .rejected

theorem number_unsigned_exact (number : Number) (width : Width)
    (valid : NumberConverts .implicit number (.uint width)) :
    ((BitVec.ofInt width.bits number.value.num).toNat : Int) = number.value.num := by
  have bounds : FitsInteger false width number.value := valid
  simp only [FitsInteger, Bool.false_eq_true, ↓reduceIte] at bounds
  have nonneg := bounds.2.1
  simp [BitVec.toNat_ofInt, Int.emod_eq_of_lt nonneg bounds.2.2, Int.toNat_of_nonneg nonneg]

end Solidity.Frontend
