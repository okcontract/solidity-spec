/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.NodeTyping

namespace Solidity.Frontend.Inference
open Core Static Lexical

/-- Asymmetric operators reject fractional literal counts. A literal left
operand must have a mobile integer type, then uses a full-width integer base. -/
def IntegralCount : Term context → Prop
  | .number value => value.value.den = 1
  | _ => True

def AsymmetricLeft (a : Term context) (left : SType) : Prop :=
  match a with
  | .number value => (∃ mobile, Mobile a mobile) ∧
      left = (if value.value.num < 0 then .sint 31 else .uint 31)
  | _ => Mobile a left

def RuntimeChoice (code : BinaryCode) (a b result : Term context) : Prop :=
  if code.asymmetric then
    IntegralCount b ∧ ∃ left, AsymmetricLeft a left ∧
      ∃ right, Mobile b right ∧ RuntimeBinary code a b left right result
  else ∃ type, CommonChoice a b type ∧ RuntimeBinary code a b type type result

private theorem bind_ok_iff (value : Except ε α) (next : α → Except ε β) :
    (value >>= next) = .ok result ↔ ∃ x, value = .ok x ∧ next x = .ok result := by
  cases value <;> simp [bind, Except.bind]

private theorem pure_ok (value : α) : (pure value : Except ε α) = .ok value := rfl
private theorem bind_error (error : ε) (next : α → Except ε β) :
    (Except.error error >>= next) = .error error := rfl
private theorem bind_ok (value : α) (next : α → Except ε β) :
    (Except.ok value >>= next) = next value := rfl
attribute [local simp] pure_ok bind_error bind_ok

theorem asymmetricLeft_iff (a : Term context) :
    (match a with
      | .number value => do
          let _ ← a.mobile
          pure (if value.value.num < 0 then SType.sint 31 else .uint 31)
      | _ => a.mobile) = .ok left ↔ AsymmetricLeft a left := by
  cases a <;> simp [AsymmetricLeft, bind_ok_iff, mobile_iff]
  intros
  exact eq_comm

theorem runtimeChoice_iff : binary.runtime code a b = .ok result ↔ RuntimeChoice code a b result := by
  unfold binary.runtime RuntimeChoice
  cases asym : code.asymmetric with
  | false => simp [bind_ok_iff, commonTerm_iff, runtimeBinary_iff]
  | true =>
      simp only [↓reduceIte]
      cases b with
      | number value =>
          by_cases integral : value.value.den = 1
          · cases a <;> simp [integral, IntegralCount, AsymmetricLeft, bind_ok_iff, mobile_iff, runtimeBinary_iff, and_assoc, exists_and_left]
          · simp [integral, IntegralCount]; intro h; cases h
      | string bytes =>
          cases a <;> simp [IntegralCount, AsymmetricLeft, bind_ok_iff, mobile_iff, runtimeBinary_iff, and_assoc, exists_and_left]
      | runtime type expression =>
          cases a <;> simp [IntegralCount, AsymmetricLeft, bind_ok_iff, mobile_iff, runtimeBinary_iff, and_assoc, exists_and_left]

/-- The left category controls builtin applicability before common-type choice.
This preserves the pinned asymmetry of numeric and string literals. -/
def LeftAdmissible (code : BinaryCode) (a b : Term context) : Prop :=
  match a with
  | .runtime type _ => permittedOnLeft code type = true ∧ match b with
      | .number value => value.value.den = 1 ∨ integerType type = true
      | _ => True
  | _ => True

def NumericTyping (code : BinaryCode) (x y : Number) (result : Term context) : Prop :=
  match literalBinary code with
  | some operation => ∃ value, operation.eval x.value y.value = .ok value ∧
      result = .number ⟨value, none⟩
  | none => ∃ left, Mobile (.number x : Term context) left ∧
      ∃ right, Mobile (.number y : Term context) right ∧
      ∃ type, Common left right type ∧ RuntimeBinary code (.number x) (.number y) type type result

def BinaryBody (code : BinaryCode) (a b result : Term context) : Prop :=
  match a, b with
  | .string _, _ => False
  | .number x, .number y => NumericTyping code x y result
  | .number value, .runtime type _ => value.value.den = 1 ∧ integerType type = true ∧ RuntimeChoice code a b result
  | _, _ => RuntimeChoice code a b result

/-- Full binary typing uses independently specified mobility, conversions,
primitive operator witnesses and exact constant arithmetic. It does not assume successful execution of `binary` or `infer` in its premises. -/
def BinaryTyping (code : BinaryCode) (a b result : Term context) : Prop :=
  if code == .and || code == .or then RuntimeBinary code a b .bool .bool result
  else LeftAdmissible code a b ∧ BinaryBody code a b result

private theorem throw_error (error : ε) : (throw error : Except ε α) = .error error := rfl
private theorem map_error (error : ε) (f : α → β) :
    (f <$> (Except.error error : Except ε α)) = .error error := rfl
private theorem mapError_ok_iff (value : Except ε α) (f : ε → ε') :
    value.mapError f = .ok result ↔ value = .ok result := by
  cases value <;> simp [Except.mapError]
attribute [local simp] throw_error map_error

private theorem commonRuntime_iff :
    (match common left right with
      | some type => runtimeBinary code a b type type
      | none => Except.error StaticError.rejected) = .ok result ↔
    ∃ type, Common left right type ∧ RuntimeBinary code a b type type result := by
  simp only [← common_iff, ← runtimeBinary_iff]
  cases hc : common left right <;> simp

theorem binary_iff : binary code a b = .ok result ↔ BinaryTyping code a b result := by
  by_cases logical : (code == .and || code == .or) = true
  · cases a <;> cases b <;> simp [binary, BinaryTyping, logical, bind_ok_iff, runtimeBinary_iff]
  · cases a with
    | string bytes =>
        cases b <;> simp [binary, BinaryTyping, logical, LeftAdmissible, BinaryBody]
    | number x =>
        cases b with
        | number y =>
            cases hl : literalBinary code with
            | some operation =>
                cases evaluated : operation.eval x.value y.value <;>
                  simp [binary, BinaryTyping, logical, LeftAdmissible, BinaryBody,
                    NumericTyping, hl, evaluated, Except.mapError, eq_comm]
            | none =>
                simp [binary, BinaryTyping, logical, LeftAdmissible, BinaryBody,
                  NumericTyping, hl, bind_ok_iff, mobile_iff]
                apply exists_congr; intro left
                apply and_congr_right; intro _
                apply exists_congr; intro right
                apply and_congr_right; intro _
                simp only [← common_iff, ← runtimeBinary_iff]
                cases hc : common left right <;> simp
        | string bytes =>
            simp [binary, BinaryTyping, logical, LeftAdmissible, BinaryBody, runtimeChoice_iff]
        | runtime type expression =>
            by_cases integral : x.value.den = 1
            · cases ht : integerType type with
              | true => simp [binary, BinaryTyping, logical, LeftAdmissible, BinaryBody, integral, ht, runtimeChoice_iff]
              | false => cases type <;> simp [binary, BinaryTyping, logical, LeftAdmissible, BinaryBody, integral, ht]
            · simp [binary, BinaryTyping, logical, LeftAdmissible, BinaryBody, integral]
    | runtime type expression =>
        cases b with
        | number value =>
            cases allowed : permittedOnLeft code type <;>
              cases integer : integerType type <;>
              by_cases integral : value.value.den = 1 <;>
              simp [binary, BinaryTyping, logical, LeftAdmissible, BinaryBody,
                allowed, integer, integral, runtimeChoice_iff]
        | string bytes =>
            cases allowed : permittedOnLeft code type <;>
              simp [binary, BinaryTyping, logical, LeftAdmissible, BinaryBody, allowed, runtimeChoice_iff]
        | runtime other right =>
            cases allowed : permittedOnLeft code type <;>
              simp [binary, BinaryTyping, logical, LeftAdmissible, BinaryBody, allowed, runtimeChoice_iff]

end Solidity.Frontend.Inference
