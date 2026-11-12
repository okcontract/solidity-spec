/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.InferenceProofs
import Solidity.Core.Registry

namespace Solidity.Frontend.Inference
open Static

/-- Validate every type supplied by the resolved input, including unused arms.
This checks consistency against a registry; constructing that registry from a
source bundle, inheritance and visibility is a caller responsibility. -/
def TypesResolved (registry : Registry) (context : Context) : Source → Prop
  | .name name => ∃ type, context name = some type ∧ WellFormed registry type
  | .number _ _ | .string _ | .bool _ => True
  | .unary _ arg => TypesResolved registry context arg
  | .binary _ a b => TypesResolved registry context a ∧ TypesResolved registry context b
  | .cast _ type arg => WellFormed registry type ∧ TypesResolved registry context arg
  | .ite test yes no => TypesResolved registry context test ∧
      TypesResolved registry context yes ∧ TypesResolved registry context no
  | .wrap identity base arg | .unwrap identity base arg =>
      WellFormed registry (.valueType identity base) ∧ TypesResolved registry context arg

def typesResolved (registry : Registry) (context : Context) : Source → Bool
  | .name name => match context name with | none => false | some type => wellFormed registry type
  | .number _ _ | .string _ | .bool _ => true
  | .unary _ arg => typesResolved registry context arg
  | .binary _ a b => typesResolved registry context a && typesResolved registry context b
  | .cast _ type arg => wellFormed registry type && typesResolved registry context arg
  | .ite test yes no => typesResolved registry context test &&
      typesResolved registry context yes && typesResolved registry context no
  | .wrap identity base arg | .unwrap identity base arg =>
      wellFormed registry (.valueType identity base) && typesResolved registry context arg

theorem typesResolved_iff (registry : Registry) (context : Context) (source : Source) :
    typesResolved registry context source = true ↔ TypesResolved registry context source := by
  induction source with
  | name name =>
      simp only [typesResolved, TypesResolved]
      cases context name <;> simp [wellFormed_iff]
  | number | string | bool => simp [typesResolved, TypesResolved]
  | unary _ _ ih => exact ih
  | binary _ _ _ ia ib => simp [typesResolved, TypesResolved, ia, ib]
  | cast _ _ _ ih => simp [typesResolved, TypesResolved, wellFormed_iff, ih]
  | ite _ _ _ it iy ino => simp [typesResolved, TypesResolved, it, iy, ino, and_assoc]
  | wrap _ _ _ ih | unwrap _ _ _ ih => simp [typesResolved, TypesResolved, wellFormed_iff, ih]

def Term.WellFormed (registry : Registry) : Term context → Prop
  | .number _ | .string _ => True
  | .runtime type _ => Static.WellFormed registry type

def Term.wellFormed (registry : Registry) : Term context → Bool
  | .number _ | .string _ => true
  | .runtime type _ => Static.wellFormed registry type

theorem Term.wellFormed_iff (registry : Registry) (term : Term context) :
    term.wellFormed registry = true ↔ term.WellFormed registry := by
  cases term <;> simp [Term.wellFormed, Term.WellFormed, Static.wellFormed_iff]

def inferResolved (registry : Registry) (context : Context) (source : Source) :
    Except StaticError (Term context) :=
  if typesResolved registry context source then
    match infer context source with
    | .error error => .error error
    | .ok term => if term.wellFormed registry then .ok term else .error .rejected
  else .error .rejected

theorem inferResolved_iff : inferResolved registry context source = .ok term ↔
    TypesResolved registry context source ∧ Elaborates context source term ∧ term.WellFormed registry := by
  rw [← typesResolved_iff, ← infer_iff, ← Term.wellFormed_iff]
  unfold inferResolved
  cases resolved : typesResolved registry context source with
  | false => simp
  | true =>
      simp only [↓reduceIte]
      cases inferred : infer context source with
      | error error => simp
      | ok result =>
          cases valid : result.wellFormed registry <;> simp_all <;> rintro rfl <;> assumption


def checkResolved (registry : Registry) (context : Context) (source : Source) (expected : SType) :
    Except StaticError (SourceExpr context expected) :=
  if wellFormed registry expected then
    match inferResolved registry context source with
    | .error error => .error error
    | .ok term => materialize .implicit term expected
  else .error .rejected

theorem checkResolved_iff : checkResolved registry context source expected = .ok expression ↔
    WellFormed registry expected ∧ ∃ term,
      (TypesResolved registry context source ∧ Elaborates context source term ∧ term.WellFormed registry) ∧
      Materializes .implicit term expected expression := by
  simp only [← inferResolved_iff, ← materialize_iff, ← wellFormed_iff, checkResolved]
  cases h : wellFormed registry expected with
  | false => simp
  | true =>
      simp only [↓reduceIte]
      cases hi : inferResolved registry context source <;> simp


theorem inferResolved_type_valid (checked : inferResolved registry context source = .ok (.runtime type expression)) :
    WellFormed registry type := (inferResolved_iff.mp checked).2.2

end Solidity.Frontend.Inference
