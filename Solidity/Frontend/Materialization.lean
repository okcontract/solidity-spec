/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Inference

namespace Solidity.Frontend.Inference
open Core Static Lexical

/-- Independent conversion elaboration rules. Numeric representation is computed
only after literal permission; runtime casts carry the declarative Allowed
relation, not a premise saying the cast checker returned true. -/
inductive Materializes (conversion : ConversionMode) :
    Term context → (type : SType) → SourceExpr context type → Prop where
  | number : type.scalarSupported = true → NumberConverts conversion value type →
      numberValue value type = .ok word →
      Materializes conversion (.number value) type (.literal word)
  | string : StringConverts bytes (.fixedBytes width) → conversion ≠ .explicit .payable →
      Materializes conversion (.string bytes) (.fixedBytes width) (.literal (stringWord width bytes))
  | runtime (allowed : Allowed conversion source type) :
      source.scalarSupported = true → type.scalarSupported = true →
      Materializes conversion (.runtime source expression) type (.cast conversion allowed expression)

section Materialization

variable {context : Context} {conversion : ConversionMode} {term : Term context} {type : SType}
  {expression : SourceExpr context type}

theorem materialize_complete (valid : Materializes conversion term type expression) :
    materialize conversion term type = .ok expression := by
  cases valid with
  | number supported allowed value =>
      simp [materialize, convertNumber, Except.map, supported, (numberConverts_iff _ _ _).mpr allowed, value]
  | string allowed ordinary =>
      simp [materialize, (stringConverts_iff _ _).mpr allowed, ordinary]
  | runtime allowed source target =>
      simp [materialize, source, target, (allows_iff _ _ _).mpr allowed]

theorem materialize_sound (checked : materialize conversion term type = .ok expression) :
    Materializes conversion term type expression := by
  cases term with
  | number value =>
      simp only [materialize, convertNumber] at checked
      split at checked
      next => cases checked
      next supported =>
        have support : type.scalarSupported = true := by simpa using supported
        split at checked
        next allowed =>
          cases hv : numberValue value type with
          | error error => simp [hv, Except.map] at checked
          | ok word =>
              simp [hv, Except.map] at checked; subst expression
              exact .number support ((numberConverts_iff _ _ _).mp allowed) hv
        next => cases checked
  | string bytes =>
      simp only [materialize] at checked
      split at checked
      next allowed =>
        have parts := (Bool.and_eq_true _ _).mp allowed
        have ordinary : conversion ≠ .explicit .payable := by simpa using parts.2
        cases type <;> simp only at checked <;> try cases checked
        rename_i width
        exact .string ((stringConverts_iff _ _).mp parts.1) ordinary
      next => cases checked
  | runtime source arg =>
      simp only [materialize] at checked
      split at checked
      next => cases checked
      next supported =>
        have support : source.scalarSupported = true ∧ type.scalarSupported = true := by simpa using supported
        split at checked
        next allowed =>
          cases checked
          exact .runtime ((allows_iff _ _ _).mp allowed) support.1 support.2
        next => cases checked

theorem materialize_iff : materialize conversion term type = .ok expression ↔
    Materializes conversion term type expression := ⟨materialize_sound, materialize_complete⟩

end Materialization

end Solidity.Frontend.Inference
