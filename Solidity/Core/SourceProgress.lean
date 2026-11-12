/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.SourceExpression

namespace Solidity.Static
open Core

/-- Accepted pure scalar expressions can return a value or panic. Static
rejection and unsupported-model markers cannot arise during their execution. -/
def RuntimeResult (result : Except ConversionFailure α) : Prop :=
  result ≠ .error .rejected ∧ result ≠ .error .unsupported

theorem RuntimeResult.ok (value : α) : RuntimeResult (.ok value) := by simp [RuntimeResult]

theorem RuntimeResult.lift (result : Core.Result α) : RuntimeResult (result.mapError ConversionFailure.panic) := by
  cases result <;> simp [RuntimeResult, Except.mapError]

theorem RuntimeResult.bind (result : Except ConversionFailure α) (next : α → Except ConversionFailure β)
    (first : RuntimeResult result) (rest : ∀ value, RuntimeResult (next value)) :
    RuntimeResult (result >>= next) := by
  cases result with
  | ok value => exact rest value
  | error error =>
      change RuntimeResult (.error error : Except ConversionFailure β)
      simpa [RuntimeResult] using first

theorem RuntimeResult.coerce (allowed : Allowed mode source target) (value : source.Value) :
    RuntimeResult (coerce source target value) :=
  ⟨coerce_ne_rejected _ _ _, coerce_supported _ _ _ (allowed_coercible _ _ _ allowed)⟩

theorem SourceExpr.eval_runtime (env : Environment context) (mode : ArithmeticMode) (order : OperandOrder)
    (expression : SourceExpr context type) : RuntimeResult (expression.eval env mode order) := by
  induction expression with
  | literal => exact .ok _
  | read => exact .ok _
  | cast conversion allowed arg ih =>
      simp only [eval]
      exact .bind _ _ ih (fun value => .coerce allowed value)
  | unary operation arg ih =>
      simp only [eval]
      exact .bind _ _ ih (fun value => .lift _)
  | binary operation left right il ir =>
      cases operation
      case and =>
        simp only [eval]
        apply RuntimeResult.bind _ _ il
        intro value
        cases value
        · exact .ok _
        · exact ir
      case or =>
        simp only [eval]
        apply RuntimeResult.bind _ _ il
        intro value
        cases value
        · exact ir
        · exact .ok _
      all_goals
        cases order <;> simp only [eval]
        all_goals first
          | exact .bind _ _ il (fun _ => .bind _ _ ir (fun _ => .lift _))
          | exact .bind _ _ ir (fun _ => .bind _ _ il (fun _ => .lift _))
  | ite test yes no it iy ino =>
      simp only [eval]
      apply RuntimeResult.bind _ _ it
      intro value
      cases value
      · exact ino
      · exact iy
  | wrap identity base arg ih =>
      simp only [eval]
      exact .bind _ _ ih (fun _ => .ok _)
  | unwrap identity base arg ih =>
      simp only [eval]
      exact .bind _ _ ih (fun _ => .ok _)

theorem SourceExpr.failure_is_panic (env : Environment context) (mode : ArithmeticMode) (order : OperandOrder)
    (expression : SourceExpr context type) (failed : expression.eval env mode order = .error error) :
    ∃ bytes, error = .panic bytes := by
  have valid := expression.eval_runtime env mode order
  rw [failed] at valid
  cases error with
  | rejected => exact False.elim (valid.1 rfl)
  | unsupported => exact False.elim (valid.2 rfl)
  | panic bytes => exact ⟨bytes, rfl⟩

end Solidity.Static
