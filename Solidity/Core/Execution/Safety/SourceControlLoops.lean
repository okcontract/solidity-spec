/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Admission

/-! Loop nesting is inspected by admission only to decide whether a break or
continue has an enclosing loop. Positive depths are interchangeable, including
inside nested loops and lexical/unchecked blocks. -/
namespace Solidity.Execution.Safety.SourceControl
open Static Aggregates Admission

theorem checkStatement_loops (positive : (0 < loopsA) ↔ (0 < loopsB)) :
    checkStatement registry fuel context returns loopsA unchecked (statement : Stmt Key) =
      checkStatement registry fuel context returns loopsB unchecked statement := by
  induction fuel generalizing context returns loopsA loopsB unchecked statement with
  | zero => rfl
  | succ fuel ih =>
      have current : ∀ context returns unchecked (statement : Stmt Key),
          checkStatement registry fuel context returns loopsA unchecked statement =
            checkStatement registry fuel context returns loopsB unchecked statement :=
        fun context returns unchecked statement => ih positive
      have nested : ∀ context returns unchecked (statement : Stmt Key),
          checkStatement registry fuel context returns (loopsA+1) unchecked statement =
            checkStatement registry fuel context returns (loopsB+1) unchecked statement :=
        fun context returns unchecked statement => ih (by omega)
      have flags : decide (0 < loopsA) = decide (0 < loopsB) := by
        by_cases first : 0 < loopsA
        · have second := positive.mp first
          simp [first,second]
        · have second : ¬0 < loopsB := fun yes => first (positive.mpr yes)
          simp [first,second]
      clear ih positive
      cases statement
      case return_ value => cases value <;> rfl
      all_goals simp only [checkStatement]
      all_goals first
        | rfl
        | solve | simp only [current]
        | solve | simp only [nested]
        | solve | simp only [current,nested]
        | solve | simp only [flags]

end Solidity.Execution.Safety.SourceControl
