/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Syntax

namespace Solidity.Execution
open Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem typesList_ofList (types : List SType) : typesList (Types.ofList types) = types := by
  induction types with
  | nil => rfl
  | cons type rest ih => simp [Types.ofList, typesList, ih]

theorem FunctionSignature.accepts_iff (actual expected : FunctionSignature) :
    actual.accepts expected = true ↔ actual.parameters = expected.parameters ∧
      actual.returns = expected.returns ∧ Mutability.Allows actual.mutability expected.mutability := by
  simp [FunctionSignature.accepts, Mutability.allows_iff, and_assoc]

namespace ArgumentOrder

/-- Every destination position selects its own captured argument. This
relation has no evaluation callback or implementation-level list traversal. -/
inductive Selects (source : List α) : List Nat → List α → Prop where
  | nil : Selects source [] []
  | cons (entry : source[index]? = some value) (rest : Selects source order values) :
      Selects source (index :: order) (value :: values)

def lookup (source : List α) (index : Nat) : Aggregates.Result α :=
  match source[index]? with
  | some value => .ok value
  | none => .error (.invalidContext "named argument index outside captured packet")

theorem mapM_lookup_iff (order : List Nat) (source selected : List α) :
    order.mapM (lookup source) = .ok selected ↔ Selects source order selected := by
  induction order generalizing selected with
  | nil =>
      constructor
      · intro same; cases same; exact .nil
      · intro entries; cases entries; rfl
  | cons index rest ih =>
      rw [List.mapM_cons]
      cases entry : source[index]? with
      | none =>
          constructor
          · simp [lookup, entry]
          · intro entries; cases entries with | cons observed _ => rw [entry] at observed; cases observed
      | some value =>
          simp only [lookup, entry, Bind.bind, Except.bind, Pure.pure, Except.pure]
          cases selected with
          | nil =>
              constructor
              · intro finished
                cases tail : rest.mapM (lookup source) with
                | error failure => simp [tail] at finished
                | ok values => simp [tail] at finished
              · intro entries; cases entries
          | cons head tail =>
              constructor
              · intro finished
                cases result : rest.mapM (lookup source) with
                | error failure => simp [result] at finished
                | ok values =>
                    simp only [result] at finished
                    cases finished
                    exact .cons entry ((ih _).mp result)
              · intro entries
                cases entries with
                | cons observed later =>
                    have same : head = value := Option.some.inj (observed.symm.trans entry)
                    subst head
                    rw [(ih tail).mpr later]

theorem select_iff (order : List Nat) (source selected : List α) :
    select order source = .ok selected ↔ Valid order source.length ∧ Selects source order selected := by
  unfold select
  cases allowed : valid order source.length with
  | false =>
      simp only [Bool.not_false, ↓reduceIte, Bind.bind, Except.bind]
      constructor
      · intro impossible; cases impossible
      · rintro ⟨admitted, _⟩
        have := (valid_iff _ _).mpr admitted
        rw [allowed] at this
        cases this
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure]
      change order.mapM (lookup source) = .ok selected ↔ Valid order source.length ∧ Selects source order selected
      rw [mapM_lookup_iff]
      exact ⟨fun entries => ⟨(valid_iff _ _).mp allowed, entries⟩, And.right⟩

theorem Selects.length (selection : Selects source order selected) : selected.length = order.length := by
  induction selection with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem select_length (selected : select order source = .ok values) : values.length = source.length := by
  rcases (select_iff _ _ _).mp selected with ⟨allowed, entries⟩
  exact entries.length.trans allowed.1

theorem Selects.entry {source selected : List α} {order : List Nat} {index original : Nat} {result : α}
    (selection : Selects source order selected)
    (position : order[index]? = some original) (value : selected[index]? = some result) :
    source[original]? = some result := by
  induction selection generalizing index with
  | nil => simp at position
  | cons observed later ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at position value
          subst original; subst result; exact observed
      | succ index => exact ih position value

theorem select_entry {source values : List α} {order : List Nat} {index original : Nat} {result : α}
    (selected : select order source = .ok values)
    (position : order[index]? = some original) (value : values[index]? = some result) :
    source[original]? = some result :=
  ((select_iff _ _ _).mp selected).2.entry position value

end ArgumentOrder
end Solidity.Execution
