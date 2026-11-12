/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Admission

namespace Solidity.Execution.Admission
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem Context.join_assigned (left right : Context) (id : LocalId) :
    id ∈ (left.join right).assigned ↔ id ∈ left.assigned ∨ id ∈ right.assigned := by
  simp [Context.join]

theorem Context.join_scopes (left right : Context) :
    (left.join right).scopes = left.scopes := rfl

/-- Successful local admission supplies the declared type and, for a read,
actual definite-assignment evidence in the incoming context. -/
theorem Context.local_checked (context : Context) (id : LocalId) (type : Static.SType) (read : Bool)
    (checked : context.local id type read = .ok ()) :
    ∃ binder, context.find id = some binder ∧ binder.type = type ∧
      (read = true → id ∈ context.assigned) := by
  cases found : context.find id with
  | none => simp [Context.local, found] at checked
  | some binder =>
      cases equal : binder.type == type with
      | false => simp [Context.local, found, ensure, equal] at checked
      | true =>
          have same : binder.type = type := by simpa using equal
          refine ⟨binder, rfl, same, ?_⟩
          intro reading
          by_cases assigned : id ∈ context.assigned
          · exact assigned
          · have absent : context.assigned.contains id = false := by simp [assigned]
            cases order : context.orderIndependent <;> cases calls : context.unresolvedCalls <;>
              simp_all [Context.local, ensure]

theorem independent_checked (checked : independent incoming check = .ok result) :
    ∃ after, check {incoming with orderIndependent := true} = .ok after ∧
      result = {after with orderIndependent := incoming.orderIndependent} := by
  unfold independent at checked
  cases action : check {incoming with orderIndependent := true} with
  | error failure => simp [action] at checked
  | ok after =>
      simp only [action, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at checked
      exact ⟨after, rfl, checked.symm⟩

private theorem fold_checked (check : α → Aggregates.Result Context) (values : List α)
    (initial result : Context)
    (checked : values.foldlM (fun accumulated value => do
      let after ← check value
      return accumulated.join after) initial = .ok result) :
    result.scopes = initial.scopes ∧
      (∀ id ∈ initial.assigned, id ∈ result.assigned) ∧
      (∀ value ∈ values, ∃ after, check value = .ok after ∧
        ∀ id ∈ after.assigned, id ∈ result.assigned) := by
  induction values generalizing initial result with
  | nil =>
      simp only [List.foldlM, Pure.pure, Except.pure, Except.ok.injEq] at checked
      subst result
      exact ⟨rfl, fun _ member => member, by simp⟩
  | cons head tail induction =>
      cases action : check head with
      | error failure => simp [List.foldlM, action] at checked
      | ok after =>
          simp only [List.foldlM, action, Bind.bind, Except.bind] at checked
          obtain ⟨scopes, ready, children⟩ := induction _ _ checked
          refine ⟨scopes, ?_, ?_⟩
          · intro id member
            exact ready id ((Context.join_assigned _ _ _).mpr (.inl member))
          · intro value member
            rcases List.mem_cons.mp member with equal | member
            · subst value
              refine ⟨after, action, ?_⟩
              intro id member
              exact ready id ((Context.join_assigned _ _ _).mpr (.inr member))
            · exact children value member

/-- Every admitted eager child was checked against the same entry readiness,
independently of where it occurs in the group or which child runs first. -/
theorem independentChildren_each
    (checked : independentChildren incoming values check = .ok result)
    (member : value ∈ values) :
    ∃ after, check {incoming with orderIndependent := true} value = .ok after := by
  obtain ⟨_, _, children⟩ := fold_checked
    (fun value => independent incoming (fun context => check context value)) values incoming result checked
  obtain ⟨after, child, _⟩ := children value member
  obtain ⟨raw, action, _⟩ := independent_checked child
  exact ⟨raw, action⟩

theorem checkExpressions_each
    (checked : checkExpressions registry (fuel + 1) incoming values = .ok result)
    (member : value ∈ values) :
    ∃ after, checkExpression registry fuel {incoming with orderIndependent := true} value = .ok after := by
  exact independentChildren_each checked member

/-- Joining completed children cannot manufacture a lexical declaration. -/
theorem independentChildren_scopes
    (checked : independentChildren incoming values check = .ok result) :
    result.scopes = incoming.scopes := by
  exact (fold_checked
    (fun value => independent incoming (fun context => check context value)) values incoming result checked).1

/-- Every completed child's guaranteed assignments are available after the
whole group completes, even though no sibling relied on them during checking. -/
theorem independentChildren_assigned
    (id : LocalId)
    (checked : independentChildren incoming values check = .ok result)
    (member : value ∈ values)
    (child : independent incoming (fun context => check context value) = .ok after)
    (assigned : id ∈ after.assigned) : id ∈ result.assigned := by
  obtain ⟨_, _, children⟩ := fold_checked
    (fun value => independent incoming (fun context => check context value)) values incoming result checked
  obtain ⟨actual, success, ready⟩ := children value member
  rw [child] at success
  cases Except.ok.inj success
  exact ready id assigned

end Solidity.Execution.Admission
