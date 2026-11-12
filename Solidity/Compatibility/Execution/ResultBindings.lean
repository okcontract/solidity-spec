/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.ReturnTransfers
import Solidity.Compatibility.Execution.LocalEffects

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def resultScope (base : Nat) : Core.Env types → Scope
  | .nil => []
  | .cons (rest := types) (type := type) value rest =>
      (2 * (base + types.length), ⟨SType.ofCore type, some (scalarValue type value)⟩) :: resultScope base rest

theorem resultScope_outside (environment : Core.Env types) (base id : Nat)
    (outside : 2 * (base + types.length) ≤ id) : Scope.find (resultScope base environment) id = none := by
  induction environment with
  | nil => rfl
  | @cons types type value rest ih =>
      have different : 2 * (base + types.length) ≠ id := by simp only [List.length_cons] at outside; omega
      simp only [resultScope, Scope.find, different, ↓reduceIte]
      exact ih (by simp only [List.length_cons] at outside; omega)

theorem resultScope_reverse_find (environment : Core.Env types) (base id : Nat) :
    Scope.find (resultScope base environment).reverse id = Scope.find (resultScope base environment) id := by
  induction environment with
  | nil => rfl
  | @cons types type value rest ih =>
      simp only [resultScope, List.reverse_cons, scope_find_append, ih]
      by_cases same : 2 * (base + types.length) = id
      · subst id
        rw [resultScope_outside rest base (2 * (base + types.length)) (Nat.le_refl _)]
        simp [Scope.find]
      · simp [Scope.find, same]

theorem resultScope_odd (environment : Core.Env types) (base index : Nat) :
    Scope.find (resultScope base environment) (2 * index + 1) = none := by
  induction environment with
  | nil => rfl
  | @cons types type value rest ih =>
      simp only [resultScope, Scope.find, even_ne_odd, ↓reduceIte]
      exact ih

theorem resultScope_frame (environment : Core.Env results)
    (caller : Core.Env vars) (frame : FrameEnv (scope :: outer) caller) :
    FrameEnv (((resultScope vars.length environment).reverse ++ scope) :: outer) (environment.append caller) := by
  have canonical : FrameEnv ((resultScope vars.length environment ++ scope) :: outer) (environment.append caller) := by
    induction environment with
    | nil => simpa only [resultScope, List.nil_append, Core.Env.append] using frame
    | @cons types type value rest ih =>
        have extended := FrameEnv.prepend ih value
        simpa only [resultScope, List.cons_append, Core.Env.append, List.length_append, Nat.add_comm] using extended
  apply FrameEnv.of_even_find canonical ?_ (by simp)
  intro index
  simp only [Locals.find, scope_find_append, resultScope_reverse_find]

/-- Real result declarations use their shifted even IDs above the caller's
live environment. Their order is the declared source component order. -/
theorem declareValues_resultScope (backend : Backend σ Keys) (registry : Registry)
    (environment : Core.Env types) (base : Nat) (state : MachineState σ)
    (scope : Scope) (outer : Locals) (shape : state.locals = scope :: outer)
    (fresh : ∀ index, index < types.length → state.locals.find (2 * (base + index)) = none) :
    Machine.declareValues backend registry legacyLimits state (resultBinders base types) (environmentPacket environment) =
      .ok {state with locals := ((resultScope base environment).reverse ++ scope) :: outer} := by
  induction environment generalizing state scope outer with
  | nil =>
      simp only [Machine.declareValues, resultBinders, environmentPacket, resultScope,
        List.reverse_nil, List.nil_append, Except.ok.injEq]
      rw [← shape]
  | @cons types type value rest ih =>
      let next : MachineState σ := {state with locals :=
        ((2 * (base + types.length), ⟨SType.ofCore type, some (scalarValue type value)⟩) :: scope) :: outer}
      have first := declare_write_scalar backend registry state scope outer shape (2 * (base + types.length))
        type value (fresh types.length (by simp))
      simp only [scalar] at first
      have nextFresh : ∀ index, index < types.length → next.locals.find (2 * (base + index)) = none := by
        intro index bound
        have different : 2 * (base + types.length) ≠ 2 * (base + index) := by omega
        simp only [next, Locals.find, Scope.find, different, ↓reduceIte]
        simpa only [shape, Locals.find] using fresh index (by simp; omega)
      have remaining := ih next
        ((2 * (base + types.length), ⟨SType.ofCore type, some (scalarValue type value)⟩) :: scope) outer rfl nextFresh
      simp only [Machine.declareValues, resultBinders, environmentPacket, Datum.asAtom, binder, except_ok_bind]
      rw [← except_bind_assoc, first, except_ok_bind]
      rw [remaining]
      simp [next, resultScope, List.reverse_cons, List.append_assoc]

theorem declareValues_results (backend : Backend σ Keys) (registry : Registry)
    (state : MachineState σ) (environment : Core.Env results) (caller : Core.Env vars)
    (frame : FrameEnv state.locals caller) :
    ∃ after,
      Machine.declareValues backend registry legacyLimits state (resultBinders vars.length results)
        (environmentPacket environment) = .ok after ∧
      FrameEnv after.locals (environment.append caller) ∧ OddFrame state.locals after.locals ∧
      after.external = state.external ∧ after.heap = state.heap ∧ after.mode = state.mode ∧
      after.materializationRemaining = state.materializationRemaining := by
  cases shape : state.locals with
  | nil => exact False.elim (frame.nonempty shape)
  | cons scope outer =>
      let after : MachineState σ := {state with locals :=
        ((resultScope vars.length environment).reverse ++ scope) :: outer}
      have current : FrameEnv (scope :: outer) caller := by simpa only [shape] using frame
      refine ⟨after, declareValues_resultScope backend registry environment vars.length state scope outer shape
        (by intro index bound; exact frame.fresh (vars.length + index) (Nat.le_add_right _ _)),
        resultScope_frame environment caller current, ?_, rfl, rfl, rfl, rfl⟩
      intro index
      simp only [after, Locals.find, scope_find_append, resultScope_reverse_find,
        resultScope_odd, Option.orElse_none]

end Solidity.Execution.Compatibility
