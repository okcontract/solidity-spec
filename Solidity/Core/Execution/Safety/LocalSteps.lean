/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.ConfigurationLaws

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem scope_replace_shape (bound : Execution.Scope.find scope key = some old)
    (same : next.type = old.type) :
    Safety.Scope.environment (Execution.Scope.replace scope key next) = Safety.Scope.environment scope := by
  induction scope with
  | nil => cases bound
  | cons entry rest induction =>
      rcases entry with ⟨localId,cell⟩
      by_cases selected : localId = key
      · simp only [Execution.Scope.find,selected,↓reduceIte,Option.some.injEq] at bound
        cases bound
        simp [Execution.Scope.replace,selected,Safety.Scope.environment,same]
      · simp only [Execution.Scope.find,selected,↓reduceIte] at bound
        simpa [Execution.Scope.replace,selected,Safety.Scope.environment] using induction bound

theorem environment_replace (bound : Execution.Locals.find locals key = some old)
    (same : next.type = old.type) :
    Safety.Locals.environment (Execution.Locals.replace locals key next) = Safety.Locals.environment locals := by
  induction locals with
  | nil => cases bound
  | cons scope rest induction =>
      cases selected : scope.find key with
      | none =>
          simp only [Execution.Locals.find,selected,Option.orElse_none] at bound
          simpa [Execution.Locals.replace,selected,Safety.Locals.environment] using induction bound
      | some cell =>
          simp only [Execution.Locals.find,selected,Option.orElse_some,Option.some.injEq] at bound
          cases bound
          simp [Execution.Locals.replace,selected,Safety.Locals.environment,scope_replace_shape selected same]

theorem environment_write (written : Execution.Locals.write locals key type value = .ok after) :
    Safety.Locals.environment after = Safety.Locals.environment locals := by
  unfold Execution.Locals.write at written
  cases bound : Execution.Locals.find locals key with
  | none => simp [bound] at written
  | some cell =>
      simp only [bound] at written
      split at written
      · cases written
      · split at written
        · cases written
          exact environment_replace bound rfl
        · cases written

theorem local_write_total {localId : LocalId}
    (stateRep : StateRep program objects environment state)
    (bound : Environment.find environment localId = some type)
    (valueRep : ValueRep program state.heap objects value) (valueType : value.type = type) :
    ∃ locals, state.locals.write localId type value = .ok locals ∧
      StateRep program objects environment {state with locals} := by
  have found := bound
  rw [← stateRep.shape,environment_find] at found
  cases position : state.locals.find localId with
  | none => simp [position] at found
  | some cell =>
      simp only [position,Option.map_some,Option.some.injEq] at found
      have sourceType : value.type = cell.type := valueType.trans found.symm
      let locals := state.locals.replace localId ⟨cell.type,some (sourceType ▸ value.value)⟩
      have written : state.locals.write localId type value = .ok locals := by
        simp [Execution.Locals.write,position,found,sourceType,locals]
      refine ⟨locals,written,stateRep.heap,stateRep.cells.write valueRep written,
        (environment_write written).trans stateRep.shape,?_⟩
      intro empty
      change locals = [] at empty
      have shape := (environment_write written).trans stateRep.shape
      rw [empty] at shape
      exact stateRep.nonempty_environment shape.symm

theorem local_declare_total (stateRep : StateRep program objects environment state)
    (fresh : Environment.find environment binder.id = none)
    (valueRep : ValueRep program state.heap objects value) (valueType : value.type = binder.type) :
    ∃ locals, state.locals.declare binder (some value) = .ok locals ∧
      StateRep program objects (Environment.declare environment binder) {state with locals} := by
  have absent := fresh
  rw [← stateRep.shape,environment_find] at absent
  have noCell : state.locals.find binder.id = none := by
    cases found : state.locals.find binder.id <;> simp_all
  cases current : state.locals with
  | nil => exact False.elim (stateRep.nonempty current)
  | cons scope rest =>
      let cell : LocalCell := ⟨binder.type,some (valueType ▸ value.value)⟩
      let locals : Execution.Locals := ((binder.id,cell) :: scope) :: rest
      have absent : Execution.Locals.find (scope :: rest) binder.id = none := by simpa only [current] using noCell
      have declared : Execution.Locals.declare (scope :: rest) binder (some value) = .ok locals := by
        simp [Execution.Locals.declare,absent,valueType,locals,cell]
      have original : state.locals.declare binder (some value) = .ok locals := by simpa only [current] using declared
      refine ⟨locals,declared,stateRep.heap,stateRep.cells.declare valueRep original,?_,by simp [locals]⟩
      have shape := stateRep.shape
      rw [current] at shape
      exact congrArg (fun environment => Environment.declare environment binder) shape

end Solidity.Execution.Safety
