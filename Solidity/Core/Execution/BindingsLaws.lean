/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Bindings

namespace Solidity.Execution
open Aggregates (Result)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem Locals.declare_shape {locals after : Locals} {binder : Binder} {value : Option Value}
    (declared : Locals.declare locals binder value = .ok after) :
    ∃ scope rest cell, locals = scope :: rest ∧ after = ((binder.id, cell) :: scope) :: rest ∧
      cell.type = binder.type := by
  cases locals with
  | nil =>
      cases value with
      | none => simp [Locals.declare, Locals.find] at declared
      | some source =>
          by_cases same : source.type = binder.type <;> simp [Locals.declare, Locals.find, same] at declared
  | cons scope rest =>
      by_cases duplicate : (Locals.find (scope :: rest) binder.id).isSome = true
      · simp [Locals.declare, duplicate] at declared
      · cases value with
        | none =>
            simp only [Locals.declare, duplicate, Bind.bind, Except.bind, Pure.pure, Except.pure] at declared
            cases declared
            exact ⟨scope, rest, ⟨binder.type, none⟩, rfl, rfl, rfl⟩
        | some source =>
            by_cases same : source.type = binder.type
            · simp only [Locals.declare, duplicate, same, Bind.bind, Except.bind, Pure.pure, Except.pure] at declared
              cases declared
              exact ⟨scope, rest, ⟨binder.type, some (same ▸ source.value)⟩, rfl, rfl, rfl⟩
            · simp [Locals.declare, duplicate, same] at declared

theorem Locals.declare_frames_other {locals after : Locals} {other : LocalId}
    (different : binder.id ≠ other)
    (declared : locals.declare binder value = .ok after) : after.find other = locals.find other := by
  rcases Locals.declare_shape declared with ⟨scope, rest, cell, rfl, rfl, _⟩
  simp only [Locals.find, Scope.find, different, ↓reduceIte]

theorem Locals.declare_type {locals after : Locals}
    (declared : locals.declare binder value = .ok after) : after.typeOf binder.id = .ok binder.type := by
  rcases Locals.declare_shape declared with ⟨scope, rest, cell, rfl, rfl, same⟩
  simp [Locals.typeOf, Locals.find, Scope.find, same]

end Solidity.Execution
