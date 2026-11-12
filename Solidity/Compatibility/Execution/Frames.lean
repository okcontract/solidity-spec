/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Bindings
import Solidity.Core.Execution.BindingsLaws

namespace Solidity.Execution.Compatibility
open Core Static

variable {types : List Core.Ty} {environment : Core.Env types}
variable {locals after : Locals} {declaration : Binder}

theorem localId_equal (first : Core.Var types a) (second : Core.Var types b)
    (same : localId first = localId second) : ∃ equal : a = b, equal ▸ first = second := by
  induction first generalizing b with
  | @here types a =>
      cases second with
      | here => exact ⟨rfl, rfl⟩
      | there second =>
          have different := Nat.ne_of_gt (localId_lt second)
          exact False.elim (different same)
  | @there types a other first ih =>
      cases second with
      | here =>
          have different := Nat.ne_of_lt (localId_lt first)
          exact False.elim (different same)
      | there second =>
          rcases ih second same with ⟨rfl, equal⟩
          cases equal
          exact ⟨rfl, rfl⟩

theorem environment_get_set_other (environment : Core.Env types) (first : Core.Var types a)
    (value : a.Value) (second : Core.Var types b) (different : localId first ≠ localId second) :
    (environment.set first value).get second = environment.get second := by
  induction first generalizing b with
  | here =>
      cases environment with
      | cons head rest =>
          cases second with
          | here => exact False.elim (different rfl)
          | there second => rfl
  | there first ih =>
      cases environment with
      | cons head rest =>
          cases second with
          | here => rfl
          | there second => exact ih rest value second different

theorem Represents.write (represented : Represents locals environment)
    (var : Core.Var types type) (value : type.Value)
    (written : locals.write (localId var) (SType.ofCore type)
      ⟨SType.ofCore type, scalarValue type value⟩ = .ok after) :
    Represents after (environment.set var value) := by
  intro other observed
  by_cases same : localId var = localId observed
  · rcases localId_equal var observed same with ⟨rfl, rfl⟩
    simpa only [Core.Env.get_set] using Locals.read_after_write written
  · rw [Locals.read_frames_other same written, represented observed,
      environment_get_set_other environment var value observed same]

theorem Represents.extend (represented : Represents locals environment)
    (value : type.Value)
    (newCell : after.read (2 * types.length) (SType.ofCore type) =
      .ok ⟨SType.ofCore type, scalarValue type value⟩)
    (framed : ∀ {oldType} (var : Core.Var types oldType),
      after.read (localId var) (SType.ofCore oldType) = locals.read (localId var) (SType.ofCore oldType)) :
    Represents after (Core.Env.cons value environment) := by
  intro observedType observed
  cases observed with
  | here => exact newCell
  | there var => exact (framed var).trans (represented var)

theorem Represents.enter (represented : Represents locals environment) :
    Represents locals.enter environment := by
  intro type var
  rw [Locals.read_eq_of_find_eq (Locals.find_enter locals (localId var))]
  exact represented var

theorem Represents.declare_other (represented : Represents locals environment)
    (different : ∀ {type} (var : Core.Var types type), declaration.id ≠ localId var)
    (declared : locals.declare declaration value = .ok after) : Represents after environment := by
  intro type var
  rw [Locals.read_eq_of_find_eq (Locals.declare_frames_other (different var) declared)]
  exact represented var

theorem Represents.declare_odd (represented : Represents locals environment)
    (index : Nat) (identifier : declaration.id = 2 * index + 1)
    (declared : locals.declare declaration value = .ok after) : Represents after environment := by
  intro type var
  have different : declaration.id ≠ localId var := by
    rw [identifier]
    intro equal
    have parity := congrArg (fun value : Nat => value % 2) equal
    simp [localId, Nat.add_mod] at parity
  rw [Locals.read_eq_of_find_eq (Locals.declare_frames_other different declared)]
  exact represented var

end Solidity.Execution.Compatibility
