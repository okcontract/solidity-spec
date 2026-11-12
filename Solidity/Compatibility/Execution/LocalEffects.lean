/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Frames

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem replace_nonempty (locals : Locals) (id : LocalId) (cell : LocalCell) (nonempty : locals ≠ []) :
    locals.replace id cell ≠ [] := by
  cases locals with
  | nil => exact False.elim (nonempty rfl)
  | cons scope rest => cases found : scope.find id <;> simp [Locals.replace, found]

theorem write_nonempty (locals after : Locals) {id : LocalId} (nonempty : locals ≠ [])
    (written : locals.write id type value = .ok after) : after ≠ [] := by
  unfold Locals.write at written
  cases position : locals.find id with
  | none => simp [position] at written
  | some cell =>
      simp only [position] at written
      split at written
      · cases written
      · split at written
        · cases written
          exact replace_nonempty _ _ _ nonempty
        · cases written

theorem even_ne_odd (first second : Nat) : 2 * first ≠ 2 * second + 1 := by
  intro equal
  have parity := congrArg (fun value : Nat => value % 2) equal
  simp [Nat.add_mod] at parity

/-- Ordinary legacy variables use even IDs. The new machine's odd named-return
cells retain their exact descriptors and contents throughout those updates. -/
def OddFrame (before after : Locals) : Prop :=
  ∀ index, after.find (2 * index + 1) = before.find (2 * index + 1)

theorem OddFrame.refl (locals : Locals) : OddFrame locals locals := fun _ => rfl

theorem OddFrame.trans (first : OddFrame before middle) (second : OddFrame middle after) : OddFrame before after :=
  fun index => (second index).trans (first index)

theorem OddFrame.typeOf (frame : OddFrame before after) (index : Nat) :
    after.typeOf (2 * index + 1) = before.typeOf (2 * index + 1) := by
  unfold Locals.typeOf
  rw [frame index]

theorem OddFrame.declare_even (index : Nat) (declaration : Binder) (identifier : declaration.id = 2 * index)
    (declared : before.declare declaration value = .ok after) : OddFrame before after := by
  intro observed
  apply Locals.declare_frames_other ?_ declared
  rw [identifier]
  exact even_ne_odd index observed

theorem OddFrame.write_even (index : Nat)
    (written : before.write (2 * index) type value = .ok after) : OddFrame before after := by
  intro observed
  exact Locals.write_frames_other (even_ne_odd index observed) written

theorem OddFrame.prepend_even (scope : Scope) (outer : Locals) (index : Nat) (cell : LocalCell) :
    OddFrame (scope :: outer) (((2 * index, cell) :: scope) :: outer) := by
  intro observed
  simp [Locals.find, Scope.find, even_ne_odd index observed]

end Solidity.Execution.Compatibility
