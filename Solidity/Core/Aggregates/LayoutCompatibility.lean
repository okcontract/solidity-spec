/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Layout
import Solidity.StorageLayout

/-! The earlier Boolean/word compiler-validation fragment uses the same byte
coordinates. Its unbounded layout is related to checked source layout only
when the latter admits the resulting frontier. -/
namespace Solidity.Aggregates
open Compiler.Validation.SolidityStorage

def legacyPosition (position : Location) : StoragePosition :=
  ⟨position.slot, position.byte⟩

def StorageType.byteSize : StorageType → Nat
  | .word => 32
  | .boolean => 1

theorem legacy_allocation_coordinates (position : Location) (type : StorageType) :
    ((legacyPosition position).align (StorageType.byteSize type),
      ((legacyPosition position).align (StorageType.byteSize type)).advance (StorageType.byteSize type) 1) =
    ((legacyPosition (position.allocate type).1), (legacyPosition (position.allocate type).2)) := by
  rcases position with ⟨slot, byte⟩
  have bound := byte.isLt
  cases type with
  | word =>
      by_cases zero : byte = 0
      · subst byte; simp [legacyPosition, StoragePosition.align,
          StoragePosition.advance, StorageType.byteSize, Location.allocate]
      · have positive : 0 < byte.val := by
          have : byte.val ≠ 0 := fun h => zero (Fin.ext h)
          omega
        simp [legacyPosition, StoragePosition.align, StoragePosition.advance,
          StorageType.byteSize, Location.allocate, zero, show ¬byte.val + 32 ≤ 32 by omega]
  | boolean =>
      simp only [StorageType.byteSize, legacyPosition, Location.allocate,
        StoragePosition.align, show byte.val + 1 ≤ 32 by omega, ↓reduceIte]
      by_cases next : byte.val + 1 < 32
      · simp [StoragePosition.advance, next]
      · simp [StoragePosition.advance, next]

theorem legacy_allocation_checked (position : Location) (type : StorageType)
    (bounded : (legacyPosition (position.allocate type).2).endSlot < storageLimit) :
    allocateStorage (legacyPosition position) (StorageType.byteSize type) 1 = .ok
      ((legacyPosition (position.allocate type).1), (legacyPosition (position.allocate type).2)) := by
  have coordinates := legacy_allocation_coordinates position type
  have right := congrArg Prod.snd coordinates
  have left := congrArg Prod.fst coordinates
  dsimp only at right left
  have dimensions : 0 < (StorageType.byteSize type) ∧ (StorageType.byteSize type) ≤ 32 ∧ 0 < (1 : Nat) ∧
      ((1 : Nat) = 1 ∨ (StorageType.byteSize type) = 32) := by cases type <;> decide
  unfold allocateStorage
  rw [if_pos dimensions]
  dsimp only
  rw [right, if_pos bounded, left]

end Solidity.Aggregates
