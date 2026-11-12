/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.MachineHelpers

namespace Solidity.Execution.Machine

private theorem orderPairs_append_low (items : List (Nat × α)) (low : Nat × α)
    (lowest : ∀ item ∈ items, low.1 < item.1) :
    orderPairs (items ++ [low]) = low :: orderPairs items := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      have smaller := lowest item (by simp)
      have tail : ∀ next ∈ items, low.1 < next.1 := fun next found => lowest next (by simp [found])
      simp only [List.cons_append, orderPairs, ih tail, insertOrdered]
      simp [Nat.not_le.mpr smaller]

private theorem zipIdx_index_ge (values : List α) (start : Nat) (item : Nat × α)
    (found : item ∈ (values.zipIdx start).map (fun (value, index) => (index, value))) :
    start ≤ item.1 := by
  induction values generalizing start with
  | nil => simp at found
  | cons value values ih =>
      simp only [List.zipIdx_cons, List.map_cons, List.mem_cons] at found
      rcases found with same | found
      · cases same; exact Nat.le_refl _
      · have tail := ih (start + 1) found; omega

theorem orderPairs_reverse_zipIdx (values : List α) (start : Nat) :
    orderPairs ((values.zipIdx start).map (fun (value, index) => (index, value))).reverse =
      (values.zipIdx start).map (fun (value, index) => (index, value)) := by
  induction values generalizing start with
  | nil => rfl
  | cons value values ih =>
      simp only [List.zipIdx_cons, List.map_cons, List.reverse_cons]
      rw [orderPairs_append_low]
      · rw [ih]
      · intro item found
        have present := List.mem_reverse.mp found
        have bound := zipIdx_index_ge values (start + 1) item present
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self start) bound

theorem ordered_reverse_zipIdx (values : List α) (start : Nat := 0) :
    ordered ((values.zipIdx start).map (fun (value, index) => (index, value))).reverse = values := by
  rw [ordered, orderPairs_reverse_zipIdx]
  induction values generalizing start with
  | nil => rfl
  | cons value values ih => simpa using ih (start + 1)

end Solidity.Execution.Machine
