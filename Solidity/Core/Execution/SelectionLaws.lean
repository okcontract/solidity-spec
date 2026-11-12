/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.MachineHelpers

/-! Operand selection is specified by removing one occurrence from a list,
independently of the executable choice number. Repeated selections preserve
the complete multiset, including distinct indexed occurrences of equal source
expressions; no evaluation may be duplicated or silently omitted. -/
namespace Solidity.Execution.Machine

def Selected (items : List α) (value : α) (rest : List α) : Prop :=
  ∃ before after, items = before ++ value :: after ∧ rest = before ++ after

theorem pick_sound (picked : pick choice items = some (value, rest)) :
    Selected items value rest := by
  cases items with
  | nil => simp [pick] at picked
  | cons head tail =>
      let index := choice % (tail.length + 1)
      have bound : index < (head :: tail).length := Nat.mod_lt _ (by simp)
      simp only [pick, List.splitAt_eq] at picked
      change (match (head :: tail).drop index with
        | [] => none
        | chosen :: after => some (chosen, (head :: tail).take index ++ after)) = some (value, rest) at picked
      rw [List.drop_eq_getElem_cons bound] at picked
      cases Option.some.inj picked
      refine ⟨(head :: tail).take index, (head :: tail).drop (index + 1), ?_, rfl⟩
      simpa only [List.drop_eq_getElem_cons bound] using (List.take_append_drop index (head :: tail)).symm

theorem pick_prefix (before : List α) (value : α) (after : List α) :
    pick before.length (before ++ value :: after) = some (value, before ++ after) := by
  have bound : before.length < (before ++ value :: after).length := by simp
  cases before with
  | nil => simp [pick]
  | cons head tail =>
      simp only [List.cons_append, pick, List.splitAt_eq]
      simp only [List.cons_append, List.length_cons] at bound
      simp only [List.length_cons]
      rw [Nat.mod_eq_of_lt bound]
      simp

theorem pick_complete (selected : Selected items value rest) :
    ∃ choice, pick choice items = some (value, rest) := by
  obtain ⟨before, after, rfl, rfl⟩ := selected
  exact ⟨before.length, pick_prefix before value after⟩

theorem selected_iff_pick : Selected items value rest ↔
    ∃ choice, pick choice items = some (value, rest) :=
  ⟨pick_complete, fun ⟨_, picked⟩ => pick_sound picked⟩

theorem pick_member_complete (member : value ∈ items) :
    ∃ choice rest, pick choice items = some (value, rest) := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp member
  exact ⟨before.length, before ++ after, pick_prefix before value after⟩

theorem Selected.perm (selected : Selected items value rest) :
    items.Perm (value :: rest) := by
  obtain ⟨before, after, rfl, rfl⟩ := selected
  exact List.perm_middle

theorem Selected.length (selected : Selected items value rest) :
    items.length = rest.length + 1 := by
  have same := selected.perm.length_eq
  simpa only [List.length_cons, Nat.add_comm 1] using same

theorem Selected.member (selected : Selected items value rest) : value ∈ items :=
  selected.perm.symm.subset (by simp)

inductive SelectionTrace : List α → List α → List α → Prop where
  | nil (items : List α) : SelectionTrace items [] items
  | cons : Selected items value middle → SelectionTrace middle values rest →
      SelectionTrace items (value :: values) rest

theorem SelectionTrace.perm (trace : SelectionTrace items values rest) :
    items.Perm (values ++ rest) := by
  induction trace with
  | nil => exact List.Perm.refl _
  | cons selected _ ih => exact selected.perm.trans (ih.cons _)

theorem SelectionTrace.length (trace : SelectionTrace items values rest) :
    items.length = values.length + rest.length := by
  simpa only [List.length_append] using trace.perm.length_eq

theorem SelectionTrace.complete (trace : SelectionTrace items values []) :
    items.Perm values := by simpa only [List.append_nil] using trace.perm

/-- Every ordering of the original occurrences has a finite sequence of
permitted selections. Each selection has an executable choice by
`pick_complete`; this is not a fixed global left/right traversal. -/
theorem selectionTrace_of_perm (permuted : items.Perm values) :
    SelectionTrace items values [] := by
  induction values generalizing items with
  | nil =>
      have empty : items = [] := List.eq_nil_of_length_eq_zero (by simpa using permuted.length_eq)
      subst items
      exact .nil []
  | cons value values ih =>
      have member : value ∈ items := permuted.symm.subset (by simp)
      obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp member
      have selected : Selected (before ++ value :: after) value (before ++ after) := ⟨before, after, rfl, rfl⟩
      have tail := (selected.perm.symm.trans permuted).cons_inv
      exact .cons selected (ih tail)

theorem insertOrdered_perm (item : Nat × α) (items : List (Nat × α)) :
    (insertOrdered item items).Perm (item :: items) := by
  induction items with
  | nil => exact List.Perm.refl _
  | cons head tail ih =>
      simp only [insertOrdered]
      split
      · exact List.Perm.refl _
      · exact (ih.cons head).trans (.swap _ _ _)

theorem orderPairs_perm (items : List (Nat × α)) : (orderPairs items).Perm items := by
  induction items with
  | nil => exact List.Perm.refl _
  | cons item items ih => exact (insertOrdered_perm item (orderPairs items)).trans (ih.cons item)

private theorem insertOrdered_sorted (item : Nat × α)
    (sorted : items.Pairwise (fun a b : Nat × α => a.1 ≤ b.1)) :
    (insertOrdered item items).Pairwise (fun a b => a.1 ≤ b.1) := by
  induction items with
  | nil => simp [insertOrdered]
  | cons head tail ih =>
      obtain ⟨headBefore, tailSorted⟩ := List.pairwise_cons.mp sorted
      simp only [insertOrdered]
      split
      · rename_i before
        apply List.pairwise_cons.mpr
        refine ⟨?_, sorted⟩
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact before
        · exact Nat.le_trans before (headBefore _ member)
      · rename_i after
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih tailSorted⟩
        intro value member
        rcases List.mem_cons.mp ((insertOrdered_perm item tail).subset member) with rfl | member
        · omega
        · exact headBefore _ member

theorem orderPairs_sorted (items : List (Nat × α)) :
    (orderPairs items).Pairwise (fun a b => a.1 ≤ b.1) := by
  induction items with
  | nil => simp [orderPairs]
  | cons item items ih => exact insertOrdered_sorted item ih

private theorem indexed_sorted (values : List α) (start : Nat) :
    ((values.zipIdx start).map (fun (value, index) => (index, value))).Pairwise
      (fun a b => a.1 ≤ b.1) := by
  induction values generalizing start with
  | nil => simp
  | cons value values ih =>
      simp only [List.zipIdx_cons, List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih (start + 1)⟩
      intro pair member
      obtain ⟨source, found, rfl⟩ := List.mem_map.mp member
      have bound := List.le_snd_of_mem_zipIdx found
      exact Nat.le_trans (Nat.le_succ start) bound

private theorem indexed_key_unique (values : List α) (a b : Nat × α)
    (foundA : a ∈ (values.zipIdx).map (fun (value, index) => (index, value)))
    (foundB : b ∈ (values.zipIdx).map (fun (value, index) => (index, value)))
    (same : a.1 = b.1) : a = b := by
  have sourceA : (a.2, a.1) ∈ values.zipIdx := by
    obtain ⟨⟨value, index⟩, found, equal⟩ := List.mem_map.mp foundA
    cases equal
    exact found
  have sourceB : (b.2, b.1) ∈ values.zipIdx := by
    obtain ⟨⟨value, index⟩, found, equal⟩ := List.mem_map.mp foundB
    cases equal
    exact found
  have readA := List.mem_zipIdx_iff_getElem?.mp sourceA
  have readB := List.mem_zipIdx_iff_getElem?.mp sourceB
  have data : a.2 = b.2 := Option.some.inj (readA.symm.trans (by simpa only [same] using readB))
  exact Prod.ext same data

/-- The actual insertion sorter restores source positions for every operand
schedule. The premise concerns the independently indexed result occurrences,
not successful execution or a desired observation. -/
theorem orderPairs_permutation_zipIdx {values : List α} {items : List (Nat × α)}
    (permuted : items.Perm ((values.zipIdx).map (fun (value, index) => (index, value)))) :
    orderPairs items = (values.zipIdx).map (fun (value, index) => (index, value)) := by
  have represented := (orderPairs_perm items).trans permuted
  apply List.Perm.eq_of_pairwise (le := fun a b : Nat × α => a.1 ≤ b.1)
    (fun a b foundA foundB before after =>
      indexed_key_unique values a b (represented.subset foundA) foundB (Nat.le_antisymm before after))
    (orderPairs_sorted items) (indexed_sorted values 0) represented

theorem ordered_permutation_zipIdx {values : List α} {items : List (Nat × α)}
    (permuted : items.Perm ((values.zipIdx).map (fun (value, index) => (index, value)))) :
    ordered items = values := by
  unfold ordered
  rw [orderPairs_permutation_zipIdx permuted]
  simpa only [List.map_map, Function.comp_def] using List.zipIdx_map_fst 0 values

end Solidity.Execution.Machine
