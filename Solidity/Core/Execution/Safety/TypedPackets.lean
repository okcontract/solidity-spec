/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.TypedState
import Solidity.Core.Execution.SelectionLaws

/-! Typed occurrence bookkeeping for the real eager collector. The syntax
predicate closes over the source environment; value representation records the
current physical heap. This relation is independent of transition success and
permits arbitrary operand schedules, heterogeneous types and nested tuples. -/
namespace Solidity.Execution.Safety.TypedPackets
open Static Aggregates

def indexed (types : List SType) : List (Nat × SType) :=
  types.zipIdx.map fun (type,index) => (index,type)

def pendingTypes (pending : List (Nat × Expr Key)) : List (Nat × SType) :=
  pending.map fun (index,expression) => (index,expression.type)

def completedTypes (completed : List (Nat × Datum)) : List (Nat × SType) :=
  completed.map fun (index,value) => (index,value.type)

structure CollectRep (program : Program Key) (heap : Heap) (objects : List WordArena.Object)
    (typing : Expr Key → Prop) (types : List SType)
    (pending : List (Nat × Expr Key)) (completed : List (Nat × Datum)) : Prop where
  pendingTyped : ∀ index expression, (index,expression) ∈ pending → typing expression
  values : ∀ index value, (index,value) ∈ completed → DatumRep program heap objects value value.type
  occurrences : (pendingTypes pending ++ completedTypes completed).Perm (indexed types)

/-- The selected occurrence is held by Frame.collect while its expression runs.
The current child is outside both pending and completed, so it cannot be picked
again or disappear when its value is inserted. -/
structure ActiveRep (program : Program Key) (heap : Heap) (objects : List WordArena.Object)
    (typing : Expr Key → Prop) (types : List SType) (index : Nat) (expected : SType)
    (pending : List (Nat × Expr Key)) (completed : List (Nat × Datum)) : Prop where
  pendingTyped : ∀ position expression, (position,expression) ∈ pending → typing expression
  values : ∀ position value, (position,value) ∈ completed → DatumRep program heap objects value value.type
  occurrences : ((index,expected) :: (pendingTypes pending ++ completedTypes completed)).Perm (indexed types)

theorem indexed_member (member : (index,type) ∈ indexed types) : types[index]? = some type := by
  obtain ⟨⟨source,position⟩,found,equal⟩ := List.mem_map.mp member
  cases equal
  exact List.mem_zipIdx_iff_getElem?.mp found

theorem CollectRep.length (represented : CollectRep program heap objects typing types pending completed) :
    pending.length + completed.length = types.length := by
  simpa [pendingTypes,completedTypes,indexed] using represented.occurrences.length_eq

theorem ActiveRep.length (represented : ActiveRep program heap objects typing types index expected pending completed) :
    pending.length + completed.length + 1 = types.length := by
  have lengths := represented.occurrences.length_eq
  simpa [pendingTypes,completedTypes,indexed] using lengths

theorem CollectRep.select (represented : CollectRep program heap objects typing types pending completed)
    (selected : Machine.Selected pending (index,expression) rest) :
    typing expression ∧ types[index]? = some expression.type ∧
      ActiveRep program heap objects typing types index expression.type rest completed := by
  have pendingMember : (index,expression.type) ∈ pendingTypes pending :=
    List.mem_map.mpr ⟨(index,expression),selected.member,rfl⟩
  have sourceMember := represented.occurrences.subset (List.mem_append_left _ pendingMember)
  refine ⟨represented.pendingTyped _ _ selected.member,indexed_member sourceMember,?_,represented.values,?_⟩
  · intro position child member
    exact represented.pendingTyped _ _ (selected.perm.symm.subset (List.mem_cons_of_mem _ member))
  · have removed := (selected.perm.map fun (position,child) => (position,child.type)).append_right
      (completedTypes completed)
    exact removed.symm.trans represented.occurrences

theorem CollectRep.pick (represented : CollectRep program heap objects typing types pending completed)
    (picked : Machine.pick choice pending = some ((index,expression),rest)) :
    typing expression ∧ types[index]? = some expression.type ∧
      ActiveRep program heap objects typing types index expression.type rest completed :=
  represented.select (Machine.pick_sound picked)

theorem ActiveRep.complete (represented : ActiveRep program heap objects typing types index expected pending completed)
    (child : DatumRep program heap objects value expected) :
    CollectRep program heap objects typing types pending ((index,value) :: completed) := by
  refine ⟨represented.pendingTyped,?_,?_⟩
  · intro position datum member
    rcases List.mem_cons.mp member with equal | old
    · cases equal
      simpa only [child.type] using child
    · exact represented.values _ _ old
  · change (pendingTypes pending ++ (index,value.type) :: completedTypes completed).Perm (indexed types)
    rw [child.type]
    exact List.perm_middle.trans represented.occurrences

theorem CollectRep.extend (represented : CollectRep program before oldObjects typing types pending completed)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    CollectRep program after newObjects typing types pending completed :=
  ⟨represented.pendingTyped,fun index value member => (represented.values index value member).extend invocation objects,
    represented.occurrences⟩

theorem ActiveRep.extend (represented : ActiveRep program before oldObjects typing types index expected pending completed)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    ActiveRep program after newObjects typing types index expected pending completed :=
  ⟨represented.pendingTyped,fun position value member => (represented.values position value member).extend invocation objects,
    represented.occurrences⟩

private theorem indexed_map (f : α → β) (values : List α) (start : Nat) :
    (values.zipIdx start).map (fun (value,index) => (index,f value)) =
      ((values.map f).zipIdx start).map (fun (value,index) => (index,value)) := by
  induction values generalizing start with
  | nil => rfl
  | cons value values ih => simp [List.zipIdx_cons,ih]

theorem CollectRep.initial (expressions : List (Expr Key))
    (typed : ∀ expression ∈ expressions, typing expression) :
    CollectRep program heap objects typing (expressions.map Expr.type)
      (expressions.zipIdx.map fun (expression,index) => (index,expression)) [] := by
  refine ⟨?_,by simp,?_⟩
  · intro index expression member
    obtain ⟨⟨child,position⟩,found,equal⟩ := List.mem_map.mp member
    cases equal
    exact typed expression (List.fst_mem_of_mem_zipIdx found)
  · apply List.Perm.of_eq
    simpa [pendingTypes,completedTypes,indexed,List.map_map,Function.comp_def] using
      indexed_map Expr.type expressions 0

private def keyMap (f : α → β) (item : Nat × α) : Nat × β := (item.1,f item.2)

theorem insertOrdered_map (f : α → β) (item : Nat × α) (items : List (Nat × α)) :
    (Machine.insertOrdered item items).map (keyMap f) =
      Machine.insertOrdered (keyMap f item) (items.map (keyMap f)) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      by_cases before : item.1 ≤ head.1 <;> simp [Machine.insertOrdered,keyMap,before,ih]

theorem orderPairs_map (f : α → β) (items : List (Nat × α)) :
    (Machine.orderPairs items).map (keyMap f) = Machine.orderPairs (items.map (keyMap f)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [Machine.orderPairs,insertOrdered_map,ih]

theorem ordered_types (completed : List (Nat × Datum)) :
    (Machine.ordered completed).map Datum.type = Machine.ordered (completedTypes completed) := by
  unfold Machine.ordered completedTypes
  change _ = (Machine.orderPairs (completed.map (keyMap Datum.type))).map Prod.snd
  rw [← orderPairs_map Datum.type]
  simp only [List.map_map,Function.comp_def,keyMap]

theorem CollectRep.finished_types (represented : CollectRep program heap objects typing types [] completed) :
    (Machine.ordered completed).map Datum.type = types := by
  rw [ordered_types]
  apply Machine.ordered_permutation_zipIdx
  simpa [pendingTypes,indexed] using represented.occurrences

private theorem packetRep_of_members (values : Packet)
    (represented : ∀ value ∈ values, DatumRep program heap objects value value.type) :
    PacketRep program heap objects values (Types.ofList (values.map Datum.type)) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (represented value (by simp)) (ih fun datum member => represented datum (by simp [member]))

/-- Finishing the actual collector returns a physically represented packet in
source order for every schedule. No final packet or successful evaluator result
is assumed: both representation and type order follow from the invariant. -/
theorem CollectRep.finish (represented : CollectRep program heap objects typing types [] completed) :
    PacketRep program heap objects (Machine.ordered completed) (Types.ofList types) := by
  rw [← represented.finished_types]
  apply packetRep_of_members
  intro value member
  obtain ⟨⟨index,datum⟩,found,equal⟩ := List.mem_map.mp member
  cases equal
  exact represented.values index datum ((Machine.orderPairs_perm completed).subset found)

end Solidity.Execution.Safety.TypedPackets
