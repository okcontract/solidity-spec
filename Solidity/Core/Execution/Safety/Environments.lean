/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.TypedState

/-! Typed lookup equivalence preserves each lexical suffix, not list order.
The checker lists function binders forward; runtime cells are prepended. Their
declaration IDs, types and lexical lifetime boundaries are what execution uses.
-/
namespace Solidity.Execution.Safety
open Static

def Environment.find (environment : Environment) (key : LocalId) : Option SType :=
  ((environment.flatten).find? fun entry => entry.1 == key).map Prod.snd

def Environment.enter (environment : Environment) : Environment := [] :: environment

def Environment.declare (environment : Environment) (binder : Binder) : Environment :=
  match environment with
  | [] => []
  | scope :: rest => ((binder.id,binder.type) :: scope) :: rest

structure Environment.Equivalent (left right : Environment) : Prop where
  depth : left.length = right.length
  lookup : ∀ depth key, Environment.find (left.drop depth) key = Environment.find (right.drop depth) key

theorem Environment.Equivalent.refl (environment : Environment) : Equivalent environment environment := ⟨rfl,by intros; rfl⟩

theorem Environment.Equivalent.of_eq (same : left = right) : Equivalent left right := by
  subst right
  exact .refl left

theorem Environment.Equivalent.symm (same : Equivalent left right) : Equivalent right left :=
  ⟨same.depth.symm,fun depth key => (same.lookup depth key).symm⟩

theorem Environment.Equivalent.trans (first : Equivalent left middle) (second : Equivalent middle right) :
    Equivalent left right := ⟨first.depth.trans second.depth,fun depth key => (first.lookup depth key).trans (second.lookup depth key)⟩

theorem Environment.Equivalent.find (same : Equivalent left right) (key : LocalId) :
    Environment.find left key = Environment.find right key := same.lookup 0 key

theorem Environment.find_enter (environment : Environment) (key : LocalId) :
    Environment.find (Environment.enter environment) key = Environment.find environment key := rfl

theorem Environment.Equivalent.enter (same : Equivalent left right) :
    Equivalent (Environment.enter left) (Environment.enter right) := by
  refine ⟨congrArg Nat.succ same.depth,?_⟩
  intro depth key
  cases depth with
  | zero => exact same.find key
  | succ depth => exact same.lookup depth key

theorem Environment.Equivalent.leave (same : Equivalent (leftScope :: left) (rightScope :: right)) :
    Equivalent left right := by
  refine ⟨by simpa using same.depth,fun depth key => ?_⟩
  exact same.lookup (depth+1) key

theorem Environment.find_declare (environment : Environment) (nonempty : environment ≠ [])
    (binder : Binder) (key : LocalId) :
    Environment.find (Environment.declare environment binder) key =
      if binder.id == key then some binder.type else Environment.find environment key := by
  cases environment with
  | nil => exact False.elim (nonempty rfl)
  | cons scope rest =>
      by_cases same : binder.id = key <;>
        simp [Environment.declare,Environment.find,same]

theorem Environment.Equivalent.declare (same : Equivalent left right) (binder : Binder) :
    Equivalent (Environment.declare left binder) (Environment.declare right binder) := by
  cases left with
  | nil =>
      have empty : right = [] := List.eq_nil_of_length_eq_zero same.depth.symm
      subst right
      exact .refl []
  | cons leftScope left =>
      cases right with
      | nil => cases same.depth
      | cons rightScope right =>
          refine ⟨same.depth,?_⟩
          intro depth key
          cases depth with
          | zero =>
              rw [List.drop_zero,List.drop_zero,Environment.find_declare _ (by simp),Environment.find_declare _ (by simp)]
              simp only [same.find]
          | succ depth => exact same.lookup (depth+1) key

end Solidity.Execution.Safety
