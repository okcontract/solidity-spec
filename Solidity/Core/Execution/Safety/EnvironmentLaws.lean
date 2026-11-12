/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Configuration

namespace Solidity.Execution.Safety
open Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private def scopeLookup (scope : List (LocalId × SType)) (key : LocalId) : Option SType :=
  (scope.find? fun entry => entry.1 == key).map Prod.snd

private theorem scopeLookup_perm (permuted : left.Perm right) (distinct : (left.map Prod.fst).Nodup)
    (key : LocalId) : scopeLookup left key = scopeLookup right key := by
  induction permuted with
  | nil => rfl
  | cons entry permuted induction =>
      have tailDistinct := (List.nodup_cons.mp distinct).2
      by_cases selected : entry.1 = key
      · simp [scopeLookup,selected]
      · simpa [scopeLookup,selected] using induction tailDistinct
  | swap first second rest =>
      have different : first.1 ≠ second.1 := by
        intro same
        simp [List.nodup_cons,same] at distinct
      by_cases a : first.1 = key <;> by_cases b : second.1 = key
      · exact False.elim (different (a.trans b.symm))
      all_goals simp [scopeLookup,a,b]
  | trans first second firstInduction secondInduction =>
      exact (firstInduction distinct).trans (secondInduction ((first.map Prod.fst).nodup distinct))

theorem Environment.Equivalent.single_permutation (permuted : left.Perm right)
    (distinct : (left.map Prod.fst).Nodup) : Environment.Equivalent [left] [right] := by
  refine ⟨rfl,?_⟩
  intro depth key
  cases depth with
  | zero => simpa [Environment.find,scopeLookup] using scopeLookup_perm permuted distinct key
  | succ depth => simp [Environment.find]

private theorem binder_find (binders : List Binder) (key : LocalId) :
    ((binders.map fun binder => (binder.id,binder.type)).find? fun entry => entry.1 == key).map Prod.snd =
      (binders.find? fun binder => binder.id == key).map Binder.type := by
  simp [Function.comp_def]

theorem context_environment_find (context : Admission.Context) (key : LocalId) :
    Environment.find (Profile.scopesEnvironment context.scopes) key = (context.find key).map Binder.type := by
  unfold Environment.find Profile.scopesEnvironment Admission.Context.find
  rw [← List.map_flatten]
  exact binder_find _ key

theorem Environment.Equivalent.context_find {context : Admission.Context} {binder : Binder} (same : Environment.Equivalent
    (Profile.scopesEnvironment context.scopes) environment)
    (bound : context.find key = some binder) : Environment.find environment key = some binder.type := by
  rw [← same.find key,context_environment_find,bound]
  rfl

theorem prefixEnvironment_equivalent (body : Stmt EmptyKey) (same : Environment.Equivalent left right) :
    Environment.Equivalent (prefixEnvironment left body) (prefixEnvironment right body) := by
  cases body with
  | seq first rest =>
      cases first <;> try {exact same}
      case declare binders initializer =>
        cases binders with
        | nil => exact same
        | cons binder binders =>
            cases binders with
            | cons next binders => cases binder <;> exact same
            | nil =>
                cases binder with
                | none => exact same
                | some binder => exact prefixEnvironment_equivalent rest (same.declare binder)
  | _ => exact same
termination_by sizeOf body

theorem initializerEnvironment_equivalent (initializer : Stmt EmptyKey) (same : Environment.Equivalent left right) :
    Environment.Equivalent (initializerEnvironment left initializer) (initializerEnvironment right initializer) := by
  cases initializer <;> try {exact same}
  case declare binders initializer =>
    cases binders with
    | nil => exact same
    | cons binder binders =>
        cases binders with
        | cons next binders => cases binder <;> exact same
        | nil =>
            cases binder with
            | none => exact same
            | some binder => exact same.declare binder

private theorem eraseDups_length_le (values : List Nat) : values.eraseDups.length ≤ values.length := by
  cases values with
  | nil => exact Nat.le_refl _
  | cons head rest =>
      rw [List.eraseDups_cons]
      have bound := eraseDups_length_le (rest.filter fun value => !(value == head))
      have filtered := List.length_filter_le (fun value => !(value == head)) rest
      simp only [List.length_cons]
      omega
termination_by values.length
decreasing_by simpa using Nat.lt_succ_of_le (List.length_filter_le (fun value => !(value == head)) rest)

theorem nodup_of_eraseDups_length (values : List Nat) (equal : values.eraseDups.length = values.length) :
    values.Nodup := by
  induction values with
  | nil => exact .nil
  | cons head rest induction =>
      rw [List.eraseDups_cons] at equal
      have deduplicated := eraseDups_length_le (rest.filter fun value => !(value == head))
      have filtered := List.length_filter_le (fun value => !(value == head)) rest
      have equalLength : (rest.filter fun value => !(value == head)).length = rest.length := by
        simp only [List.length_cons] at equal
        omega
      have all := List.length_filter_eq_length_iff.mp equalLength
      have unchanged : rest.filter (fun value => !(value == head)) = rest := List.filter_eq_self.mpr all
      refine List.nodup_cons.mpr ⟨?_,induction ?_⟩
      · intro member
        have bad := all head member
        simp at bad
      · simpa only [unchanged,List.length_cons,Nat.succ.injEq] using equal

theorem lookup_distinct {program : Program EmptyKey} {definition : FunctionDefinition EmptyKey}
    (valid : program.valid = true) (lookup : program.lookup handle = .ok definition) :
    ((definition.parameters ++ definition.returns).map Binder.id).Nodup := by
  have all := valid
  simp only [Program.valid,Bool.and_eq_true] at all
  unfold Program.lookup at lookup
  simp only [valid,Bool.not_true,Bool.false_eq_true,↓reduceIte] at lookup
  cases selected : program.functions.find? (fun entry => entry.1 == handle) with
  | none => simp [selected] at lookup
  | some entry =>
      simp [selected] at lookup
      subst definition
      have member := List.mem_of_find?_eq_some selected
      have distinct := List.all_eq_true.mp all.2 entry member
      simp only [Bool.and_eq_true] at distinct
      apply nodup_of_eraseDups_length
      simpa [FunctionDefinition.distinctBindings] using distinct.1

end Solidity.Execution.Safety
