/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Translations

namespace Solidity.Execution.Compatibility
open Core Static
variable {Keys : SType → Type} {types : List Core.Ty} {id : Nat}

theorem eraseDups_nodup (values : List Nat) (distinct : values.Nodup) : values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
      have filtered : rest.filter (fun item => !(item == value)) = rest := by
        apply List.filter_eq_self.mpr
        intro item member
        have different : item ≠ value := by intro same; subst item; exact absent member
        simp [different]
      rw [List.eraseDups_cons, filtered, ih distinct]

theorem parameter_id (member : id ∈ (parameterBinders types).map Binder.id) :
    id < 2 * types.length ∧ ∃ index, id = 2 * index := by
  induction types with
  | nil => simp [parameterBinders] at member
  | cons type rest ih =>
      simp only [parameterBinders, List.map_cons, binder, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨by simp, rest.length, rfl⟩
      · obtain ⟨bound, index, same⟩ := ih member
        exact ⟨by simp only [List.length_cons]; omega, index, same⟩

theorem parameter_ids_distinct (types : List Core.Ty) : ((parameterBinders types).map Binder.id).Nodup := by
  induction types with
  | nil => exact .nil
  | cons type rest ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih⟩
      intro member
      have bound := (parameter_id member).1
      dsimp only [binder] at bound
      omega

theorem return_id (base : Nat) (member : id ∈ (returnBinders base types).map Binder.id) :
    2 * base + 1 ≤ id ∧ ∃ index, id = 2 * index + 1 := by
  induction types generalizing base with
  | nil => simp [returnBinders] at member
  | cons type rest ih =>
      simp only [returnBinders, List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨Nat.le_refl _, base, rfl⟩
      · obtain ⟨bound, index, same⟩ := ih (base+1) member
        exact ⟨by omega, index, same⟩

theorem return_ids_distinct (types : List Core.Ty) (base : Nat) :
    ((returnBinders base types).map Binder.id).Nodup := by
  induction types generalizing base with
  | nil => exact .nil
  | cons type rest ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih (base+1)⟩
      intro member
      have bound := (return_id (base+1) member).1
      dsimp only at bound
      omega

@[simp] theorem parameterBinders_length (types : List Core.Ty) : (parameterBinders types).length = types.length := by
  induction types <;> simp [parameterBinders, *]

@[simp] theorem returnBinders_length (types : List Core.Ty) (base : Nat) : (returnBinders base types).length = types.length := by
  induction types generalizing base <;> simp [returnBinders, *]

@[simp] theorem parameterBinders_types (types : List Core.Ty) :
    (parameterBinders types).map Binder.type = types.map SType.ofCore := by
  induction types <;> simp [parameterBinders, binder, *]

@[simp] theorem returnBinders_types (types : List Core.Ty) (base : Nat) :
    (returnBinders base types).map Binder.type = types.map SType.ofCore := by
  induction types generalizing base <;> simp [returnBinders, *]

theorem function_bindings (parameters returns : List Core.Ty) (body : Execution.Stmt Keys) :
    (⟨.nonpayable, parameterBinders parameters, returnBinders 0 returns, body⟩ : FunctionDefinition Keys).distinctBindings = true := by
  have disjoint : ∀ first ∈ (parameterBinders parameters).map Binder.id,
      ∀ second ∈ (returnBinders 0 returns).map Binder.id, first ≠ second := by
    intro first firstMember second secondMember
    obtain ⟨_, a, rfl⟩ := parameter_id firstMember
    obtain ⟨_, b, rfl⟩ := return_id 0 secondMember
    intro equal
    have parity := congrArg (fun value : Nat => value % 2) equal
    simp [Nat.add_mod] at parity
  have distinct := List.nodup_append.mpr
    ⟨parameter_ids_distinct parameters, return_ids_distinct returns 0, disjoint⟩
  simp only [FunctionDefinition.distinctBindings, List.map_append]
  rw [eraseDups_nodup _ distinct]
  simp

theorem function_signature (parameters returns : List Core.Ty) (body : Execution.Stmt Keys) :
    (⟨.nonpayable, parameterBinders parameters, returnBinders 0 returns, body⟩ : FunctionDefinition Keys).signature =
      signature parameters returns := by
  simp [FunctionDefinition.signature, signature]

structure TableRegion (first stop : Nat) (functions : List (Nat × FunctionDefinition Keys)) : Prop where
  grows : first ≤ stop
  distinct : (functions.map Prod.fst).Nodup
  bounds : ∀ entry ∈ functions, first ≤ entry.1 ∧ entry.1 < stop
  bindings : ∀ entry ∈ functions, entry.2.distinctBindings = true ∧ entry.2.mutability ≠ .payable

variable {functions initial final : List (Nat × FunctionDefinition Keys)}

theorem TableRegion.empty (start : Nat) : TableRegion start start ([] : List (Nat × FunctionDefinition Keys)) :=
  ⟨Nat.le_refl _, .nil, by simp, by simp⟩

theorem TableRegion.id_bounds (region : TableRegion first stop functions)
    (member : id ∈ functions.map Prod.fst) : first ≤ id ∧ id < stop := by
  obtain ⟨entry, inFunctions, same⟩ := List.mem_map.mp member
  subst id
  exact region.bounds entry inFunctions

theorem TableRegion.append (left : TableRegion first middle initial) (right : TableRegion middle stop final) :
    TableRegion first stop (initial ++ final) := by
  refine ⟨Nat.le_trans left.grows right.grows, ?_, ?_, ?_⟩
  · rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨left.distinct, right.distinct, ?_⟩
    intro a memberA b memberB equal
    have before := (left.id_bounds memberA).2
    have after := (right.id_bounds memberB).1
    omega
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨lower, upper⟩ := left.bounds entry member
      exact ⟨lower, Nat.lt_of_lt_of_le upper right.grows⟩
    · obtain ⟨lower, upper⟩ := right.bounds entry member
      exact ⟨Nat.le_trans left.grows lower, upper⟩
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact left.bindings entry member
    · exact right.bindings entry member

theorem TableRegion.prepend (tail : TableRegion (first+1) stop functions)
    (function : FunctionDefinition Keys)
    (bindings : function.distinctBindings = true) (mutability : function.mutability ≠ .payable) :
    TableRegion first stop ((first, function) :: functions) := by
  refine ⟨Nat.le_trans (Nat.le_succ first) tail.grows, ?_, ?_, ?_⟩
  · apply List.nodup_cons.mpr
    refine ⟨?_, tail.distinct⟩
    intro member
    have bound := (tail.id_bounds member).1
    omega
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨Nat.le_refl _, by have := tail.grows; omega⟩
    · obtain ⟨lower, upper⟩ := tail.bounds entry member
      exact ⟨by omega, upper⟩
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨bindings, mutability⟩
    · exact tail.bindings entry member

theorem procedure_table (body : Core.Procedure Ref Place returns vars) (start : Nat) :
    TableRegion start (procedure start body).nextHandle (procedure start body).functions := by
  induction body generalizing start with
  | ret | revert => exact .empty start
  | let_ _ _ ih | assign _ _ _ ih | store _ _ _ ih | emit _ _ _ _ ih => exact ih start
  | branch _ _ _ first second => exact (first start).append (second _)
  | call helper arguments next first second =>
      exact ((first (start+1)).append (second _)).prepend _ (function_bindings _ _ _)
        (by change Mutability.nonpayable ≠ .payable; decide)

theorem procedure_program_valid (body : Core.Procedure Ref Place returns vars) (start : Nat) :
    (program (procedure start body)).valid = true := by
  have region := procedure_table body start
  simp only [program, Program.valid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  constructor
  · rw [eraseDups_nodup _ region.distinct]
    simp
  · intro entry member
    obtain ⟨bindings, mutability⟩ := region.bindings entry member
    simp [bindings, mutability]

private theorem find_handle (distinct : (functions.map Prod.fst).Nodup)
    {handle : Nat} {function : FunctionDefinition Keys} (member : (handle, function) ∈ functions) :
    functions.find? (fun entry => entry.1 == handle) = some (handle, function) := by
  induction functions with
  | nil => cases member
  | cons entry rest ih =>
      obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have different : entry.1 ≠ handle := by
          intro same
          apply absent
          exact List.mem_map.mpr ⟨(handle, function), member, same.symm⟩
        have unequal : (entry.1 == handle) = false := Bool.eq_false_iff.mpr (by
          intro equal; exact different (by simpa only [beq_iff_eq] using equal))
        simpa [List.find?, unequal] using ih distinct member

theorem lookup_member (compiled : Translation Keys) (valid : (program compiled).valid = true)
    (region : TableRegion first compiled.nextHandle compiled.functions)
    (member : (handle, function) ∈ compiled.functions) :
    (program compiled).lookup handle = .ok function := by
  simp only [Program.lookup, valid]
  simp [program, find_handle region.distinct member]
  rfl

end Solidity.Execution.Compatibility
