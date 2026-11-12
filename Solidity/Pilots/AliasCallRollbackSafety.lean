/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Pilots.AliasCallRollback
import Solidity.Core.Execution.Safety.ConfigurationLaws

/-! The checked pilot has an initial configuration in the independently
specified safety profile when the caller supplies its stronger heap invariant.
The concrete source/target theorem retains its weaker physical object premise;
this companion does not assume a successful machine operation or preservation. -/
namespace Solidity.Pilots.AliasCallRollback
open Static Aggregates Execution Execution.Safety
open Contract.Interaction (Word)

private theorem array_supported : Supported array := .inr ⟨true,rfl⟩
private theorem word_supported : Supported word := .inl rfl
private theorem bool_supported : Supported .bool := .inl rfl

private theorem array_local (program : Program EmptyKey) (id : Nat) : Profile.Expression program (arrayLocal id) :=
  .local array_supported
private theorem word_local (program : Program EmptyKey) (id : Nat) : Profile.Expression program (.local id word) :=
  .local word_supported
private theorem bool_local (program : Program EmptyKey) (id : Nat) : Profile.Expression program (.local id .bool) :=
  .local bool_supported
private theorem element_target (program : Program EmptyKey) (id : Nat) : Profile.Target program (element id) :=
  .index (array_local program id) ⟨true,rfl⟩ (.literal rfl trivial)

private theorem helper_literal (owner : BitVec 160) :
    Profile.Expression (entryProgram owner) (.literal ⟨signature.type,some 7⟩) := by
  apply Profile.Expression.literal rfl
  intro identity equal
  have same : identity = 7 := by simpa using equal.symm
  subst identity
  exact ⟨helper owner,entry_lookup_helper owner,by rfl⟩

private theorem entry_literal (owner : BitVec 160) :
    Profile.Expression (entryProgram owner) (.literal ⟨entrySignature.type,some 8⟩) := by
  apply Profile.Expression.literal rfl
  intro identity equal
  have same : identity = 8 := by simpa using equal.symm
  subst identity
  exact ⟨entryFunction,lookup_entry owner,by rfl⟩

private theorem helper_parameters : ∀ type ∈ typesList signature.parameters, Supported type := by
  intro type member
  change type ∈ [array,word] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact array_supported
  · have same : type = word := by simpa using member
    subst type
    exact word_supported

private theorem entry_parameters : ∀ type ∈ typesList entrySignature.parameters, Supported type := by
  intro type member
  change type ∈ [array,array,word,.bool] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact array_supported
  · exact array_supported
  · exact word_supported
  · exact bool_supported

theorem entry_profile (owner : BitVec 160) : Profile.Expression (entryProgram owner) entryExpression := by
  apply Profile.Expression.call (entry_literal owner)
    (.cons (array_local _ 0) (.cons (array_local _ 1) (.cons (word_local _ 2) (.cons (bool_local _ 3) .nil))))
    entry_parameters
  intro type member
  change type ∈ [word] at member
  have same : type = word := by simpa using member
  subst type
  exact word_supported

private theorem helper_profile (owner : BitVec 160) : Profile.Body (entryProgram owner) (helper owner).body := by
  apply Profile.Body.statement
  apply Profile.Statement.seq (.expr (.assign (element_target _ 10) (word_local _ 11)))
  apply Profile.Statement.seq
  · apply Profile.Statement.expr
    apply Profile.Expression.assign _ (word_local _ 11)
    exact .heap ⟨rfl,.storage owner,0,⟨owner,.inl rfl⟩,rfl⟩
  · apply Profile.Statement.return_
    intro expression impossible
    cases impossible

private theorem entry_body_profile (owner : BitVec 160) : Profile.Body (entryProgram owner) entryFunction.body := by
  apply Profile.Body.statement
  apply Profile.Statement.seq
  · apply Profile.Statement.expr
    apply Profile.Expression.call (helper_literal owner)
      (.cons (array_local _ 0) (.cons (word_local _ 2) .nil)) helper_parameters
    intro type impossible
    cases impossible
  · apply Profile.Statement.if_ (bool_local _ 3) (.revert)
    apply Profile.Statement.return_
    intro expression member
    have same : .read (element 1) = expression := by simpa using member
    subst expression
    exact .read (element_target _ 1)

private theorem lookup_cases {owner : BitVec 160} {handle : Nat} {definition : FunctionDefinition EmptyKey}
    (checked : (entryProgram owner).lookup handle = .ok definition) :
    (handle = 7 ∧ definition = helper owner) ∨ (handle = 8 ∧ definition = entryFunction) := by
  by_cases first : handle = 7
  · subst handle
    rw [entry_lookup_helper] at checked
    cases checked
    exact .inl ⟨rfl,rfl⟩
  · by_cases second : handle = 8
    · subst handle
      rw [lookup_entry] at checked
      cases checked
      exact .inr ⟨rfl,rfl⟩
    · have valid : (entryProgram owner).valid = true := by rfl
      unfold Program.lookup at checked
      rw [valid] at checked
      simp [entryProgram,Ne.symm first,Ne.symm second,Bind.bind,Except.bind,Pure.pure,Except.pure] at checked

theorem entry_closed (owner : BitVec 160) : Profile.ClosedProgram registry (entryProgram owner) := by
  refine ⟨by rfl,⟨128,by rfl⟩,?_,?_,?_⟩
  · intro handle definition checked
    rcases lookup_cases checked with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact helper_profile owner
    · exact entry_body_profile owner
  · intro handle definition checked binder member
    rcases lookup_cases checked with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · change binder ∈ [⟨10,array,none⟩,⟨11,word,none⟩] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact array_supported
      · exact word_supported
    · change binder ∈ [⟨0,array,none⟩,⟨1,array,none⟩,⟨2,word,none⟩,⟨3,.bool,none⟩] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact array_supported
      · exact array_supported
      · exact word_supported
      · exact bool_supported
  · intro handle definition checked binder member
    rcases lookup_cases checked with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · cases member
    · change binder ∈ [⟨4,word,none⟩] at member
      have same : binder = ⟨4,word,none⟩ := by simpa using member
      subst binder
      exact word_supported

theorem entry_state_rep (physical : HeapRep heap [object]) (owner : BitVec 160) (value : Word) (fail : Bool) :
    StateRep (entryProgram owner) [object] (Execution.Safety.Locals.environment (entryLocals heap value fail))
      (entryState heap value fail) := by
  refine ⟨physical,?_,rfl,by simp [entryState,entryLocals]⟩
  intro scope member item contained
  have same : scope = [(3,⟨.bool,some fail⟩),(2,⟨word,some value⟩),
      (1,⟨array,some (reference heap)⟩),(0,⟨array,some (reference heap)⟩)] := by
    simpa [entryState,entryLocals] using member
  subst scope
  simp only [List.mem_cons,List.not_mem_nil,or_false] at contained
  rcases contained with rfl | rfl | rfl | rfl
  · exact ⟨fail,rfl,.boolean _ _ _ _⟩
  · exact ⟨value,rfl,.word _ _ _ _⟩
  · exact ⟨reference heap,rfl,.array true object (by simp)⟩
  · exact ⟨reference heap,rfl,.array true object (by simp)⟩

theorem initial_configuration (physical : HeapRep heap [object]) (owner : BitVec 160) (value : Word) (fail : Bool) :
    ConfigurationRep registry (entryProgram owner)
      (Config.expression (entryState heap value fail) entryExpression) := by
  have prepared := checked_entry heap owner value fail
  unfold SourceFacade.prepareExpression at prepared
  obtain ⟨_,_,remaining⟩ := SourceTyping.bind_checked prepared
  obtain ⟨_,admitted,_⟩ := SourceTyping.bind_checked remaining
  exact configuration_expression (entry_closed owner) (entry_state_rep physical owner value fail)
    (entry_profile owner) admitted

end Solidity.Pilots.AliasCallRollback
