/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.ExpressionSteps
import Solidity.Core.Execution.Safety.SupportedReads
import Solidity.Core.Execution.Safety.TargetWrites

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem StateRep.local_type {localId : LocalId} (stateRep : StateRep program objects environment state)
    (bound : Environment.find environment localId = some type) : state.locals.typeOf localId = .ok type := by
  rw [← stateRep.shape,environment_find] at bound
  cases found : state.locals.find localId with
  | none => simp [found] at bound
  | some cell =>
      simp only [found,Option.map_some,Option.some.injEq] at bound
      simp [Execution.Locals.typeOf,found,bound]

theorem physicalWord_target (physical : Profile.PhysicalWord place) : HeapTargetRep heap objects place := by
  rcases place with ⟨type,reference⟩
  rcases physical with ⟨rfl,region,address,⟨owner,storageOrTransient⟩,rfl⟩
  rcases storageOrTransient with rfl | rfl
  · exact .persistent owner address
  · exact .transient owner address

theorem heapTarget_validate (represented : HeapTargetRep heap objects place) : Access.validate heap place = .ok () := by
  cases represented with
  | persistent owner address => exact WordEffects.validate_persistent _ _ _
  | transient owner address => exact WordEffects.validate_transient _ _ _
  | cell object member index inside => exact WordArena.validate_word _ _

theorem local_eval_progress {localId : LocalId}
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (code : ExpressionCode registry program environment (.local localId type)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
      ⟨.eval (.local localId type),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  have supported : Supported type := by cases code.form with | «local» supported => exact supported
  obtain ⟨value,read,represented,typed⟩ := SupportedReads.local_total (fuel := fuel) context.stateRep code.local_bound ⟨supported,code.formed⟩
  refine ⟨⟨.value (.atom value),stack,state,entry⟩,step_of_transition ?_,?_,rfl⟩
  · simp [Machine.transition,read,Machine.next]
  · exact context.configuration (.value (by simpa only [typed] using (DatumRep.atom represented)))

theorem capture_local_progress {localId : LocalId}
    (context : EvaluationContext registry program objects environment state entry stack (.target type))
    (code : TargetCode registry program environment (.local localId type)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
      ⟨.capture (.local localId type),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  have bound := code.local_bound
  have current := context.stateRep.local_type bound
  refine ⟨⟨.target (.captured (.local localId type)),stack,state,entry⟩,step_of_transition ?_,?_,rfl⟩
  · simp [Machine.transition,current,Machine.next]
  · exact context.configuration (.target (.local bound code.ready))

theorem capture_heap_progress
    (context : EvaluationContext registry program objects environment state entry stack (.target place.type))
    (code : TargetCode registry program environment (.heap place)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
      ⟨.capture (.heap place),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  have represented : HeapTargetRep state.heap objects place := by
    cases code.form with
    | heap physical => exact physicalWord_target physical
  have typed := TargetWrites.heapTarget_type represented
  refine ⟨⟨.target (.captured (.heap place)),stack,state,entry⟩,step_of_transition ?_,?_,rfl⟩
  · simp [Machine.transition,heapTarget_validate represented,Machine.next]
  · apply context.configuration
    rw [typed]
    exact .target (.heap represented)

theorem capture_index_progress
    (context : EvaluationContext registry program objects environment state entry stack (.target (.uint 31)))
    (code : TargetCode registry program environment (.index (.uint 31) source index)) :
    ∃ after, Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
      ⟨.capture (.index (.uint 31) source index),stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases code.form with
  | index sourceForm array indexForm =>
      obtain ⟨pointer,arrayType⟩ := array
      obtain ⟨sourceFuel,incoming,after,writable,shape,checked⟩ := code.admitted
      cases sourceFuel with
      | zero => cases checked
      | succ sourceFuel =>
          obtain ⟨childrenAfter,checkedChildren,unsigned,_,_⟩ := SourceTyping.index_target_checked checked
          obtain ⟨width,indexType⟩ := SourceTyping.unsigned_type unsigned
          have children : ∀ expression ∈ [source,index], ExpressionCode registry program environment expression := by
            intro expression member
            obtain ⟨childFuel,childAfter,child⟩ := SourceTyping.children_checked checkedChildren member
            refine ⟨?_,childFuel,{incoming with orderIndependent := true},childAfter,shape,child⟩
            rcases List.mem_cons.mp member with rfl | member
            · exact sourceForm
            · cases List.mem_singleton.mp member
              exact indexForm
          refine ⟨⟨.collect ([source,index].zipIdx.map fun (value,index) => (index,value)) [] (.index (.uint 31)),stack,state,entry⟩,
            rfl,?_,rfl⟩
          apply context.gather children
          simpa only [List.map_cons,List.map_nil,arrayType,indexType] using
            (CompletionRep.index (registry := registry) pointer width)

end Solidity.Execution.Safety
