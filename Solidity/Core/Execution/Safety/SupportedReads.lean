/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.CodeLaws
import Solidity.Core.Execution.Safety.LocalSteps
import Solidity.Core.Execution.Safety.WordEffects

namespace Solidity.Execution.Safety.SupportedReads
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem scalar_reference_none {value : Value} (supported : value.type.scalarSupported = true) : value.reference = none := by
  cases value with
  | mk type data => cases type <;> simp_all [SType.scalarSupported,Value.reference]

theorem canonical_array (registry : Registry) (fuel : Nat) (heap : Heap) (pointer : Bool)
    (address : Contract.Interaction.Word) :
    Access.readChecked registry (fuel+2) heap ⟨WordArena.arrayType pointer,Copy.memoryReference heap address⟩ =
      .ok ⟨WordArena.arrayType pointer,Copy.memoryReference heap address⟩ := by
  have eligible := WordEffects.eligible_array registry fuel heap.invocation pointer
  have valid := Copy.memory_validate_reference (heap := heap) (type := WordArena.arrayType pointer)
    (address := address) (by rfl)
  change (do
    eligibleAt registry (fuel+2) (.memory heap.invocation) (WordArena.arrayType pointer)
    Access.read heap ⟨WordArena.arrayType pointer,Copy.memoryReference heap address⟩) = _
  rw [eligible]
  simp only [Bind.bind,Except.bind]
  unfold Access.read
  rw [valid]
  simp [WordArena.arrayType,isReference,referenceLocation,Place.asValue,referenceValue,
    Copy.memoryReference,Except.map]

theorem local_total {localId : LocalId}
    (stateRep : StateRep program objects environment state)
    (bound : Environment.find environment localId = some type) (ready : TypeReady registry type) :
    ∃ value, Effects.readCaptured registry (fuel+2) state.locals state.heap (.local localId type) = .ok value ∧
      ValueRep program state.heap objects value ∧ value.type = type := by
  obtain ⟨value,read,represented⟩ := stateRep.local_read bound
  have typed : value.type = type := by
    unfold Execution.Locals.read at read
    cases found : state.locals.find localId with
    | none => simp [found] at read
    | some cell =>
        simp only [found] at read
        split at read
        · cases read
        · rename_i correct
          cases initialized : cell.value with
          | none => simp [initialized] at read
          | some stored =>
              simp [initialized] at read
              subst value
              simpa using correct
  have eligible := SupportedEligibility.eligible_total ready fuel
  refine ⟨value,?_,represented,typed⟩
  simp only [Effects.readCaptured,eligible,read,Bind.bind,Except.bind]
  cases represented with
  | scalar support closed => simp [scalar_reference_none support]
  | array pointer object member =>
      simp only [WordArena.arrayType,Value.reference]
      exact canonical_array _ _ _ _ _
  | emptyArray pointer =>
      simp only [WordArena.arrayType,Value.reference]
      exact canonical_array _ _ _ _ _

end Solidity.Execution.Safety.SupportedReads
