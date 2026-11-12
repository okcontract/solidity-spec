/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.MemoryConstructionFrame

/-! Recursive defaults preserve old allocation registrations and every slice
from the zero slot upward below the entry frontier. The shared empty zero slot
is read, never replaced; fresh parent cells and children compose through the
same physical extension laws as explicit memory copies. -/
namespace Solidity.Aggregates.Defaults
open Static
open Copy (MemoryExtension)

def MakesDefaultExtension (makeDefault : MakeDefault) : Prop :=
  ∀ heap budget type value after remaining,
    makeDefault heap budget type = .ok (value, after, remaining) →
    MemoryExtension heap.nextMemory heap after

private theorem map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] map_error map_ok

theorem initializeCell_extension (makeDefault : MakeDefault) (safe : MakesDefaultExtension makeDefault)
    (data : Reference) (region : data.region = .memory invocation)
    (above : cutoff ≤ data.address.toNat) (frontier : cutoff ≤ heap.nextMemory)
    (written : initializeCell makeDefault data (heap, budget) entry = .ok (after, remaining)) :
    MemoryExtension cutoff heap after := by
  unfold initializeCell at written
  cases made : makeDefault heap budget (atLocation entry.1 .memory false) with
  | error failure => simp [made] at written <;> cases written
  | ok result =>
      rcases result with ⟨value, fresh, available⟩
      have first := (safe heap budget _ value fresh available made).weaken frontier
      simp only [made, Bind.bind, Except.bind] at written
      cases reserved : reserve available 32 with
      | error failure => simp [reserved] at written <;> cases written
      | ok allowance =>
          simp only [reserved] at written
          cases advanced : Access.advance data (entry.2*32) with
          | error failure => simp [advanced] at written <;> cases written
          | ok reference =>
              have position := Copy.advance_memory data (entry.2*32) region advanced
              simp only [advanced] at written
              cases stored : writeMemoryValue fresh reference value with
              | error failure => simp [stored] at written <;> cases written
              | ok final =>
                  have last := Copy.writeMemoryValue_extension reference value position.1
                    (by omega : cutoff ≤ reference.address.toNat) stored
                  simp only [stored] at written
                  cases written
                  exact first.trans last

theorem initializeCells_extension (makeDefault : MakeDefault) (safe : MakesDefaultExtension makeDefault)
    (data : Reference) (region : data.region = .memory invocation)
    (above : cutoff ≤ data.address.toNat) (frontier : cutoff ≤ heap.nextMemory)
    (written : initializeCells makeDefault heap budget data types = .ok (after, remaining)) :
    MemoryExtension cutoff heap after := by
  unfold initializeCells at written
  cases reserved : reserve budget types.length with
  | error failure => simp [reserved] at written <;> cases written
  | ok allowance =>
      simp only [reserved, Bind.bind, Except.bind] at written
      exact Copy.fold_extension (initializeCell makeDefault data)
        (fun heap budget entry after remaining frontier done =>
          initializeCell_extension makeDefault safe data region above frontier done)
        types.zipIdx frontier written

theorem arrayDataReference_memory (reference : Reference) (region : reference.region = .memory invocation)
    (above : cutoff ≤ reference.address.toNat)
    (advanced : arrayDataReference reference dynamic = .ok data) :
    data.region = .memory invocation ∧ cutoff ≤ data.address.toNat := by
  cases dynamic with
  | false => cases advanced; exact ⟨region, above⟩
  | true =>
      have position := Copy.advance_memory reference 32 region advanced
      exact ⟨position.1, by omega⟩

theorem allocateArray_extension (makeDefault : MakeDefault) (safe : MakesDefaultExtension makeDefault)
    (written : allocateArray makeDefault heap budget element count dynamic pointer = .ok (value, after, remaining)) :
    MemoryExtension heap.nextMemory heap after := by
  unfold allocateArray at written
  cases sized : MemoryOps.arraySize count false dynamic with
  | error failure => simp [sized] at written <;> cases written
  | ok bytes =>
      simp only [sized, Bind.bind, Except.bind] at written
      cases allocated : MemoryOps.allocate heap budget bytes with
      | error failure => simp [allocated] at written <;> cases written
      | ok result =>
          rcases result with ⟨reference, fresh, available⟩
          have first := Copy.allocate_extension allocated (Nat.le_refl heap.nextMemory)
          simp only [allocated] at written
          cases header : initializeLength fresh available reference count dynamic with
          | error failure => simp [header] at written <;> cases written
          | ok result =>
              rcases result with ⟨populated, rest⟩
              have second := Copy.initializeLength_extension reference first.2.1
                (by omega : heap.nextMemory ≤ reference.address.toNat) header
              simp only [header] at written
              cases advanced : arrayDataReference reference dynamic with
              | error failure => simp [advanced] at written <;> cases written
              | ok data =>
                  have position := arrayDataReference_memory reference first.2.1
                    (by omega : heap.nextMemory ≤ reference.address.toNat) advanced
                  simp only [advanced] at written
                  cases reserved : reserve rest count with
                  | error failure => simp [reserved] at written <;> cases written
                  | ok allowance =>
                      simp only [reserved] at written
                      cases filled : initializeCells makeDefault populated allowance data (List.replicate count element) with
                      | error failure => simp [filled] at written <;> cases written
                      | ok result =>
                          rcases result with ⟨final, unused⟩
                          have third := initializeCells_extension makeDefault safe data position.1 position.2
                            ((first.1.trans second).grows) filled
                          simp only [filled] at written
                          cases written
                          exact (first.1.trans second).trans third

theorem allocateStruct_extension (makeDefault : MakeDefault) (safe : MakesDefaultExtension makeDefault)
    (written : allocateStruct makeDefault registry heap budget identity pointer = .ok (value, after, remaining)) :
    MemoryExtension heap.nextMemory heap after := by
  unfold allocateStruct at written
  cases definition : registry.structFields identity with
  | none => simp [definition] at written <;> cases written
  | some fields =>
      simp only [definition, Bind.bind, Except.bind] at written
      cases sized : MemoryOps.arraySize fields.length false false with
      | error failure => simp [sized] at written <;> cases written
      | ok bytes =>
          simp only [sized] at written
          cases allocated : MemoryOps.allocate heap budget bytes with
          | error failure => simp [allocated] at written <;> cases written
          | ok result =>
              rcases result with ⟨reference, fresh, available⟩
              have first := Copy.allocate_extension allocated (Nat.le_refl heap.nextMemory)
              simp only [allocated] at written
              cases filled : initializeCells makeDefault fresh available reference (fields.map Prod.snd) with
              | error failure => simp [filled] at written <;> cases written
              | ok result =>
                  rcases result with ⟨final, unused⟩
                  have second := initializeCells_extension makeDefault safe reference first.2.1
                    (by omega : heap.nextMemory ≤ reference.address.toNat) first.1.grows filled
                  simp only [filled] at written
                  cases written
                  exact first.1.trans second

theorem build_extension (registry : Registry) (fuel : Nat) : MakesDefaultExtension (build registry fuel) := by
  induction fuel with
  | zero => intro heap budget type value after remaining written; cases written
  | succ fuel ih =>
      intro heap budget type value after remaining written
      cases zero : Static.defaultScalar type with
      | some scalar =>
          simp only [build, zero] at written
          have same := MemoryExtension.refl heap.nextMemory heap
          cases written
          exact same
      | none =>
          simp only [build, zero] at written
          cases type with
          | array element size location pointer =>
              cases location with
              | storage => cases size <;> cases written
              | calldata => cases size <;> cases written
              | memory =>
                  cases size with
                  | none =>
                      cases empty : emptyReference heap with
                      | error failure => simp [empty] at written <;> cases written
                      | ok reference =>
                          simp only [empty, Bind.bind, Except.bind] at written
                          have same := MemoryExtension.refl heap.nextMemory heap
                          cases written
                          exact same
                  | some count => exact allocateArray_extension _ ih written
          | bytes location pointer | string location pointer =>
              cases location with
              | storage => cases written
              | calldata => cases written
              | memory =>
                  cases empty : emptyReference heap with
                  | error failure => simp [empty] at written <;> cases written
                  | ok reference =>
                      simp only [empty, Bind.bind, Except.bind] at written
                      have same := MemoryExtension.refl heap.nextMemory heap
                      cases written
                      exact same
          | structType identity location pointer =>
              cases location with
              | storage => cases written
              | calldata => cases written
              | memory => exact allocateStruct_extension _ ih written
          | _ => cases written

theorem defaultValue_extension
    (written : defaultValue registry fuel budget heap type = .ok (value, after, remaining)) :
    MemoryExtension heap.nextMemory heap after := by
  unfold defaultValue at written
  cases eligible : memoryEligible registry fuel type with
  | error failure => simp [eligible] at written <;> cases written
  | ok _ =>
      simp only [eligible, Bind.bind, Except.bind] at written
      exact build_extension registry fuel heap budget type value after remaining written

theorem newArray_extension
    (written : newArray registry fuel budget heap element count dynamic = .ok (value, after, remaining)) :
    MemoryExtension heap.nextMemory heap after := by
  unfold newArray at written
  cases eligible : memoryEligible registry fuel
      (.array (atLocation element .memory false) (if dynamic then none else some count) .memory true) with
  | error failure => simp [eligible] at written <;> cases written
  | ok _ =>
      simp only [eligible, Bind.bind, Except.bind] at written
      exact allocateArray_extension _ (build_extension registry fuel) written

theorem newBytes_extension
    (written : newBytes budget heap count string = .ok (value, after, remaining)) :
    MemoryExtension heap.nextMemory heap after := (Copy.newBytes_extension written).1

end Solidity.Aggregates.Defaults
