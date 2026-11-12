/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Representation.Base
import Solidity.Core.Aggregates.MemoryRepresentationFold

/-! Physical scalar/pointer stores and the completed-cell prefix invariant used
by fresh aggregate construction. -/
namespace Solidity.Aggregates.Copy
open Core Static
open Contract.Interaction (Word Memory wordBytes bytesWord)

def WordEncoding (value : Value) (word : Word) : Prop :=
  match value.reference with
  | none => encodeMemory value.type value.value = .ok word
  | some reference => word = reference.address

theorem checkExtent_memory_allocated (reference : Reference)
    (memory : reference.region = .memory invocation)
    (checked : checkExtent heap reference size = .ok ()) : heap.allocated reference.address.toNat size = true := by
  simp only [checkExtent, memory] at checked
  split at checked
  · cases checked
  · split at checked
    · assumption
    · cases checked

/-- Every successful padded memory value store has an exact physical word
image, whether that word is a scalar encoding or an aggregate data pointer. -/
theorem writeMemoryValue_word (cell : Reference) (value : Value)
    (memory : cell.region = .memory invocation) (padded : cell.byteCell = false)
    (written : Defaults.writeMemoryValue heap cell value = .ok after) :
    ∃ word, WordEncoding value word ∧ heap.allocated cell.address.toNat 32 = true ∧
      after = MemoryOps.snapshotCopy heap cell.address.toNat (wordBytes word) := by
  unfold Defaults.writeMemoryValue at written
  simp only [memory] at written
  split at written
  · cases written
  · split at written
    · cases written
    · cases reference : value.reference with
      | none =>
          simp only [reference] at written
          unfold writeScalar at written
          cases sized : storageBytes value.type with
          | none => simp [sized] at written
          | some bytes =>
              simp only [sized, memory, Bind.bind, Except.bind] at written
              split at written
              · cases written
              · simp only [padded, Bool.false_and, Bool.false_eq_true, ↓reduceIte, scalarCellBytes] at written
                cases extent : checkExtent heap cell 32 with
                | error failure => simp [extent] at written <;> cases written
                | ok token =>
                    have allocated := checkExtent_memory_allocated cell memory (by cases token; exact extent)
                    simp only [extent] at written
                    cases encoded : encodeMemory value.type value.value with
                    | error failure => simp [encoded] at written <;> cases written
                    | ok word =>
                        simp only [encoded] at written
                        cases written
                        exact ⟨word, by simpa [WordEncoding, reference] using encoded, allocated, rfl⟩
      | some pointer =>
          simp only [reference] at written
          split at written
          · cases written
          · split at written
            · cases written
            · split at written
              · cases written
              · cases pointerExtent : checkExtent heap pointer 0 with
                | error failure => simp [pointerExtent] at written <;> cases written
                | ok _ =>
                    simp only [pointerExtent] at written
                    cases cellExtent : checkExtent heap cell 32 with
                    | error failure => simp [cellExtent] at written <;> cases written
                    | ok token =>
                        have allocated := checkExtent_memory_allocated cell memory (by cases token; exact cellExtent)
                        simp only [cellExtent] at written
                        cases written
                        exact ⟨pointer.address, by simp [WordEncoding, reference], allocated, rfl⟩

theorem convertScalar_supported (converted : convertScalar type source = .ok value) :
    type.scalarSupported = true := by
  by_cases supported : type.scalarSupported = true
  · exact supported
  · have unsupported : type.scalarSupported = false := Bool.eq_false_iff.mpr supported
    simp [convertScalar, Static.convert, unsupported] at converted

theorem Value.reference_none (value : Value) (supported : value.type.scalarSupported = true) :
    value.reference = none := by
  cases value with
  | mk type value => cases type <;> simp_all [SType.scalarSupported, Value.reference]

theorem writeMemoryValue_scalar_rep (source value : Value) (type : SType) (cell : Reference)
    (converted : convertScalar type source = .ok value)
    (memory : cell.region = .memory invocation) (padded : cell.byteCell = false)
    (written : Defaults.writeMemoryValue heap cell value = .ok after) :
    ScalarPacket after type cell.address.toNat (.scalar source) := by
  have same := convertScalar_type converted
  have supported := convertScalar_supported converted
  have noReference : value.reference = none := Value.reference_none value (by simpa only [same] using supported)
  rcases writeMemoryValue_word cell value memory padded written with ⟨word, encoding, extent, shape⟩
  cases value with
  | mk valueType represented =>
      dsimp only at same
      subst valueType
      have encoded : encodeMemory type represented = .ok word := by
        simpa only [WordEncoding, noReference] using encoding
      refine ⟨source, represented, word, rfl, converted, encoded, ?_, ?_⟩
      · rw [shape]; exact extent
      · rw [shape]
        simpa only [Contract.Interaction.wordBytes_length] using
          MemoryOps.snapshotCopy_contents heap cell.address.toNat (wordBytes word)

theorem writeMemoryValue_rep (represented : ValueRep registry heap origin type contents value)
    (cell : Reference) (memory : cell.region = .memory invocation) (padded : cell.byteCell = false)
    (range : lower ≤ cell.address.toNat ∧ cell.address.toNat+32 ≤ floor)
    (fresh : floor ≤ origin)
    (written : Defaults.writeMemoryValue heap cell value = .ok after) :
    CellRep registry after lower floor type cell.address.toNat contents := by
  cases contents with
  | scalar source =>
      exact .scalar type cell.address.toNat (.scalar source) range
        (writeMemoryValue_scalar_rep source value type cell represented memory padded written)
  | array sourceElement values | «structure» identity values | bytes string values =>
      rcases represented with ⟨address, tagged, tree⟩
      have reference := retag_reference tagged
      rcases writeMemoryValue_word cell value memory padded written with ⟨word, encoding, extent, shape⟩
      have wordEq : word = address := by simpa only [WordEncoding, reference, memoryReference] using encoding
      rw [wordEq] at shape
      have treeAfter := tree.frame (PacketFrame.snapshotCopy heap cell.address.toNat origin (wordBytes address)
        (by simp only [Contract.Interaction.wordBytes_length]; omega))
      rw [← shape] at treeAfter
      refine .pointer type cell.address.toNat address _ range ?_ ?_ (treeAfter.weaken fresh)
      · rw [shape]; exact extent
      · rw [shape]
        simpa only [Contract.Interaction.wordBytes_length] using
          MemoryOps.snapshotCopy_contents heap cell.address.toNat (wordBytes address)

/-- Filling a later parent cell preserves an earlier cell and the fresh
subtree it owns. The two physical inequalities discharge both disjoint ranges. -/
theorem CellRep.after_value_store (represented : CellRep registry heap lower floor type address contents)
    (cell : Reference) (value : Value)
    (memory : cell.region = .memory invocation) (padded : cell.byteCell = false)
    (before : address+32 ≤ cell.address.toNat) (inside : cell.address.toNat+32 ≤ floor)
    (written : Defaults.writeMemoryValue heap cell value = .ok after) :
    CellRep registry after lower floor type address contents := by
  rcases writeMemoryValue_word cell value memory padded written with ⟨word, _, _, shape⟩
  have preserved : after.execution.memory.read address 32 = heap.execution.memory.read address 32 := by
    rw [shape]
    exact MemoryOps.snapshotCopy_frame heap cell.address.toNat (wordBytes word) address 32 (Or.inl before)
  cases represented with
  | scalar type address contents range packet =>
      rcases packet with ⟨source, represented, encoded, same, converted, encoding, extent, bytes⟩
      refine .scalar type address contents range ⟨source, represented, encoded, same, converted, encoding, ?_, ?_⟩
      · rw [shape]; exact extent
      · exact preserved.trans bytes
  | pointer type address target contents range extent packet tree =>
      have treeAfter := tree.frame (PacketFrame.snapshotCopy heap cell.address.toNat floor (wordBytes word)
        (by simpa only [Contract.Interaction.wordBytes_length] using inside))
      rw [← shape] at treeAfter
      refine .pointer type address target contents range ?_ (preserved.trans packet) treeAfter
      rw [shape]; exact extent

def MakesValueRep (registry : Registry) (materialize : Materialize) : Prop :=
  ∀ budget heap type contents value after remaining,
    MemoryOps.validFrontier heap = true →
    materialize budget heap type contents = .ok (value, after, remaining) →
    ValueRep registry after heap.nextMemory type contents value

structure CellStep (registry : Registry) (before after : Heap) (lower floor : Nat)
    (type : SType) (address : Nat) (contents : Contents) : Prop where
  valid : MemoryOps.validFrontier after = true
  frontier : floor ≤ after.nextMemory
  current : CellRep registry after lower floor type address contents
  previous : ∀ oldType oldAddress oldContents, oldAddress+32 ≤ address →
    CellRep registry before lower floor oldType oldAddress oldContents →
    CellRep registry after lower floor oldType oldAddress oldContents

theorem advance_memory_padded (region : reference.region = .memory invocation)
    (advanced : Access.advance reference bytes = .ok target) : target.byteCell = false := by
  unfold Access.advance at advanced
  simp only [region] at advanced
  split at advanced
  · cases advanced; rfl
  · cases advanced

theorem memoryCell_rep (materialize : Materialize) (correct : MakesValueRep registry materialize)
    (safe : MakesMemoryExtension materialize) (data : Reference) (type : SType)
    (region : data.region = .memory invocation) (valid : MemoryOps.validFrontier heap = true)
    (minimum : 96 ≤ lower)
    (range : lower ≤ data.address.toNat+entry.2*32 ∧ data.address.toNat+entry.2*32+32 ≤ floor)
    (frontier : floor ≤ heap.nextMemory)
    (written : memoryCell materialize data type (heap, budget) entry = .ok (after, remaining)) :
    CellStep registry heap after lower floor (atLocation type .memory false)
      (data.address.toNat+entry.2*32) entry.1 := by
  unfold memoryCell at written
  cases made : materialize budget heap (atLocation type .memory false) entry.1 with
  | error failure => simp [made] at written <;> cases written
  | ok result =>
      rcases result with ⟨value, built, rest⟩
      have represented := correct budget heap _ entry.1 value built rest valid made
      have extension := safe budget heap _ entry.1 value built rest made
      have builtValid := extension.valid valid
      simp only [made, Bind.bind, Except.bind] at written
      cases reserved : reserve rest 32 with
      | error failure => simp [reserved] at written <;> cases written
      | ok available =>
          simp only [reserved] at written
          cases advanced : Access.advance data (entry.2*32) with
          | error failure => simp [advanced] at written <;> cases written
          | ok cell =>
              have position := advance_memory data (entry.2*32) region advanced
              have padded := advance_memory_padded region advanced
              simp only [advanced] at written
              cases stored : Defaults.writeMemoryValue built cell value with
              | error failure => simp [stored] at written <;> cases written
              | ok final =>
                  have finalFrame := writeMemoryValue_extension cell value position.1 (Nat.zero_le _) stored
                  have current := writeMemoryValue_rep represented cell position.1 padded
                    (by simpa only [position.2] using range) frontier stored
                  simp only [stored] at written
                  cases written
                  refine ⟨finalFrame.valid builtValid, Nat.le_trans frontier (Nat.le_trans extension.grows finalFrame.grows), ?_, ?_⟩
                  · simpa only [position.2] using current
                  · intro oldType oldAddress oldContents before old
                    have oldBuilt := old.frame ((extension.packetFrame valid).weaken minimum)
                    exact oldBuilt.after_value_store cell value position.1 padded
                      (by simpa only [position.2] using before)
                      (by simpa only [position.2] using range.2) stored

theorem fillMemory_rep (materialize : Materialize) (correct : MakesValueRep registry materialize)
    (safe : MakesMemoryExtension materialize) (items : List α) (typeOf : α → SType) (contentsOf : α → Contents)
    (data : Reference) (region : data.region = .memory invocation)
    (valid : MemoryOps.validFrontier heap = true) (minimum : 96 ≤ lower)
    (base : lower ≤ data.address.toNat) (span : data.address.toNat+items.length*32 ≤ floor)
    (frontier : floor ≤ heap.nextMemory)
    (written : items.zipIdx.foldlM
      (fun state entry => memoryCell materialize data (typeOf entry.1) state (contentsOf entry.1, entry.2))
      (heap, budget) = .ok (after, remaining)) :
    ∀ index item, items[index]? = some item →
      CellRep registry after lower floor (atLocation (typeOf item) .memory false)
        (data.address.toNat+index*32) (contentsOf item) := by
  let property := fun stop (state : Heap × Nat) =>
    MemoryOps.validFrontier state.1 = true ∧ floor ≤ state.1.nextMemory ∧
      ∀ index item, index < stop → items[index]? = some item →
        CellRep registry state.1 lower floor (atLocation (typeOf item) .memory false)
          (data.address.toNat+index*32) (contentsOf item)
  have initial : property 0 (heap, budget) := ⟨valid, frontier, by intro index item outside; omega⟩
  have final := foldlM_zipIdx_invariant
    (fun state entry => memoryCell materialize data (typeOf entry.1) state (contentsOf entry.1, entry.2))
    items 0 property initial (fun entry state next member prior done => by
      rcases entry with ⟨item, index⟩
      have lookup : items[index]? = some item := List.mk_mem_zipIdx_iff_getElem?.mp member
      have inside := (List.getElem?_eq_some_iff.mp lookup).1
      have step := memoryCell_rep materialize correct safe data (typeOf item) region prior.1 minimum
        (by constructor <;> dsimp only <;> omega) prior.2.1 done
      refine ⟨step.valid, step.frontier, ?_⟩
      intro earlier value before lookupEarlier
      by_cases same : earlier = index
      · subst earlier
        have sameValue : value = item := Option.some.inj (lookupEarlier.symm.trans lookup)
        subst value
        exact step.current
      · have old := prior.2.2 earlier value (by omega) lookupEarlier
        exact step.previous _ _ _ (by omega) old)
    written
  intro index item lookup
  exact final.2.2 index item (by simpa using (List.getElem?_eq_some_iff.mp lookup).1) lookup


end Solidity.Aggregates.Copy
