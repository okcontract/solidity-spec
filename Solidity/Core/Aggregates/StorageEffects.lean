/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.StorageScalarFrame

/-! A scalar effect retains its masked field extent. Physical events reuse the
shared storage trace. This refinement supports packed-member frames without
pretending that distinct source paths imply disjoint EVM words. -/
namespace Solidity.Aggregates.Copy
open Core Static
open Contract.Interaction (Word)

inductive StorageAction where
  | physical (event : StorageEvent)
  | scalar (owner : BitVec 160) (place : Place) (value : place.type.Value)

inductive StorageActions : Heap → List StorageAction → Heap → Prop where
  | nil (heap : Heap) : StorageActions heap [] heap
  | physical (step : StorageTrace before [event] middle) (tail : StorageActions middle actions after) :
      StorageActions before (.physical event :: actions) after
  | scalar {owner : BitVec 160} (region : place.reference.region = .storage owner)
      (written : writeScalar before place value = .ok middle) (tail : StorageActions middle actions after) :
      StorageActions before (.scalar owner place value :: actions) after

theorem StorageActions.append (first : StorageActions before initial middle)
    (last : StorageActions middle final after) : StorageActions before (initial ++ final) after := by
  induction first with
  | nil => exact last
  | physical step _ ih => exact .physical step (ih last)
  | scalar region written _ ih => exact .scalar region written (ih last)

theorem StorageActions.ofTrace (trace : StorageTrace before events after) :
    StorageActions before (events.map StorageAction.physical) after := by
  induction trace with
  | nil => exact .nil _
  | load read _ ih => exact .physical (.read read) ih
  | store written _ ih => exact .physical (.write written) ih
  | resize _ ih => exact .physical (.journal _ _ _ _ _ _) ih

theorem StorageActions.split (trace : StorageActions before (initial ++ final) after) :
    ∃ middle, StorageActions before initial middle ∧ StorageActions middle final after := by
  induction initial generalizing before with
  | nil => exact ⟨before, .nil _, trace⟩
  | cons head rest ih =>
      cases trace with
      | physical step tail =>
          obtain ⟨middle, first, last⟩ := ih tail
          exact ⟨middle, .physical step first, last⟩
      | scalar region written tail =>
          obtain ⟨middle, first, last⟩ := ih tail
          exact ⟨middle, .scalar region written first, last⟩

structure StorageCell where
  account : Word
  slot : Word
  bits : Nat
  offset : Nat
  fits : offset+bits ≤ 256

def StorageCell.observe (cell : StorageCell) (heap : Heap) : BitVec cell.bits :=
  Packed.extract cell.bits cell.offset (heap.execution.world.storage cell.account cell.slot)

def StorageCell.separate (cell : StorageCell) : StorageAction → Prop
  | .physical (.store (.storage owner) slot _) => cell.account ≠ owner.setWidth 256 ∨ cell.slot ≠ slot
  | .physical _ => True
  | .scalar owner place _ => ∀ bytes, storageBytes place.type = some bytes →
      cell.account ≠ owner.setWidth 256 ∨ cell.slot ≠ place.reference.address ∨
      cell.offset+cell.bits ≤ 8*place.reference.byte.val ∨ 8*(place.reference.byte.val+bytes) ≤ cell.offset

theorem StorageCell.event_frame (cell : StorageCell) (trace : StorageTrace before [event] after)
    (separate : cell.separate (.physical event)) : cell.observe after = cell.observe before := by
  unfold StorageCell.observe
  rw [trace.persistent]
  cases event with
  | load region slot word => rfl
  | resize region slot oldLength newLength bytes => rfl
  | store region slot word =>
      cases region with
      | storage owner =>
          rcases separate with account | address
          · simp [List.foldl_cons, StorageEvent.persistent, account]
          · simp [List.foldl_cons, StorageEvent.persistent, address]
      | transient owner | memory invocation | calldata invocation => rfl

/-- The only frame premises are concrete physical separation tests. The proof
handles scalar fields by masked insertion and every other store by the shared
last-write trace law. No semantic preservation callback is assumed. -/
theorem StorageActions.cell_frame (trace : StorageActions before actions after) (cell : StorageCell)
    (separate : ∀ action ∈ actions, cell.separate action) : cell.observe after = cell.observe before := by
  induction trace with
  | nil => rfl
  | @physical before event middle actions after step tail ih =>
      have head := cell.event_frame step (separate _ (by simp))
      exact (ih (fun action member => separate action (by simp [member]))).trans head
  | @scalar before place value middle actions after owner region written tail ih =>
      have head := writeScalar_extract_frame region written cell.bits cell.offset cell.account cell.slot cell.fits
        (separate (.scalar owner place value) (by simp))
      exact (ih (fun action member => separate action (by simp [member]))).trans head

theorem StorageActions.scalar_frame {place : Place} {owner : BitVec 160}
    (region : place.reference.region = .storage owner)
    (sized : storageBytes place.type = some bytes) (fits : place.reference.byte.val+bytes ≤ 32)
    (trace : StorageActions before actions after)
    (separate : ∀ action ∈ actions,
      (StorageCell.mk (owner.setWidth 256) place.reference.address (8*bytes) (8*place.reference.byte.val) (by omega)).separate action) :
    readScalar after place = readScalar before place := by
  have packet := trace.cell_frame
    ⟨owner.setWidth 256, place.reference.address, 8*bytes, 8*place.reference.byte.val, by omega⟩ separate
  simp only [StorageCell.observe] at packet
  simp only [readScalar, sized, region, Nat.not_lt.mpr fits, ↓reduceIte, Slot.read, Bind.bind, Except.bind]
  rw [packet]

/-- Every scalar leaf stored during a recursive copy has its converted source
value at the end if the remaining actions are physically separate from that
field. Later writes to other fields of the same word are admitted. -/
theorem StorageActions.scalar_readback {place : Place} {value : place.type.Value} {owner : BitVec 160}
    (region : place.reference.region = .storage owner)
    (trace : StorageActions before (initial ++ (.scalar owner place value :: final)) after)
    (separate : ∀ bytes, storageBytes place.type = some bytes →
      ∀ fit : place.reference.byte.val+bytes ≤ 32, ∀ action ∈ final,
        (StorageCell.mk (owner.setWidth 256) place.reference.address (8*bytes) (8*place.reference.byte.val) (by omega)).separate action) :
    readScalar after place = .ok value := by
  obtain ⟨middle, _, tail⟩ := trace.split
  cases tail with
  | scalar actualRegion written suffix =>
      obtain ⟨bytes, _, _, sized, fits, _, _, _⟩ := writeScalar_storage_packet actualRegion written
      rw [suffix.scalar_frame region sized fits (separate bytes sized fits)]
      exact readScalar_writeScalar_storage _ _ _ _ _ actualRegion written

/-- Raw packet leaves (packed arrays and byte payloads) use the same produced
packet rule, with whole-word separation for the suffix. -/
theorem StorageActions.packet_readback {owner : BitVec 160}
    (trace : StorageActions before (initial ++ (.physical (.store (.storage owner) slot word) :: final)) after)
    (separate : ∀ action ∈ final, (StorageCell.mk (owner.setWidth 256) slot 256 0 (by decide)).separate action) :
    Slot.read after (.storage owner) slot = .ok word := by
  obtain ⟨middle, _, tail⟩ := trace.split
  cases tail with
  | physical stored suffix =>
      have packet := stored.persistent (owner.setWidth 256) slot
      simp [List.foldl_cons, StorageEvent.persistent] at packet
      have frame := suffix.cell_frame ⟨owner.setWidth 256, slot, 256, 0, by decide⟩ separate
      simp [StorageCell.observe, Packed.extract] at frame
      simp only [Slot.read]
      rw [frame, packet]

end Solidity.Aggregates.Copy
