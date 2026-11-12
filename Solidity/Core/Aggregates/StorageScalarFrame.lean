/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.StorageCopyTraversal

/-! Physical bit-field frames for storage scalar effects. Separate Solidity
members may share a packet; the frame therefore uses owner, slot and byte range
rather than treating every scalar store as overwriting its whole word. -/
namespace Solidity.Aggregates.Copy
open Core Static
open Contract.Interaction (Word)

theorem writeScalar_storage_packet {place : Place} {value : place.type.Value} {owner : BitVec 160}
    (region : place.reference.region = .storage owner)
    (written : writeScalar before place value = .ok after) :
    ∃ bytes old encoded, storageBytes place.type = some bytes ∧
      place.reference.byte.val+bytes ≤ 32 ∧
      Slot.read before place.reference.region place.reference.address = .ok old ∧
      encodeStorage place.type value = .ok encoded ∧
      Slot.write before place.reference.region place.reference.address
        (Packed.insert (8*bytes) (8*place.reference.byte.val) old (encoded.setWidth (8*bytes))) = .ok after := by
  unfold writeScalar at written
  cases sized : storageBytes place.type with
  | none => simp [sized] at written
  | some bytes =>
      simp only [sized, region, Bind.bind, Except.bind, Slot.read, Pure.pure, Except.pure] at written
      split at written
      · cases written
      · rename_i bounded
        cases encoded : encodeStorage place.type value with
        | error failure => simp [encoded] at written
        | ok word =>
            simp only [encoded] at written
            exact ⟨bytes, before.execution.world.storage (owner.setWidth 256) place.reference.address,
              word, rfl, by omega, by simp [region, Slot.read], rfl,
              by simpa only [region] using written⟩

/-- A scalar store preserves every nonoverlapping physical read field,
including a neighboring field of the same packed storage word. -/
theorem writeScalar_extract_frame {place : Place} {value : place.type.Value} {owner : BitVec 160}
    (region : place.reference.region = .storage owner)
    (written : writeScalar before place value = .ok after)
    (readBits readOffset : Nat) (readAccount readSlot : Word)
    (fits : readOffset+readBits ≤ 256)
    (separate : ∀ bytes, storageBytes place.type = some bytes →
      readAccount ≠ owner.setWidth 256 ∨ readSlot ≠ place.reference.address ∨
      readOffset+readBits ≤ 8*place.reference.byte.val ∨ 8*(place.reference.byte.val+bytes) ≤ readOffset) :
    Packed.extract readBits readOffset (after.execution.world.storage readAccount readSlot) =
      Packed.extract readBits readOffset (before.execution.world.storage readAccount readSlot) := by
  obtain ⟨bytes, old, encoded, sized, _, loaded, _, stored⟩ := writeScalar_storage_packet region written
  have packet := Slot.write_persistent stored readAccount readSlot
  have apart := separate bytes sized
  simp only [region] at packet loaded
  by_cases sameAccount : readAccount = owner.setWidth 256
  · by_cases sameSlot : readSlot = place.reference.address
    · have bits : readOffset+readBits ≤ 8*place.reference.byte.val ∨
          8*place.reference.byte.val+8*bytes ≤ readOffset := by
        rcases apart with h | h | h | h
        · exact False.elim (h sameAccount)
        · exact False.elim (h sameSlot)
        · exact Or.inl h
        · exact Or.inr (by omega)
      have oldWord : before.execution.world.storage (owner.setWidth 256) place.reference.address = old :=
        Except.ok.inj loaded
      rw [packet]
      simp only [StorageEvent.persistent, sameAccount, sameSlot, Bool.and_self]
      rw [oldWord]
      exact Packed.extract_insert_disjoint readBits readOffset (8*bytes) (8*place.reference.byte.val)
        old (encoded.setWidth (8*bytes)) fits bits
    · rw [packet]
      simp [StorageEvent.persistent, sameSlot]
  · rw [packet]
    simp [StorageEvent.persistent, sameAccount]

/-- Low-level successful scalar observations are stable under a physically
separate scalar write. The statement also preserves decoding failure, including
invalid dirty bool/enum representations and fixed-point unsupported outcomes. -/
theorem readScalar_writeScalar_disjoint {readPlace writePlace : Place}
    {value : writePlace.type.Value} {readOwner writeOwner : BitVec 160}
    (readRegion : readPlace.reference.region = .storage readOwner)
    (writeRegion : writePlace.reference.region = .storage writeOwner)
    (written : writeScalar before writePlace value = .ok after)
    (separate : ∀ readBytes writeBytes,
      storageBytes readPlace.type = some readBytes → storageBytes writePlace.type = some writeBytes →
      readOwner.setWidth 256 ≠ writeOwner.setWidth 256 ∨
      readPlace.reference.address ≠ writePlace.reference.address ∨
      readPlace.reference.byte.val+readBytes ≤ writePlace.reference.byte.val ∨
      writePlace.reference.byte.val+writeBytes ≤ readPlace.reference.byte.val) :
    readScalar after readPlace = readScalar before readPlace := by
  cases sized : storageBytes readPlace.type with
  | none => simp [readScalar, sized]
  | some bytes =>
      by_cases fits : readPlace.reference.byte.val+bytes ≤ 32
      · have packet := writeScalar_extract_frame writeRegion written (8*bytes)
          (8*readPlace.reference.byte.val) (readOwner.setWidth 256) readPlace.reference.address (by omega)
          (by
            intro writeBytes writeSized
            rcases separate bytes writeBytes sized writeSized with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl (by omega)))
            · exact Or.inr (Or.inr (Or.inr (by omega))))
        simp only [readScalar, sized, readRegion, Nat.not_lt.mpr fits, ↓reduceIte,
          Slot.read, Bind.bind, Except.bind]
        rw [packet]
      · simp [readScalar, sized, readRegion, Nat.lt_of_not_ge fits, Bind.bind, Except.bind]

end Solidity.Aggregates.Copy
