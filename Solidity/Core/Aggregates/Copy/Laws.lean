/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy.Operations

namespace Solidity.Aggregates.Copy
open Core Static
open Contract.Interaction (Word Memory wordBytes bytesWord)

theorem convertScalar_type (converted : convertScalar type source = .ok value) :
    value.type = type := by
  unfold convertScalar at converted
  cases conversion : Static.convert .implicit source.type type source.value with
  | error failure => cases failure <;> simp [conversion] at converted
  | ok result => simp only [conversion] at converted; cases converted; rfl

theorem retag_reference (tagged : retag type reference = .ok value) :
    value.reference = some reference := by
  cases type <;> simp only [retag, referenceValue, Bind.bind, Except.bind, pure, Except.pure] at tagged <;>
    cases tagged <;> rfl

theorem alias_reference (aliased : alias heap type source = .ok value) :
    ∃ reference, source.reference = some reference ∧
      value.reference = some {reference with bindingCell := none} := by
  unfold alias at aliased
  cases extracted : source.reference with
  | none => simp [extracted] at aliased <;> cases aliased
  | some reference =>
      refine ⟨reference, rfl, ?_⟩
      simp only [extracted, Bind.bind, Except.bind] at aliased
      cases valid : Access.validate heap ⟨source.type, reference⟩ with
      | error failure => simp [valid] at aliased <;> cases aliased
      | ok _ =>
          simp only [valid] at aliased
          cases extent : checkExtent heap reference 0 with
          | error failure => simp [extent] at aliased <;> cases aliased
          | ok _ => exact retag_reference (by simpa [extent] using aliased)

theorem writePacket_success (memory : reference.region = .memory invocation)
    (byte : reference.byte = 0) (cell : reference.byteCell = false)
    (extent : checkExtent heap reference bytes.length = .ok ())
    (enough : bytes.length ≤ budget) :
    writePacket heap budget reference bytes = .ok
      (MemoryOps.snapshotCopy heap reference.address.toNat bytes, budget-bytes.length) := by
  simp [writePacket, memory, byte, cell, extent, reserve_sufficient _ _ enough]
  rfl

theorem writePacket_shape
    (written : writePacket heap budget reference bytes = .ok (after, remaining)) :
    after = MemoryOps.snapshotCopy heap reference.address.toNat bytes := by
  unfold writePacket at written
  cases region : reference.region <;> simp only [region] at written
  all_goals try cases written
  split at written
  · cases written
  · cases extent : checkExtent heap reference bytes.length with
    | error failure => simp [extent] at written <;> cases written
    | ok _ =>
        simp only [extent, Bind.bind, Except.bind] at written
        cases reserved : reserve budget bytes.length with
        | error failure => simp [reserved] at written <;> cases written
        | ok rest =>
            simp only [reserved] at written
            exact (congrArg (fun result : Heap × Nat => result.1) (Except.ok.inj written)).symm

/-- This representation law refers to actual bytes in the physical memory,
not to a second evaluation of the copy runner. -/
theorem writePacket_contents
    (written : writePacket heap budget reference bytes = .ok (after, remaining)) :
    after.execution.memory.read reference.address.toNat bytes.length = bytes := by
  rw [writePacket_shape written]
  exact MemoryOps.snapshotCopy_contents heap reference.address.toNat bytes

theorem writePacket_frame
    (written : writePacket heap budget reference bytes = .ok (after, remaining))
    (separate : offset+count ≤ reference.address.toNat ∨
      reference.address.toNat+bytes.length ≤ offset) :
    after.execution.memory.read offset count = heap.execution.memory.read offset count := by
  rw [writePacket_shape written]
  exact MemoryOps.snapshotCopy_frame heap reference.address.toNat bytes offset count separate

theorem bind_alias
    (planned : planTransfer registry fuel true source.type type = .ok kind)
    (isAlias : kind = .storageAlias ∨ kind = .memoryAlias ∨ kind = .calldataAlias)
    (aliased : alias heap type source = .ok value) :
    bind registry fuel budget heap type source = .ok (value, heap, budget) := by
  rcases isAlias with rfl | rfl | rfl
  all_goals simp [bind_of_plan planned, aliased]; rfl

theorem bind_scalar
    (planned : planTransfer registry fuel true source.type type = .ok .scalarConversion)
    (converted : convertScalar type source = .ok value) :
    bind registry fuel budget heap type source = .ok (value, heap, budget) := by
  simp [bind_of_plan planned, converted]
  rfl

theorem bind_memoryCopy
    (planned : planTransfer registry fuel true source.type type = .ok .memoryCopy) :
    bind registry fuel budget heap type source = (do
      let (contents, remaining) ← snapshotValue registry fuel budget heap source
      materializeMemory registry fuel remaining heap type contents) := by
  exact bind_of_plan planned

theorem materializeMemory_exhausted (registry : Registry) (budget : Nat)
    (heap : Heap) (type : SType) (contents : Contents) :
    materializeMemory registry 0 budget heap type contents = .error .exhausted := rfl

theorem writeContents_exhausted (registry : Registry) (budget : Nat)
    (heap : Heap) (place : Place) (contents : Contents) :
    writeContents registry 0 budget heap place contents = .error .exhausted := rfl

/-- A physical scalar store replaces precisely the selected packed bits.
This statement keeps actual accounts/slots; no path or Keccak injectivity is
assumed. The scalar codec theorems discharge the representation of `encoded`. -/
theorem storageScalar_physical (heap : Heap) (type : SType) (owner : BitVec 160)
    (slot : Word) (byte : Fin 32) (value : type.Value) (bytes : Nat) (encoded : Word)
    (sized : storageBytes type = some bytes) (fits : byte.val+bytes ≤ 32)
    (encoding : encodeStorage type value = .ok encoded)
    (writable : heap.execution.context.readOnly = false) :
    let word := Packed.insert (8*bytes) (8*byte.val)
      (heap.execution.world.storage (owner.setWidth 256) slot) (encoded.setWidth (8*bytes))
    writeScalar heap ⟨type, {region := .storage owner, address := slot, byte}⟩ value =
      .ok {heap with execution := {heap.execution with
        world := heap.execution.world.store (owner.setWidth 256) slot word}} := by
  simp [writeScalar, sized, Nat.not_lt.mpr fits, Slot.read, encoding, Slot.write, writable]
  rfl

theorem storageScalar_contents (heap after : Heap) (type : SType) (owner : BitVec 160)
    (slot : Word) (byte : Fin 32) (value : type.Value) (bytes : Nat) (encoded : Word)
    (sized : storageBytes type = some bytes) (fits : byte.val+bytes ≤ 32)
    (encoding : encodeStorage type value = .ok encoded)
    (writable : heap.execution.context.readOnly = false)
    (written : writeScalar heap ⟨type, {region := .storage owner, address := slot, byte}⟩ value = .ok after) :
    after.execution.world.storage (owner.setWidth 256) slot =
      Packed.insert (8*bytes) (8*byte.val) (heap.execution.world.storage (owner.setWidth 256) slot)
        (encoded.setWidth (8*bytes)) := by
  rw [storageScalar_physical heap type owner slot byte value bytes encoded sized fits encoding writable] at written
  cases written
  exact Contract.Interaction.World.store_same _ _ _ _


end Solidity.Aggregates.Copy
