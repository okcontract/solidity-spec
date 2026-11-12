/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Representation.Base
import Init.Data.BitVec.Lemmas

/-! Physical memory objects used by the admitted-state safety profile.
This is a representation predicate, not successful execution or reachability.
Payload cells contain uint256 words, so every complete 32-byte packet is a
well-typed element. Multiple source references may name the same object. -/
namespace Solidity.Execution.Safety.WordArena
open Static Aggregates
open Contract.Interaction (Word wordBytes bytesWord Memory)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def arrayType (pointer : Bool := true) : SType := .array (.uint 31) none .memory pointer

structure Object where
  address : Word
  length : Nat
  deriving DecidableEq, Repr

def Object.bytes (object : Object) : Nat := 32+32*object.length
def Object.reference (heap : Heap) (object : Object) : Reference := Copy.memoryReference heap object.address
def Object.place (heap : Heap) (object : Object) (pointer : Bool := true) : Place :=
  ⟨arrayType pointer, object.reference heap⟩
def Object.offset (object : Object) (index : Nat) : Nat := object.address.toNat+32+index*32
def Object.cell (heap : Heap) (object : Object) (index : Nat) : Place :=
  ⟨.uint 31, Copy.memoryReference heap (BitVec.ofNat 256 (object.offset index))⟩

structure Represents (heap : Heap) (object : Object) : Prop where
  above : 96 ≤ object.address.toNat
  bounded : object.address.toNat+object.bytes ≤ MemoryOps.maximumMemory
  extent : heap.allocated object.address.toNat object.bytes = true
  header : heap.execution.memory.read object.address.toNat 32 = wordBytes (BitVec.ofNat 256 object.length)

def Separated (first second : Object) : Prop :=
  first.address = second.address ∨ first.address.toNat+first.bytes ≤ second.address.toNat ∨
    second.address.toNat+second.bytes ≤ first.address.toNat

structure WellFormed (heap : Heap) (objects : List Object) : Prop where
  allocation : MemoryOps.validAllocationContext heap = true
  zero : heap.execution.memory.read 96 32 = wordBytes 0
  represented : ∀ object ∈ objects, Represents heap object
  separated : ∀ first ∈ objects, ∀ second ∈ objects, Separated first second

theorem Represents.length_bound (represented : Represents heap object) : object.length < 2^256 := by
  have limit : MemoryOps.maximumMemory < 2^256 := by decide
  have bounded := represented.bounded
  simp only [Object.bytes] at bounded
  omega

theorem Represents.header_extent (represented : Represents heap object) :
    heap.allocated object.address.toNat 32 = true :=
  Copy.allocated_subrange heap _ _ _ _ represented.extent (Nat.le_refl _) (by simp [Object.bytes])

theorem Represents.cell_bound (represented : Represents heap object) (inside : index < object.length) :
    object.offset index+32 ≤ object.address.toNat+object.bytes ∧ object.offset index < 2^256 := by
  have limit : MemoryOps.maximumMemory < 2^256 := by decide
  have bounded := represented.bounded
  simp only [Object.offset, Object.bytes] at bounded ⊢
  omega

theorem Represents.cell_extent (represented : Represents heap object) (inside : index < object.length) :
    heap.allocated (object.offset index) 32 = true :=
  Copy.allocated_subrange heap _ _ _ _ represented.extent (by simp only [Object.offset]; omega) (represented.cell_bound inside).1

theorem validate_word (heap : Heap) (address : Word) :
    Access.validate heap ⟨.uint 31, Copy.memoryReference heap address⟩ = .ok () := by
  simp [Access.validate, Access.regionMatches, Copy.memoryReference, isReference,
    referenceLocation, Access.checkGuards, storageBytes]

theorem Represents.length (represented : Represents heap object) (pointer : Bool) :
    Access.length heap (object.place heap pointer) = .ok object.length := by
  have validated := Copy.memory_validate_reference (heap := heap) (type := arrayType pointer)
    (address := object.address) (by rfl)
  have header := Copy.memory_readWord_packet represented.header_extent represented.header object.address.isLt
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at header
  change (do
    Access.validate heap ⟨arrayType pointer, Copy.memoryReference heap object.address⟩
    let word ← Access.readWord heap (Copy.memoryReference heap object.address)
    pure word.toNat) = .ok object.length
  simp [validated, header, Nat.mod_eq_of_lt represented.length_bound]

theorem Represents.read_cell (represented : Represents heap object) (inside : index < object.length) :
    Access.read heap (object.cell heap index) =
      .ok ⟨.uint 31, bytesWord (heap.execution.memory.read (object.offset index) 32)⟩ := by
  have extent := represented.cell_extent inside
  have bound := (represented.cell_bound inside).2
  simp only [Access.read, Object.cell, validate_word]
  simp [isReference, referenceLocation, readScalar, Copy.memoryReference,
    storageBytes, scalarCellBytes, checkExtent, extent, Nat.mod_eq_of_lt bound,
    decodeMemory, Core.Width.bits]
  change BitVec.setWidth 256 (bytesWord (heap.execution.memory.read (object.offset index) 32)) = _
  exact BitVec.setWidth_eq _

theorem Represents.write_cell (represented : Represents heap object) (inside : index < object.length) (value : Word) :
    Access.write heap (object.cell heap index) ⟨.uint 31, value⟩ =
      .ok (MemoryOps.snapshotCopy heap (object.offset index) (wordBytes value)) := by
  have extent := represented.cell_extent inside
  have bound := (represented.cell_bound inside).2
  simp only [Access.write, Object.cell, validate_word]
  simp [writeScalar, Copy.memoryReference,
    storageBytes, scalarCellBytes, checkExtent, extent, Nat.mod_eq_of_lt bound,
    encodeMemory, MemoryOps.snapshotCopy, Core.Width.bits]
  exact congrArg (fun word : Word => heap.execution.memory.write (object.offset index) (wordBytes word))
    (BitVec.setWidth_eq value)

theorem Represents.index_inside (represented : Represents heap object) (inside : index < object.length)
    (registry : Registry) (fuel : Nat) (pointer : Bool) :
    Access.index registry fuel heap (object.place heap pointer) index = .ok (object.cell heap index) := by
  have bound := (represented.cell_bound inside).2
  have headerBound : object.address.toNat+32 < 2^256 := by
    have limit : MemoryOps.maximumMemory < 2^256 := by decide
    have bounded := represented.bounded
    simp only [Object.bytes] at bounded
    omega
  have length := represented.length pointer
  have nestedBound : object.address.toNat+(32+index*32) < 2^256 := by simpa [Object.offset, Nat.add_assoc] using bound
  simp only [Access.index, Access.sourceLength, length, Bind.bind, Except.bind]
  simp only [Object.place, arrayType, Object.reference, Copy.memoryReference, Pure.pure, Except.pure]
  simp [Access.arrayData, Access.advance, headerBound, Nat.mod_eq_of_lt headerBound,
    show ¬object.length ≤ index by omega, Access.child, atLocation, isReference, referenceLocation,
    rebase, Object.cell, Object.offset, Nat.add_assoc, nestedBound, Copy.memoryReference]

theorem Represents.index_outside (represented : Represents heap object) (outside : object.length ≤ index)
    (registry : Registry) (fuel : Nat) (pointer : Bool) :
    Access.index registry fuel heap (object.place heap pointer) index = .error (.panic 0x32) := by
  have length := represented.length pointer
  simp only [Access.index, Access.sourceLength, length, Bind.bind, Except.bind]
  simp [Object.place, Object.reference, Copy.memoryReference, outside]

theorem snapshot_allocationContext (valid : MemoryOps.validAllocationContext heap = true)
    (above : 96 ≤ destination) (packet : List UInt8) :
    MemoryOps.validAllocationContext (MemoryOps.snapshotCopy heap destination packet) = true := by
  have frame := MemoryOps.snapshotCopy_frame heap destination packet 64 32 (Or.inl (by omega))
  change (MemoryOps.validFrontier heap && decide (heap.nextMemory < 2^256) &&
    (MemoryOps.snapshotCopy heap destination packet).execution.memory.read 64 32 == wordBytes (BitVec.ofNat 256 heap.nextMemory)) = true
  rw [frame]
  exact valid

theorem Represents.store_frame (represented : Represents heap object)
    (separate : object.address.toNat+32 ≤ destination ∨ destination+packet.length ≤ object.address.toNat) :
    Represents (MemoryOps.snapshotCopy heap destination packet) object where
  above := represented.above
  bounded := represented.bounded
  extent := represented.extent
  header := (MemoryOps.snapshotCopy_frame _ _ _ _ _ separate).trans represented.header

theorem WellFormed.store_cell (wellFormed : WellFormed heap objects) (member : object ∈ objects)
    (inside : index < object.length) (value : Word) :
    WellFormed (MemoryOps.snapshotCopy heap (object.offset index) (wordBytes value)) objects := by
  have selected := wellFormed.represented object member
  have cell := selected.cell_bound inside
  have above : 128 ≤ object.offset index := by
    have := selected.above
    simp only [Object.offset]
    omega
  refine ⟨snapshot_allocationContext wellFormed.allocation (by omega) _, ?_, ?_, wellFormed.separated⟩
  · exact (MemoryOps.snapshotCopy_frame _ _ _ 96 32 (Or.inl (by omega))).trans wellFormed.zero
  · intro other otherMember
    apply (wellFormed.represented other otherMember).store_frame
    have separation := wellFormed.separated object member other otherMember
    rcases separation with equal | before | after
    · left
      simp only [Object.offset, equal]
      omega
    · right
      simpa only [Contract.Interaction.wordBytes_length] using Nat.le_trans cell.1 before
    · left
      have bytes : 32 ≤ other.bytes := by simp only [Object.bytes]; omega
      simp only [Object.offset]
      omega

end Solidity.Execution.Safety.WordArena
