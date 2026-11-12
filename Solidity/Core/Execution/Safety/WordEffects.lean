/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Profile

/-! Total physical array primitives for the first admitted-state profile.
Bounds panics remain source failures; missing ownership/extent is excluded by
representation rather than assumed away by a successful-operation premise. -/
namespace Solidity.Execution.Safety.WordEffects
open Static Aggregates
open Contract.Interaction (Word bytesWord wordBytes)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem eligible_word (registry : Registry) (fuel : Nat) (invocation : Nat) :
    eligibleAt registry (fuel+1) (.memory invocation) (.uint 31) = .ok () := by rfl

theorem eligible_array (registry : Registry) (fuel : Nat) (invocation : Nat) (pointer : Bool) :
    eligibleAt registry (fuel+2) (.memory invocation) (WordArena.arrayType pointer) = .ok () := by rfl

theorem length (represented : WordArena.Represents heap object) (pointer : Bool) :
    Effects.length registry fuel heap ⟨WordArena.arrayType pointer,object.reference heap⟩ =
      .ok ⟨.uint 31,BitVec.ofNat 256 object.length⟩ := by
  have known := represented.length pointer
  dsimp only [WordArena.Object.place,WordArena.Object.reference,WordArena.arrayType,Copy.memoryReference] at known
  simp [Effects.length,Defaults.asPlace,Value.reference,WordArena.arrayType,
    WordArena.Object.reference,Copy.memoryReference,Access.sourceLength,known]

theorem index_inside {width : Core.Width} {index : BitVec width.bits}
    (represented : WordArena.Represents heap object) (inside : index.toNat < object.length)
    (pointer : Bool) :
    Effects.index registry (fuel+2) heap ⟨WordArena.arrayType pointer,object.reference heap⟩ ⟨.uint width,index⟩ =
      .ok (object.cell heap index.toNat) := by
  have known := represented.index_inside inside registry (fuel+2) pointer
  have eligible := eligible_array registry fuel heap.invocation pointer
  have valid := WordArena.validate_word heap (BitVec.ofNat 256 (object.offset index.toNat))
  have elementEligible := eligible_word registry (fuel+1) heap.invocation
  dsimp only [WordArena.Object.place,WordArena.Object.reference,WordArena.arrayType,Copy.memoryReference] at known
  dsimp only [WordArena.arrayType] at eligible
  dsimp only [Copy.memoryReference] at valid
  simp [Effects.index,Effects.unsignedNat,Effects.indexNumber,Defaults.asPlace,Value.reference,
    WordArena.arrayType,WordArena.Object.reference,Copy.memoryReference,Access.resolveChecked,
    eligible,Access.resolve,Access.step,known,WordArena.Object.cell,valid,elementEligible]

theorem index_outside {width : Core.Width} {index : BitVec width.bits}
    (represented : WordArena.Represents heap object) (outside : object.length ≤ index.toNat)
    (pointer : Bool) :
    Effects.index registry (fuel+2) heap ⟨WordArena.arrayType pointer,object.reference heap⟩ ⟨.uint width,index⟩ =
      .error (.panic 0x32) := by
  have known := represented.index_outside outside registry (fuel+2) pointer
  have eligible := eligible_array registry fuel heap.invocation pointer
  dsimp only [WordArena.Object.place,WordArena.Object.reference,WordArena.arrayType,Copy.memoryReference] at known
  dsimp only [WordArena.arrayType] at eligible
  simp [Effects.index,Effects.unsignedNat,Effects.indexNumber,Defaults.asPlace,Value.reference,
    WordArena.arrayType,WordArena.Object.reference,Copy.memoryReference,Access.resolveChecked,
    eligible,Access.resolve,Access.step,known]

theorem read_cell (represented : WordArena.Represents heap object) (inside : index < object.length) :
    Effects.readCaptured registry (fuel+1) locals heap (.heap (object.cell heap index)) =
      .ok ⟨.uint 31,bytesWord (heap.execution.memory.read (object.offset index) 32)⟩ := by
  have known := represented.read_cell inside
  have valid := WordArena.validate_word heap (BitVec.ofNat 256 (object.offset index))
  have eligible := eligible_word registry fuel heap.invocation
  dsimp only [WordArena.Object.cell,Copy.memoryReference] at known
  dsimp only [Copy.memoryReference] at valid
  simp [Effects.readCaptured,WordArena.Object.cell,Effects.reloadBinding,valid,
    Copy.memoryReference,isReference,referenceLocation,Access.readChecked,eligible,known]

theorem plan_word (registry : Registry) (fuel : Nat) (localBinding : Bool) :
    planTransfer registry (fuel+1) localBinding (.uint 31) (.uint 31) = .ok .scalarConversion := by rfl

theorem convert_word (value : Word) :
    Copy.convertScalar (.uint 31) ⟨.uint 31,value⟩ = .ok ⟨.uint 31,value⟩ := by rfl

theorem write_cell (represented : WordArena.Represents heap object) (inside : index < object.length)
    (value : Word) :
    Effects.writeCaptured registry (fuel+1) budget locals heap (.heap (object.cell heap index)) ⟨.uint 31,value⟩ =
      .ok (locals,MemoryOps.snapshotCopy heap (object.offset index) (wordBytes value),budget) := by
  have write := represented.write_cell inside value
  have valid := WordArena.validate_word heap (BitVec.ofNat 256 (object.offset index))
  simp only [Effects.writeCaptured,Copy.assign,WordArena.Object.cell] at *
  rw [valid]
  simp only [Bind.bind,Except.bind,plan_word,convert_word]
  rw [write]
  rfl

theorem HeapRep.store_cell (heapRep : HeapRep heap objects) (member : object ∈ objects)
    (inside : index < object.length) (value : Word) :
    HeapRep (MemoryOps.snapshotCopy heap (object.offset index) (wordBytes value)) objects :=
  ⟨heapRep.arena.store_cell member inside value,heapRep.sharedZero⟩

def persistent (owner : BitVec 160) (address : Word) : Place :=
  ⟨.uint 31,{region := .storage owner,address}⟩

def transient (owner : BitVec 160) (address : Word) : Place :=
  ⟨.uint 31,{region := .transient owner,address}⟩

theorem eligible_persistent (registry : Registry) (fuel : Nat) (owner : BitVec 160) :
    eligibleAt registry (fuel+1) (.storage owner) (.uint 31) = .ok () := by rfl

theorem eligible_transient (registry : Registry) (fuel : Nat) (owner : BitVec 160) :
    eligibleAt registry (fuel+1) (.transient owner) (.uint 31) = .ok () := by rfl

theorem validate_persistent (heap : Heap) (owner : BitVec 160) (address : Word) :
    Access.validate heap (persistent owner address) = .ok () := by rfl

theorem validate_transient (heap : Heap) (owner : BitVec 160) (address : Word) :
    Access.validate heap (transient owner address) = .ok () := by rfl

theorem read_persistent (heap : Heap) (owner : BitVec 160) (address : Word) :
    Effects.readCaptured registry (fuel+1) locals heap (.heap (persistent owner address)) =
      .ok ⟨.uint 31,heap.execution.world.storage (owner.setWidth 256) address⟩ := by
  have valid := validate_persistent heap owner address
  dsimp only [persistent] at valid
  simp [Effects.readCaptured,persistent,eligible_persistent,Effects.reloadBinding,
    valid,storageBytes,Access.readChecked,Access.read,readScalar,Slot.read,decodeStorage,
    isReference,referenceLocation,Packed.extract,Core.Width.bits,show (31 : Core.Width).val = 31 by rfl]
  change BitVec.setWidth 256 _ = _
  exact BitVec.setWidth_eq _

theorem read_transient (heap : Heap) (owner : BitVec 160) (address : Word) :
    Effects.readCaptured registry (fuel+1) locals heap (.heap (transient owner address)) =
      .ok ⟨.uint 31,heap.execution.world.transient owner address⟩ := by
  have valid := validate_transient heap owner address
  dsimp only [transient] at valid
  simp [Effects.readCaptured,transient,eligible_transient,Effects.reloadBinding,
    valid,storageBytes,Access.readChecked,Access.read,readScalar,Slot.read,decodeStorage,
    isReference,referenceLocation,Packed.extract,Core.Width.bits,show (31 : Core.Width).val = 31 by rfl]
  change BitVec.setWidth 256 _ = _
  exact BitVec.setWidth_eq _

theorem write_persistent (heap : Heap) (owner : BitVec 160) (address value : Word) :
    Effects.writeCaptured registry (fuel+1) budget locals heap (.heap (persistent owner address)) ⟨.uint 31,value⟩ =
      (do pure (locals,← Slot.write heap (.storage owner) address value,budget)) := by
  have valid := validate_persistent heap owner address
  dsimp only [persistent] at valid
  simp [Effects.writeCaptured,Copy.assign,persistent,valid,
    storageBytes,plan_word,convert_word,
    Access.write,writeScalar,Slot.read,encodeStorage,Packed.insert,Packed.mask,
    Core.Width.bits,show (31 : Core.Width).val = 31 by rfl]
  erw [BitVec.setWidth_eq value]
  cases Slot.write heap (.storage owner) address value <;> rfl

theorem write_transient (heap : Heap) (owner : BitVec 160) (address value : Word) :
    Effects.writeCaptured registry (fuel+1) budget locals heap (.heap (transient owner address)) ⟨.uint 31,value⟩ =
      (do pure (locals,← Slot.write heap (.transient owner) address value,budget)) := by
  have valid := validate_transient heap owner address
  dsimp only [transient] at valid
  simp [Effects.writeCaptured,Copy.assign,transient,valid,
    storageBytes,plan_word,convert_word,
    Access.write,writeScalar,Slot.read,encodeStorage,Packed.insert,Packed.mask,
    Core.Width.bits,show (31 : Core.Width).val = 31 by rfl]
  erw [BitVec.setWidth_eq value]
  cases Slot.write heap (.transient owner) address value <;> rfl

theorem HeapRep.withWorld (heapRep : HeapRep heap objects) (world : Contract.Interaction.World) :
    HeapRep {heap with execution := {heap.execution with world}} objects := by
  refine ⟨⟨heapRep.arena.allocation,heapRep.arena.zero,?_,heapRep.arena.separated⟩,heapRep.sharedZero⟩
  intro object member
  have represented := heapRep.arena.represented object member
  exact ⟨represented.above,represented.bounded,represented.extent,represented.header⟩

theorem persistent_heap_frame {owner : BitVec 160} (heapRep : HeapRep heap objects)
    (written : Slot.write heap (.storage owner) address value = .ok after) :
    HeapRep after objects ∧ after.invocation = heap.invocation := by
  unfold Slot.write at written
  split at written
  · cases written
  · cases written
    exact ⟨HeapRep.withWorld heapRep _,rfl⟩

theorem transient_heap_frame {owner : BitVec 160} (heapRep : HeapRep heap objects)
    (written : Slot.write heap (.transient owner) address value = .ok after) :
    HeapRep after objects ∧ after.invocation = heap.invocation := by
  unfold Slot.write at written
  split at written
  · cases written
  · cases written
    exact ⟨HeapRep.withWorld heapRep _,rfl⟩

end Solidity.Execution.Safety.WordEffects
