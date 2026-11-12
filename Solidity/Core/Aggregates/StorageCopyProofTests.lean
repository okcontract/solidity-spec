/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.StorageCopyEffects

namespace Solidity.Aggregates.Copy.Tests
open Core Static
open Contract.Interaction (Word)

private def base : Heap :=
  MemoryOps.initialHeap {world := {storage := fun _ _ => 0xdeadbeef}}

private def left : Place := ⟨.uint 0, {region := .storage 0, address := 7}⟩
private def right : Place := ⟨.uint 0, {region := .storage 0, address := 7, byte := 1}⟩

private def stored (heap : Heap) (slot word : Word) : Heap :=
  {heap with execution := {heap.execution with world := heap.execution.world.store 0 slot word}}

private def first : Heap := stored base 7 (Packed.insert 8 0 0xdeadbeef 9)
private def last : Heap := stored first 7 (Packed.insert 8 8 (Packed.insert 8 0 0xdeadbeef 9) 13)

private theorem packedHistory : StorageActions base
    [.scalar 0 left (9#8), .scalar 0 right (13#8)] last :=
  .scalar rfl rfl (.scalar rfl rfl (.nil _))

/-- The suffix is an actual second packed-member write in the same word.
Its separation is derived from byte extents, not an assumed preservation law. -/
example : readScalar last left = .ok (9#8) := by
  apply StorageActions.scalar_readback (initial := []) rfl packedHistory
  intro bytes sized fit action member
  have one : bytes = 1 := by simpa [left, storageBytes] using sized.symm
  subst bytes
  simp only [List.mem_singleton] at member
  subst action
  simp [StorageCell.separate, left, right]

example : ¬(StorageCell.mk 0 7 8 0 (by decide)).separate (.scalar 0 left (13#8)) := by
  simp [StorageCell.separate, left, storageBytes]

/-- A neighboring byte preserves the earlier byte, but changes the earlier
whole-word packet: the whole-packet frame must reject this alias. -/
example : ¬(StorageCell.mk 0 7 256 0 (by decide)).separate (.scalar 0 right (13#8)) := by
  simp [StorageCell.separate, right, storageBytes]

private def packetFirst : Heap := stored base 7 0xface
private def packetLast : Heap := stored packetFirst 8 0x1234

private theorem packetHistory : StorageActions base
    [.physical (.store (.storage 0) 7 0xface), .physical (.store (.storage 0) 8 0x1234)] packetLast :=
  .physical (.write rfl) (.physical (.write rfl) (.nil _))

example : Slot.read packetLast (.storage 0) 7 = .ok 0xface := by
  apply StorageActions.packet_readback (initial := []) packetHistory
  intro action member
  simp only [List.mem_singleton] at member
  subst action
  simp [StorageCell.separate]

/-- Hash collisions and wrapping may make logical destinations the same slot.
The raw-store representation retains the later store rather than assuming an
injective address constructor. -/
private def collisionLast : Heap := stored packetFirst 7 0x1234

example : Slot.read collisionLast (.storage 0) 7 = .ok 0x1234 := rfl

end Solidity.Aggregates.Copy.Tests
