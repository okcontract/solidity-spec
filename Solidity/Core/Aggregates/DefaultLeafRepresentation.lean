/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.DefaultRepresentation
import Solidity.Core.Aggregates.Representation.Construction

namespace Solidity.Aggregates.Defaults.Representation
open Static
open Contract.Interaction (Word Memory wordBytes)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem asPlace_retag (located : asPlace value = .ok place) :
    Copy.retag place.type place.reference = .ok value := by
  rcases value with ⟨type, data⟩
  cases type <;> simp only [asPlace, Value.reference] at located <;> cases located <;> rfl

theorem emptyArray_rep (loaded : emptyReference heap = .ok reference)
    (tagged : Copy.retag (.array element none .memory pointer) reference = .ok value) :
    ∃ contents, DefaultContents registry (.array element none .memory pointer) contents ∧
      ValueRep registry heap lower (.array element none .memory pointer) contents value := by
  rcases emptyReference_packet loaded with ⟨rfl, extent, header⟩
  exact ⟨.array element [], .arrayEmpty element pointer,
    96, tagged, .emptyArray element pointer extent header⟩

theorem emptyBytes_rep (loaded : emptyReference heap = .ok reference)
    (tagged : Copy.retag (Copy.byteType string pointer) reference = .ok value) :
    ∃ contents, DefaultContents registry (Copy.byteType string pointer) contents ∧
      ValueRep registry heap lower (Copy.byteType string pointer) contents value := by
  rcases emptyReference_packet loaded with ⟨rfl, extent, header⟩
  exact ⟨.bytes string [], .bytes string pointer,
    96, tagged, .emptyBytes string pointer extent header⟩

theorem initializeBytes_zero_slice (heap : Heap) (size start count : Nat)
    (within : start + count ≤ MemoryOps.roundedSize size) :
    (MemoryOps.initializeBytes heap size).execution.memory.read (heap.nextMemory+start) count =
      List.replicate count 0 := by
  apply List.ext_getElem
  · simp [Memory.read]
  · intro index inside _
    have bound : index < count := by simpa [Memory.read] using inside
    have packetBound : heap.nextMemory+start+index-heap.nextMemory < MemoryOps.roundedSize size := by omega
    simp [MemoryOps.initializeBytes, Memory.read, Memory.write,
      show heap.nextMemory ≤ heap.nextMemory+start+index by omega,
      show heap.nextMemory+start+index < heap.nextMemory+MemoryOps.roundedSize size by omega,
      List.getElem?_replicate, packetBound]

theorem initializeLength_payload_frame (reference : Reference)
    (region : reference.region = .memory invocation) (padded : reference.byteCell = false)
    (written : initializeLength heap budget reference count true = .ok (after, remaining)) :
    after.execution.memory.read (reference.address.toNat+32) count =
      heap.execution.memory.read (reference.address.toNat+32) count := by
  unfold initializeLength at written
  cases reserved : reserve budget 32 with
  | error failure => simp [reserved] at written
  | ok allowance =>
      simp only [reserved, Bind.bind, Except.bind] at written
      cases stored : writeMemoryValue heap reference ⟨.uint 31, BitVec.ofNat 256 count⟩ with
      | error failure => simp [stored] at written
      | ok filled =>
          rcases Copy.writeMemoryValue_word reference _ region padded stored with ⟨word, _, _, shape⟩
          simp only [stored] at written
          cases written
          rw [shape]
          exact MemoryOps.snapshotCopy_frame heap reference.address.toNat (wordBytes word)
            (reference.address.toNat+32) count
            (Or.inr (by simp [Contract.Interaction.wordBytes_length]))

theorem newBytes_zero_payload
    (created : newBytes budget heap count string = .ok (value, after, remaining)) :
    after.execution.memory.read (heap.nextMemory+32) count = List.replicate count 0 := by
  unfold newBytes at created
  cases sized : MemoryOps.arraySize count true true with
  | error failure => simp [sized] at created
  | ok size =>
      have sizeEq : size = MemoryOps.roundedSize count+32 := by
        unfold MemoryOps.arraySize at sized
        split at sized
        · cases sized
        · exact (Except.ok.inj sized).symm
      simp only [sized, Bind.bind, Except.bind] at created
      cases allocated : MemoryOps.allocate heap budget size with
      | error failure => simp [allocated] at created
      | ok result =>
          rcases result with ⟨reference, fresh, allowance⟩
          have position := Copy.allocate_extension allocated (Nat.le_refl heap.nextMemory)
          have post := Copy.allocate_post allocated
          simp only [allocated] at created
          cases initialized : initializeLength fresh allowance reference count true with
          | error failure => simp [initialized] at created
          | ok result =>
              rcases result with ⟨filled, rest⟩
              have packet := initializeLength_payload_frame reference position.2.1
                (by rw [post.1]; rfl) initialized
              rw [position.2.2, post.2.1] at packet
              have covered := MemoryOps.roundedSize_covers count
              have sizeCovered := MemoryOps.roundedSize_covers size
              have zero := initializeBytes_zero_slice heap size 32 count (by omega)
              simp only [initialized] at created
              have sameHeap := congrArg (fun result : Value × Heap × Nat => result.2.1)
                (Except.ok.inj created)
              dsimp only at sameHeap
              rw [← sameHeap]
              exact packet.trans zero

theorem newBytes_rep
    (created : newBytes budget heap count string = .ok (value, after, remaining)) :
    ValueRep registry after heap.nextMemory (Copy.byteType string true)
      (.bytes string (List.replicate count 0)) value := by
  rcases Copy.newBytes_object created with ⟨reference, located, canonical, address, bounded, extent, header⟩
  have invocation := (newBytes_frame budget remaining count heap after string value created).2
  have referenceEq : reference = Copy.memoryReference after reference.address := by
    rw [canonical]
    simp [MemoryOps.allocatedReference, Copy.memoryReference, invocation]
  refine ⟨reference.address, ?_, ?_⟩
  · rw [← referenceEq]
    exact asPlace_retag located
  · apply Object.bytes string true reference.address (List.replicate count 0)
    · omega
    · simpa using bounded
    · simpa using extent
    · simpa using header
    · simpa only [address, List.length_replicate] using newBytes_zero_payload created

end Solidity.Aggregates.Defaults.Representation
