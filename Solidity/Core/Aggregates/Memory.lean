/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Types

/-! Byte memory and immutable calldata views. Allocation is a byte-zeroing
primitive; typed aggregate initialization additionally installs the appropriate
reference defaults. Its frontier follows the local codegen's
`finalizeAllocationFunction` 64-bit bound. Host materialization allowance is
separate from that source panic and from EVM gas. -/
namespace Solidity.Aggregates.MemoryOps
open Static
open Contract.Interaction (Word Memory wordBytes readBytesPadded)

def roundedSize (size : Nat) : Nat := (size + 31) / 32 * 32

theorem roundedSize_covers (size : Nat) : size ≤ roundedSize size := by
  have remainder := Nat.mod_lt (size + 31) (by decide : 0 < 32)
  have quotient := Nat.mod_add_div (size + 31) 32
  simp only [roundedSize]
  omega

theorem roundedSize_lt (size : Nat) : roundedSize size < size + 32 := by
  have remainder := Nat.mod_lt (size + 31) (by decide : 0 < 32)
  have quotient := Nat.mod_add_div (size + 31) 32
  simp only [roundedSize]
  omega

theorem roundedSize_aligned (size : Nat) : roundedSize size % 32 = 0 := by
  simp [roundedSize]

def maximumMemory : Nat := 2^64 - 1

/-- Fresh invocation memory has the conventional free pointer and zero slot.
Internal source calls reuse the heap instead of invoking this constructor. -/
def initialHeap (execution : Contract.Interaction.State := {}) (invocation : Nat := 0) : Heap :=
  let memory : Memory := Memory.write (fun _ => 0) 64 (wordBytes (BitVec.ofNat 256 128))
  { execution := { execution with memory }, invocation, nextMemory := 128, allocations := [⟨96, 32⟩] }

/-- Every old allocation lies below the frontier. No freshness claim follows
merely from the fact that the new allocation has a different logical name. -/
def validFrontier (heap : Heap) : Bool :=
  128 ≤ heap.nextMemory && heap.nextMemory % 32 == 0 &&
    heap.allocations.all (fun allocation => allocation.start + allocation.size ≤ heap.nextMemory)

/-- Raw memory may invalidate the free-pointer mirror without changing source
ownership metadata. Construction validates both before choosing an address.
The Word bound prevents a wrapped Nat mirror from hiding a corrupt frontier. -/
def validAllocationContext (heap : Heap) : Bool :=
  validFrontier heap && heap.nextMemory < 2^256 &&
    heap.execution.memory.read 64 32 == wordBytes (BitVec.ofNat 256 heap.nextMemory)

theorem validAllocationContext_frontier (valid : validAllocationContext heap = true) :
    validFrontier heap = true := by
  simp only [validAllocationContext, Bool.and_eq_true] at valid
  exact valid.1.1

/-- This helper is consumed only after allocation checks and reservation.
The reserved free-pointer word [64,96) is updated as well as the new packet. -/
def initializeBytes (heap : Heap) (size : Nat) : Heap :=
  let rounded := roundedSize size
  let next := heap.nextMemory + rounded
  let memory := (heap.execution.memory.write 64 (wordBytes (BitVec.ofNat 256 next))).write
    heap.nextMemory (List.replicate rounded 0)
  { heap with execution := { heap.execution with memory }, nextMemory := next, allocations := ⟨heap.nextMemory, rounded⟩ :: heap.allocations }

def allocatedReference (heap : Heap) : Reference :=
  { region := .memory heap.invocation, address := BitVec.ofNat 256 heap.nextMemory }

def allocate (heap : Heap) (budget size : Nat) : Result (Reference × Heap × Nat) := do
  if !validAllocationContext heap then throw (.invalidContext "invalid memory allocation context")
  if heap.nextMemory + roundedSize size > maximumMemory then throw (.panic 0x41)
  let remaining ← reserve budget (roundedSize size + 32)
  return (allocatedReference heap, initializeBytes heap size, remaining)

/-- The native array-size helper checks length before computing either a
32-byte stride or a rounded byte payload, and adds a dynamic length header. -/
def arraySize (length : Nat) (byteArray dynamic : Bool) : Result Nat :=
  if length > maximumMemory then .error (.panic 0x41) else
  .ok ((if byteArray then roundedSize length else length * 32) + if dynamic then 32 else 0)

theorem arraySize_wordBound (length size : Nat) (byteArray dynamic : Bool)
    (sized : arraySize length byteArray dynamic = .ok size) : size < 2^256 := by
  unfold arraySize at sized
  split at sized
  · cases sized
  · rename_i allowed
    have bound : length ≤ maximumMemory := by omega
    have rounded := roundedSize_lt length
    cases byteArray <;> cases dynamic <;> simp at sized
    all_goals simp only [maximumMemory] at bound; omega

theorem initialize_frontier (heap : Heap) (size : Nat) :
    (initializeBytes heap size).nextMemory = heap.nextMemory + roundedSize size := rfl

theorem initialize_world (heap : Heap) (size : Nat) :
    (initializeBytes heap size).execution.world = heap.execution.world := rfl

theorem initialHeap_frontier (execution : Contract.Interaction.State) (invocation : Nat) :
    validFrontier (initialHeap execution invocation) = true := by simp [validFrontier, initialHeap]

theorem initialHeap_allocationContext (execution : Contract.Interaction.State) (invocation : Nat) :
    validAllocationContext (initialHeap execution invocation) = true := by
  have mirror : (initialHeap execution invocation).execution.memory.read 64 32 = wordBytes 128 := by
    simpa only [initialHeap, Contract.Interaction.wordBytes_length] using
      Memory.read_write (fun _ => 0) 64 (wordBytes 128)
  simp only [validAllocationContext, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨initialHeap_frontier execution invocation, by change 128 < 2^256; decide⟩, mirror⟩

theorem initialHeap_zeroSlot (execution : Contract.Interaction.State) (invocation : Nat) :
    (initialHeap execution invocation).execution.memory.read 96 32 = List.replicate 32 0 := by
  unfold initialHeap
  dsimp only
  rw [Memory.read_write_disjoint _ 96 32 64 _ (by simp [Contract.Interaction.wordBytes_length])]
  simp [Memory.read, List.map_const']

theorem initialize_contents (heap : Heap) (size : Nat) :
    (initializeBytes heap size).execution.memory.read heap.nextMemory (roundedSize size) =
      List.replicate (roundedSize size) 0 := by
  simpa only [initializeBytes, List.length_replicate] using
    (Memory.read_write
      (heap.execution.memory.write 64
        (wordBytes (BitVec.ofNat 256 (heap.nextMemory + roundedSize size))))
      heap.nextMemory (List.replicate (roundedSize size) 0))

theorem initialize_frame (heap : Heap) (size offset count : Nat)
    (separateAllocation : offset + count ≤ heap.nextMemory ∨
      heap.nextMemory + roundedSize size ≤ offset)
    (separateHeader : offset + count ≤ 64 ∨ 96 ≤ offset) :
    (initializeBytes heap size).execution.memory.read offset count =
      heap.execution.memory.read offset count := by
  unfold initializeBytes
  dsimp only
  rw [Memory.read_write_disjoint _ offset count heap.nextMemory
    (List.replicate (roundedSize size) 0) (by simpa using separateAllocation)]
  exact Memory.read_write_disjoint _ offset count 64 _
    (by simpa [Contract.Interaction.wordBytes_length] using separateHeader)

theorem initialize_allocated (heap : Heap) (size : Nat) :
    (initializeBytes heap size).allocated heap.nextMemory size = true := by
  have covers := roundedSize_covers size
  simp [Heap.allocated, initializeBytes, covers]

theorem allocatedReference_address (heap : Heap) (size : Nat)
    (fits : heap.nextMemory + roundedSize size ≤ maximumMemory) :
    (allocatedReference heap).address.toNat = heap.nextMemory := by
  have range : heap.nextMemory < 2^256 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) fits)
      (by decide : maximumMemory < 2^256)
  simp [allocatedReference, Nat.mod_eq_of_lt range]

theorem allocatedReference_extent (heap : Heap) (size : Nat)
    (fits : heap.nextMemory + roundedSize size ≤ maximumMemory) :
    checkExtent (initializeBytes heap size) (allocatedReference heap) size = .ok () := by
  have address := allocatedReference_address heap size fits
  simp only [allocatedReference] at address
  simp [checkExtent, allocatedReference, initializeBytes, Heap.allocated, address, roundedSize_covers]

theorem initialize_freePointer (heap : Heap) (size : Nat)
    (start : 128 ≤ heap.nextMemory) :
    (initializeBytes heap size).execution.memory.read 64 32 =
      wordBytes (BitVec.ofNat 256 (heap.nextMemory + roundedSize size)) := by
  unfold initializeBytes
  dsimp only
  rw [Memory.read_write_disjoint _ 64 32 heap.nextMemory _ (Or.inl (by omega))]
  simpa only [Contract.Interaction.wordBytes_length] using
    Memory.read_write heap.execution.memory 64
      (wordBytes (BitVec.ofNat 256 (heap.nextMemory + roundedSize size)))

theorem validFrontier_old_separate (heap : Heap) (allocation : Allocation)
    (valid : validFrontier heap = true) (old : allocation ∈ heap.allocations) :
    allocation.start + allocation.size ≤ heap.nextMemory := by
  simp only [validFrontier, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at valid
  exact valid.2 allocation old

theorem initialize_preserves_frontier (heap : Heap) (size : Nat)
    (valid : validFrontier heap = true) : validFrontier (initializeBytes heap size) = true := by
  have aligned := roundedSize_aligned size
  simp only [validFrontier, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.all_eq_true] at valid ⊢
  refine ⟨⟨by simpa only [initializeBytes] using Nat.le_trans valid.1.1 (Nat.le_add_right _ _), ?_⟩, ?_⟩
  · simp [initializeBytes, Nat.add_mod, valid.1.2, aligned]
  · intro allocation member
    simp only [initializeBytes, List.mem_cons] at member
    rcases member with same | old
    · subst allocation; simp [initializeBytes]
    · exact Nat.le_trans (valid.2 allocation old) (Nat.le_add_right _ _)

theorem initialize_allocationContext (heap : Heap) (size : Nat)
    (valid : validFrontier heap = true)
    (fits : heap.nextMemory + roundedSize size ≤ maximumMemory) :
    validAllocationContext (initializeBytes heap size) = true := by
  have frontier := initialize_preserves_frontier heap size valid
  have start : 128 ≤ heap.nextMemory := by
    simp only [validFrontier, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1
  have mirror := initialize_freePointer heap size start
  have range : (initializeBytes heap size).nextMemory < 2^256 := by
    simp only [initialize_frontier]
    exact Nat.lt_of_le_of_lt fits (by decide : maximumMemory < 2^256)
  simp only [validAllocationContext, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨frontier, range⟩, by simpa only [initialize_frontier] using mirror⟩

theorem allocate_resource_failure (heap : Heap) (budget size : Nat)
    (valid : validAllocationContext heap = true)
    (oversized : maximumMemory < heap.nextMemory + roundedSize size) :
    allocate heap budget size = .error (.panic 0x41) := by
  simp [allocate, valid, oversized]
  rfl

theorem allocate_host_exhausted (heap : Heap) (budget size : Nat)
    (valid : validAllocationContext heap = true)
    (fits : heap.nextMemory + roundedSize size ≤ maximumMemory)
    (small : budget < roundedSize size + 32) :
    allocate heap budget size = .error .exhausted := by
  simp [allocate, valid, Nat.not_lt.mpr fits, reserve_exhausted _ _ small]
  rfl

theorem allocate_success (heap : Heap) (budget size : Nat)
    (valid : validAllocationContext heap = true)
    (fits : heap.nextMemory + roundedSize size ≤ maximumMemory)
    (enough : roundedSize size + 32 ≤ budget) :
    allocate heap budget size = .ok
      (allocatedReference heap, initializeBytes heap size, budget - (roundedSize size + 32)) := by
  simp [allocate, valid, Nat.not_lt.mpr fits, reserve_sufficient _ _ enough]
  rfl

theorem allocate_frame (heap after : Heap) (budget size remaining : Nat) (reference : Reference)
    (allocated : allocate heap budget size = .ok (reference, after, remaining)) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation := by
  cases valid : validAllocationContext heap with
  | false => simp [allocate, valid] at allocated; cases allocated
  | true =>
      by_cases fits : heap.nextMemory + roundedSize size ≤ maximumMemory
      · by_cases enough : roundedSize size + 32 ≤ budget
        · rw [allocate_success heap budget size valid fits enough] at allocated
          have same := congrArg (fun triple : Reference × Heap × Nat => triple.2.1) (Except.ok.inj allocated)
          cases same
          exact ⟨rfl, rfl⟩
        · rw [allocate_host_exhausted heap budget size valid fits (by omega)] at allocated
          cases allocated
      · rw [allocate_resource_failure heap budget size valid (by omega)] at allocated
        cases allocated

/-- A byte view never pads malformed source input with zero. Creation checks
the complete extent; source-level ABI admission is an input assumption. -/
def calldataView (heap : Heap) (offset length : Nat) : Result Reference :=
  if offset + length ≥ 2^256 then .error (.invalidContext "calldata address exceeds word range")
  else if offset + length ≤ heap.execution.context.calldata.length then
    .ok { region := .calldata heap.invocation, address := BitVec.ofNat 256 offset, byteCell := false, viewLength := some length }
  else .error (.revert [])

theorem checkedCalldata_no_padding (bytes : List UInt8) (offset size : Nat)
    (bound : offset + size ≤ bytes.length) :
    readBytesPadded bytes offset size = (bytes.drop offset).take size := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, readBytesPadded]
    omega
  · intro index hi hi'
    have inside : offset + index < bytes.length := by
      have : index < size := by simpa [readBytesPadded] using hi
      omega
    simp [readBytesPadded, inside]

theorem calldataView_success (heap : Heap) (offset length : Nat)
    (wordBound : offset + length < 2^256)
    (extent : offset + length ≤ heap.execution.context.calldata.length) :
    calldataView heap offset length = .ok
      { region := .calldata heap.invocation, address := BitVec.ofNat 256 offset, byteCell := false, viewLength := some length } := by
  simp [calldataView, Nat.not_le.mpr wordBound, extent]

def slice (heap : Heap) (reference : Reference) (start stop : Nat) : Result Reference := do
  let .calldata invocation := reference.region | throw .rejected
  if invocation != heap.invocation then throw (.invalidContext "foreign calldata reference")
  let some length := reference.viewLength | throw .rejected
  if start > stop || stop > length then throw (.panic 0x32)
  let _ ← checkExtent heap reference length
  if reference.address.toNat + start ≥ 2^256 then
    throw (.invalidContext "calldata slice address exceeds word range")
  return { reference with address := BitVec.ofNat 256 (reference.address.toNat + start), byte := 0, byteCell := false, viewLength := some (stop - start) }

def checkViewLength (reference : Reference) (size : Nat) : Result Unit :=
  match reference.viewLength with
  | none => .ok ()
  | some length => if size ≤ length then .ok () else .error (.panic 0x32)

def readView (heap : Heap) (budget : Nat) (reference : Reference) (size : Nat) :
    Result (List UInt8 × Nat) := do
  match reference.region with
  | .storage _ | .transient _ => throw .rejected
  | _ => pure ()
  let _ ← checkViewLength reference size
  let _ ← checkExtent heap reference size
  let remaining ← reserve budget size
  match reference.region with
  | .memory _ => return (heap.execution.memory.read reference.address.toNat size, remaining)
  | .calldata _ =>
      return (readBytesPadded heap.execution.context.calldata reference.address.toNat size, remaining)
  | _ => throw .rejected

/-- Snapshot reads precede writes, including when memory extents overlap.
This is raw byte copying; typed reference assignment is a separate operation. -/
def snapshotCopy (heap : Heap) (destination : Nat) (packet : List UInt8) : Heap :=
  let memory := heap.execution.memory.write destination packet
  { heap with execution := { heap.execution with memory } }

def copyBytes (heap : Heap) (budget : Nat) (source destination : Reference) (size : Nat) :
    Result (Heap × Nat) := do
  let .memory invocation := destination.region | throw .rejected
  if invocation != heap.invocation then throw (.invalidContext "foreign memory reference")
  let _ ← checkViewLength destination size
  let _ ← checkExtent heap destination size
  let (packet, remaining) ← readView heap budget source size
  let remaining ← reserve remaining size
  return (snapshotCopy heap destination.address.toNat packet, remaining)

theorem snapshotCopy_contents (heap : Heap) (destination : Nat) (packet : List UInt8) :
    (snapshotCopy heap destination packet).execution.memory.read destination packet.length = packet :=
  Memory.read_write _ _ _

theorem snapshotCopy_frame (heap : Heap) (destination : Nat) (packet : List UInt8)
    (offset size : Nat)
    (separate : offset + size ≤ destination ∨ destination + packet.length ≤ offset) :
    (snapshotCopy heap destination packet).execution.memory.read offset size =
      heap.execution.memory.read offset size := Memory.read_write_disjoint _ _ _ _ _ separate

theorem snapshotCopy_preserves_world (heap : Heap) (destination : Nat) (packet : List UInt8) :
    (snapshotCopy heap destination packet).execution.world = heap.execution.world := rfl

theorem snapshotCopy_overlap (heap : Heap) (source destination size : Nat) :
    (snapshotCopy heap destination (heap.execution.memory.read source size)).execution.memory.read
      destination size = heap.execution.memory.read source size := by
  have length : (heap.execution.memory.read source size).length = size := by simp [Memory.read]
  simpa only [length] using snapshotCopy_contents heap destination (heap.execution.memory.read source size)

end Solidity.Aggregates.MemoryOps
