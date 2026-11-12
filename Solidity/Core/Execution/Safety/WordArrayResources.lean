/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.TypedState
import Solidity.Core.Aggregates.DefaultAliasing

/-! Constructive resource adequacy for the actual uint256[] memory default
builder. The allowance is host work, independent of gas or source reachability.
The proofs derive successful primitive equations from physical extents and
budgets; successful construction is never an input assumption. -/
namespace Solidity.Execution.Safety.WordArrayResources
open Static Aggregates
open WordArena
open Contract.Interaction (Word wordBytes)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def bytes (count : Nat) : Nat := 32*count+32
def cost (count : Nat) : Nat := 66*count+96
def freshObject (heap : Heap) (count : Nat) : Object := ⟨BitVec.ofNat 256 heap.nextMemory,count⟩
def headerHeap (heap : Heap) (count : Nat) : Heap :=
  MemoryOps.snapshotCopy (MemoryOps.initializeBytes heap (bytes count)) heap.nextMemory
    (wordBytes (BitVec.ofNat 256 count))
def dataReference (heap : Heap) (object : Object) : Reference :=
  Copy.memoryReference heap (BitVec.ofNat 256 (object.address.toNat+32))

theorem rounded_bytes (count : Nat) : MemoryOps.roundedSize (bytes count) = bytes count := by
  unfold MemoryOps.roundedSize bytes
  omega

theorem context_bounds (valid : MemoryOps.validAllocationContext heap = true) :
    128 ≤ heap.nextMemory ∧ heap.nextMemory < 2^256 := by
  have frontier := MemoryOps.validAllocationContext_frontier valid
  simp only [MemoryOps.validFrontier,Bool.and_eq_true,decide_eq_true_eq] at frontier
  simp only [MemoryOps.validAllocationContext,Bool.and_eq_true,decide_eq_true_eq] at valid
  exact ⟨frontier.1.1,valid.1.2⟩

theorem headerHeap_old_extent (extent : heap.allocated address size = true) :
    (headerHeap heap count).allocated address size = true := by
  have old : heap.allocations.any (fun allocation =>
      allocation.start ≤ address && address+size ≤ allocation.start+allocation.size) = true := extent
  simp [headerHeap,MemoryOps.snapshotCopy,MemoryOps.initializeBytes,Heap.allocated,old]

theorem headerHeap_old_read (_valid : MemoryOps.validAllocationContext heap = true)
    (above : 96 ≤ address) (below : address+size ≤ heap.nextMemory) :
    (headerHeap heap count).execution.memory.read address size = heap.execution.memory.read address size := by
  exact (MemoryOps.snapshotCopy_frame _ _ _ address size (Or.inl below)).trans
    (MemoryOps.initialize_frame heap _ address size (Or.inl below) (Or.inr above))

theorem headerHeap_rep (represented : HeapRep heap objects)
    (fits : heap.nextMemory+bytes count ≤ MemoryOps.maximumMemory) :
    HeapRep (headerHeap heap count) (freshObject heap count :: objects) := by
  have valid := represented.arena.allocation
  have frontier := MemoryOps.validAllocationContext_frontier valid
  obtain ⟨above,wordBound⟩ := context_bounds valid
  have address : (freshObject heap count).address.toNat = heap.nextMemory := by
    simp [freshObject,Nat.mod_eq_of_lt wordBound]
  have oldBound (object : Object) (member : object ∈ objects) :
      object.address.toNat+object.bytes ≤ heap.nextMemory :=
    Defaults.Representation.allocated_end_le_frontier frontier (represented.arena.represented object member).extent
  have fresh : Represents (headerHeap heap count) (freshObject heap count) := by
    refine ⟨by rw [address]; omega,?_,?_,?_⟩
    · rw [address]
      simpa only [freshObject,Object.bytes,bytes,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using fits
    · rw [address]
      change (MemoryOps.initializeBytes heap (bytes count)).allocated heap.nextMemory (32+32*count) = true
      simpa only [bytes,Nat.add_comm] using MemoryOps.initialize_allocated heap (bytes count)
    · rw [address]
      simpa only [headerHeap,freshObject,Contract.Interaction.wordBytes_length] using
        MemoryOps.snapshotCopy_contents (MemoryOps.initializeBytes heap (bytes count)) heap.nextMemory
          (wordBytes (BitVec.ofNat 256 count))
  have oldRep (object : Object) (member : object ∈ objects) : Represents (headerHeap heap count) object := by
    have old := represented.arena.represented object member
    refine ⟨old.above,old.bounded,headerHeap_old_extent old.extent,?_⟩
    exact (headerHeap_old_read valid old.above (by have := oldBound object member; simp only [Object.bytes] at this; omega)).trans old.header
  refine ⟨⟨?_,?_,?_,?_⟩,headerHeap_old_extent represented.sharedZero⟩
  · exact WordArena.snapshot_allocationContext
      (MemoryOps.initialize_allocationContext heap (bytes count) frontier (by simpa only [rounded_bytes] using fits))
      (by omega) _
  · exact (headerHeap_old_read valid (Nat.le_refl 96) (by omega)).trans represented.arena.zero
  · intro object member
    rcases List.mem_cons.mp member with rfl | member
    · exact fresh
    · exact oldRep object member
  · intro first firstMember second secondMember
    rcases List.mem_cons.mp firstMember with rfl | firstMember <;>
      rcases List.mem_cons.mp secondMember with rfl | secondMember
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (by rw [address]; exact oldBound second secondMember))
    · exact Or.inr (Or.inl (by rw [address]; exact oldBound first firstMember))
    · exact represented.arena.separated first firstMember second secondMember

theorem write_word (heap : Heap) (address : Word) (value : Word)
    (extent : heap.allocated address.toNat 32 = true) :
    Defaults.writeMemoryValue heap (Copy.memoryReference heap address) ⟨.uint 31,value⟩ =
      .ok (MemoryOps.snapshotCopy heap address.toNat (wordBytes value)) := by
  simp [Defaults.writeMemoryValue,Copy.memoryReference,Value.reference,writeScalar,storageBytes,
    scalarCellBytes,checkExtent,extent,encodeMemory,MemoryOps.snapshotCopy,Core.Width.bits]
  exact congrArg (fun word : Word => heap.execution.memory.write address.toNat (wordBytes word))
    (BitVec.setWidth_eq value)

theorem advance_data (represented : Represents heap object) (inside : index < object.length) :
    Access.advance (dataReference heap object) (index*32) = .ok (object.cell heap index).reference := by
  have bounded := represented.bounded
  have limit : MemoryOps.maximumMemory < 2^256 := by decide
  have base : object.address.toNat+32 < 2^256 := by simp only [Object.bytes] at bounded; omega
  have bound : object.address.toNat+(32+32*index) < 2^256 := by
    simpa [Object.offset,Nat.mul_comm,Nat.add_assoc] using (represented.cell_bound inside).2
  simp [Access.advance,dataReference,Object.cell,Object.offset,Copy.memoryReference,rebase,
    Nat.mod_eq_of_lt base,Nat.add_assoc,Nat.mul_comm index 32,bound]

theorem heapRep_store (represented : HeapRep heap objects) (member : object ∈ objects)
    (inside : index < object.length) (value : Word) :
    HeapRep (MemoryOps.snapshotCopy heap (object.offset index) (wordBytes value)) objects :=
  ⟨represented.arena.store_cell member inside value,represented.sharedZero⟩

theorem initialize_word (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (object : Object) (index : Nat) (represented : Represents heap object)
    (inside : index < object.length) (enough : 32 ≤ budget) :
    Defaults.initializeCell (Defaults.build registry (fuel+1)) (dataReference heap object)
      (heap,budget) (.uint 31,index) =
      .ok (MemoryOps.snapshotCopy heap (object.offset index) (wordBytes 0),budget-32) := by
  have extent := represented.cell_extent inside
  have bound := (represented.cell_bound inside).2
  simp only [Defaults.initializeCell,atLocation,Defaults.build,Static.defaultScalar,
    Bind.bind,Except.bind,Pure.pure,Except.pure]
  rw [reserve_sufficient budget 32 enough,advance_data represented inside]
  dsimp only
  have stored := write_word heap (BitVec.ofNat 256 (object.offset index)) 0
    (by simpa [Nat.mod_eq_of_lt bound] using extent)
  simpa only [Object.cell,Nat.mod_eq_of_lt bound,BitVec.toNat_ofNat,Bind.bind,Except.bind,
    Pure.pure,Except.pure] using congrArg
      (fun result => result.map fun heap => (heap,budget-32)) stored

theorem initialize_words (registry : Registry) (fuel count start budget : Nat) (heap : Heap)
    (objects : List Object) (object : Object) (represented : HeapRep heap objects)
    (member : object ∈ objects) (inside : start+count ≤ object.length)
    (enough : 32*count ≤ budget) :
    ∃ after,
      ((List.replicate count (SType.uint 31)).zipIdx start).foldlM
        (Defaults.initializeCell (Defaults.build registry (fuel+1)) (dataReference heap object)) (heap,budget) =
          .ok (after,budget-32*count) ∧
      HeapRep after objects ∧ after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation := by
  induction count generalizing start budget heap with
  | zero => exact ⟨heap,by simp,represented,rfl,rfl⟩
  | succ count ih =>
      have firstInside : start < object.length := by omega
      have firstBudget : 32 ≤ budget := by omega
      let middle := MemoryOps.snapshotCopy heap (object.offset start) (wordBytes 0)
      have nextRep : HeapRep middle objects := heapRep_store represented member firstInside 0
      obtain ⟨after,tail,rep,world,invocation⟩ := ih (start+1) (budget-32) middle nextRep
        (by omega) (by omega)
      refine ⟨after,?_,rep,world,invocation⟩
      simp only [List.replicate_succ,List.zipIdx_cons,List.foldlM_cons]
      rw [initialize_word registry fuel budget heap object start
        (represented.arena.represented object member) firstInside firstBudget]
      simp only [Bind.bind,Except.bind]
      simpa only [middle,show budget-32-32*count = budget-32*(count+1) by omega] using tail

theorem eligible_array (registry : Registry) (fuel : Nat) (pointer : Bool) :
    Defaults.memoryEligible registry (fuel+2) (arrayType pointer) = .ok () := rfl

theorem initialize_length (heap : Heap) (count budget : Nat)
    (valid : MemoryOps.validAllocationContext heap = true) (enough : 32 ≤ budget) :
    Defaults.initializeLength (MemoryOps.initializeBytes heap (bytes count)) budget
      (MemoryOps.allocatedReference heap) count true = .ok (headerHeap heap count,budget-32) := by
  have bound := (context_bounds valid).2
  have allocated := MemoryOps.initialize_allocated heap (bytes count)
  have extent : (MemoryOps.initializeBytes heap (bytes count)).allocated heap.nextMemory 32 = true :=
    Copy.allocated_subrange _ _ _ _ _ allocated (Nat.le_refl _) (by simp [bytes])
  have written := write_word (MemoryOps.initializeBytes heap (bytes count)) (BitVec.ofNat 256 heap.nextMemory)
    (BitVec.ofNat 256 count) (by simpa [Nat.mod_eq_of_lt bound] using extent)
  unfold Defaults.initializeLength
  rw [reserve_sufficient budget 32 enough]
  simpa only [MemoryOps.allocatedReference,Copy.memoryReference,headerHeap,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound,Bind.bind,Except.bind,Pure.pure,Except.pure] using
    congrArg (fun result => result.map fun heap => (heap,budget-32)) written

/-- A linear host allowance suffices for every traversal and physical store of
the real default builder. Valid size/frontier bounds derive actual success. -/
theorem newArray_success (registry : Registry) (fuel budget count : Nat) (heap : Heap)
    (objects : List Object) (represented : HeapRep heap objects)
    (fits : heap.nextMemory+bytes count ≤ MemoryOps.maximumMemory) (enough : cost count ≤ budget) :
    ∃ after,
      Defaults.newArray registry (fuel+2) budget heap (.uint 31) count =
        .ok (⟨arrayType true,(freshObject heap count).reference after⟩,after,budget-cost count) ∧
      HeapRep after (freshObject heap count :: objects) ∧
      after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation := by
  have valid := represented.arena.allocation
  obtain ⟨above,bound⟩ := context_bounds valid
  have countBound : count ≤ MemoryOps.maximumMemory := by simp only [bytes] at fits; omega
  have baseBound : heap.nextMemory+32 < 2^256 := by
    have limit : MemoryOps.maximumMemory < 2^256 := by decide
    simp only [bytes] at fits
    omega
  have allocationBudget : bytes count+32 ≤ budget := by simp only [bytes,cost] at *; omega
  have headerBudget : 32 ≤ budget-(bytes count+32) := by simp only [bytes,cost] at *; omega
  have firstBudget : count ≤ budget-(bytes count+32)-32 := by simp only [bytes,cost] at *; omega
  have secondBudget : count ≤ budget-(bytes count+32)-32-count := by simp only [bytes,cost] at *; omega
  have cellsBudget : 32*count ≤ budget-(bytes count+32)-32-count-count := by simp only [bytes,cost] at *; omega
  obtain ⟨after,initialized,rep,world,invocation⟩ := initialize_words registry (fuel+1) count 0
    (budget-(bytes count+32)-32-count-count) (headerHeap heap count)
    (freshObject heap count :: objects) (freshObject heap count) (headerHeap_rep represented fits)
    (by simp) (by simp [freshObject]) cellsBudget
  refine ⟨after,?_,rep,world,invocation⟩
  have sized : MemoryOps.arraySize count false true = .ok (bytes count) := by
    simp [MemoryOps.arraySize,Nat.not_lt.mpr countBound,bytes,Nat.mul_comm]
  have allocated := MemoryOps.allocate_success heap budget (bytes count) valid
    (by simpa only [rounded_bytes] using fits) (by simpa only [rounded_bytes] using allocationBudget)
  have length := initialize_length heap count (budget-(bytes count+32)) valid headerBudget
  have data : Defaults.arrayDataReference (MemoryOps.allocatedReference heap) true =
      .ok (dataReference (headerHeap heap count) (freshObject heap count)) := by
    simp [Defaults.arrayDataReference,Access.advance,MemoryOps.allocatedReference,dataReference,
      freshObject,Copy.memoryReference,rebase,Nat.mod_eq_of_lt bound,baseBound,headerHeap,
      MemoryOps.snapshotCopy,MemoryOps.initializeBytes]
  unfold Defaults.newArray
  simp only [atLocation,↓reduceIte]
  have admitted := eligible_array registry fuel true
  unfold arrayType at admitted
  rw [admitted]
  simp only [Bind.bind,Except.bind]
  unfold Defaults.allocateArray
  rw [sized]
  simp only [Bind.bind,Except.bind]
  rw [allocated]
  dsimp only [Bind.bind,Except.bind]
  simp only [rounded_bytes] at *
  rw [length]
  dsimp only [Bind.bind,Except.bind]
  rw [data,reserve_sufficient _ count firstBudget]
  dsimp only [Bind.bind,Except.bind]
  unfold Defaults.initializeCells
  rw [List.length_replicate,reserve_sufficient _ count secondBudget]
  simp only [Bind.bind,Except.bind]
  rw [initialized]
  dsimp only [Bind.bind,Except.bind,Pure.pure,Except.pure]
  have remaining : budget-(bytes count+32)-32-count-count-32*count = budget-cost count := by
    simp only [bytes,cost]
    omega
  rw [remaining]
  congr 1
  simp [arrayType,Object.reference,Copy.memoryReference,MemoryOps.allocatedReference,
    freshObject,invocation,headerHeap]
  rfl

theorem newArray_resource_panic (registry : Registry) (fuel budget count : Nat) (heap : Heap)
    (valid : MemoryOps.validAllocationContext heap = true)
    (oversized : MemoryOps.maximumMemory < heap.nextMemory+bytes count) :
    Defaults.newArray registry (fuel+2) budget heap (.uint 31) count = .error (.panic 0x41) := by
  have admitted := eligible_array registry fuel true
  unfold arrayType at admitted
  unfold Defaults.newArray
  simp only [atLocation,↓reduceIte,admitted,Bind.bind,Except.bind]
  unfold Defaults.allocateArray
  by_cases countBound : count ≤ MemoryOps.maximumMemory
  · have sized : MemoryOps.arraySize count false true = .ok (bytes count) := by
      simp [MemoryOps.arraySize,Nat.not_lt.mpr countBound,bytes,Nat.mul_comm]
    rw [sized]
    dsimp only [Bind.bind,Except.bind]
    rw [MemoryOps.allocate_resource_failure heap budget (bytes count) valid
      (by simpa only [rounded_bytes] using oversized)]
  · simp [MemoryOps.arraySize,Nat.lt_of_not_ge countBound]

/-- Every well-formed heap has a native resource panic or a physically
represented result under this explicit linear allowance. -/
theorem newArray_total (registry : Registry) (fuel budget count : Nat) (heap : Heap)
    (objects : List Object) (represented : HeapRep heap objects) (enough : cost count ≤ budget) :
    Defaults.newArray registry (fuel+2) budget heap (.uint 31) count = .error (.panic 0x41) ∨
    ∃ after,
      Defaults.newArray registry (fuel+2) budget heap (.uint 31) count =
        .ok (⟨arrayType true,(freshObject heap count).reference after⟩,after,budget-cost count) ∧
      HeapRep after (freshObject heap count :: objects) ∧
      after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation ∧
      Copy.MemoryExtension heap.nextMemory heap after := by
  by_cases fits : heap.nextMemory+bytes count ≤ MemoryOps.maximumMemory
  · obtain ⟨after,written,rep,world,invocation⟩ := newArray_success registry fuel budget count heap objects represented fits enough
    exact Or.inr ⟨after,written,rep,world,invocation,Defaults.newArray_extension written⟩
  · exact Or.inl (newArray_resource_panic registry fuel budget count heap represented.arena.allocation (by omega))

theorem emptyReference_total (represented : HeapRep heap objects) :
    Defaults.emptyReference heap = .ok (Copy.memoryReference heap 96) := by
  have zero := represented.arena.zero
  have extent := represented.sharedZero
  simp [Defaults.emptyReference,checkExtent,extent,zero,Contract.Interaction.bytesWord_wordBytes,
    Copy.memoryReference]

/-- Dynamic word-array named returns/default locals use the actual shared
zero-slot reference. They consume neither memory nor materialization work. -/
theorem defaultArray_total (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (objects : List Object) (represented : HeapRep heap objects) (pointer : Bool) :
    Defaults.defaultValue registry (fuel+2) budget heap (arrayType pointer) =
      .ok (⟨arrayType pointer,Copy.memoryReference heap 96⟩,heap,budget) := by
  unfold Defaults.defaultValue
  rw [eligible_array registry fuel pointer]
  simp [Defaults.build,arrayType,Static.defaultScalar,emptyReference_total represented,atLocation]

end Solidity.Execution.Safety.WordArrayResources
