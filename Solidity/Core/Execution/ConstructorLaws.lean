/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Constructors
import Solidity.Core.Aggregates.DefaultAliasing

/-! Physical constructor contracts allow shared reference arguments. A root
contains actual encoded packets; no fresh-tree premise excludes an intentional
alias to an object constructed before its parent. -/
namespace Solidity.Execution.Constructors
open Static
open Aggregates
open Contract.Interaction (Word wordBytes)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

/-- Every implicit binding either preserves memory or extends it through the
existing fresh-copy builder. This covers all conversion stages of constructors. -/
theorem bind_extension
    (bound : Copy.bind registry fuel budget heap type source = .ok (value, after, remaining)) :
    Copy.MemoryExtension heap.nextMemory heap after := by
  unfold Copy.bind at bound
  cases planned : planTransfer registry fuel true source.type type with
  | error failure => simp [planned] at bound
  | ok kind =>
      simp only [planned] at bound
      cases kind with
      | scalarConversion =>
          change (do let value ← Copy.convertScalar type source; pure (value, heap, budget)) = .ok (value, after, remaining) at bound
          cases converted : Copy.convertScalar type source with
          | error failure => simp [converted] at bound
          | ok value => simp only [converted] at bound; cases bound; exact .refl _ _
      | storageAlias | memoryAlias | calldataAlias =>
          change (do let value ← Copy.alias heap type source; pure (value, heap, budget)) = .ok (value, after, remaining) at bound
          cases aliased : Copy.alias heap type source with
          | error failure => simp [aliased] at bound
          | ok value => simp only [aliased] at bound; cases bound; exact .refl _ _
      | memoryCopy =>
          change (do
            let (contents, allowance) ← Copy.snapshotValue registry fuel budget heap source
            Copy.materializeMemory registry fuel allowance heap type contents) = .ok (value, after, remaining) at bound
          cases frozen : Copy.snapshotValue registry fuel budget heap source with
          | error failure => simp [frozen] at bound
          | ok result =>
              rcases result with ⟨contents, allowance⟩
              simp only [frozen] at bound
              exact Copy.materializeMemory_extension bound
      | storageCopy => cases bound

def StateFrame (before after : MachineState σ) : Prop :=
  after.external = before.external ∧ after.locals = before.locals ∧ after.mode = before.mode ∧
    after.heap.execution.world = before.heap.execution.world ∧ after.heap.invocation = before.heap.invocation

theorem allocateArray_root
    (allocated : allocateArray registry limits (state : MachineState σ) element count = .ok (root, after)) :
    root.type = .array (atLocation element .memory false) (some count) .memory true ∧
      root.reference = MemoryOps.allocatedReference state.heap ∧
      root.reference.region = .memory state.heap.invocation ∧ root.reference.byteCell = false ∧
      root.reference.address.toNat = state.heap.nextMemory ∧
      after.heap.allocated root.reference.address.toNat (32*count) = true ∧
      Copy.MemoryExtension state.heap.nextMemory state.heap after.heap ∧ StateFrame state after := by
  unfold allocateArray at allocated
  split at allocated
  · cases allocated
  · cases checked : eligibleAt registry limits.aggregateFuel (.memory state.heap.invocation)
        (.array (atLocation element .memory false) (some count) .memory true) with
    | error failure => simp [checked] at allocated
    | ok _ =>
        simp only [checked, Bind.bind, Except.bind] at allocated
        cases sized : MemoryOps.arraySize count false false with
        | error failure => simp [sized] at allocated
        | ok size =>
            have bytes : size = 32*count := by
              simpa [Copy.rootSize] using (Copy.arraySize_rootSize (size := some 0) sized)
            simp only [sized] at allocated
            cases fresh : MemoryOps.allocate state.heap state.materializationRemaining size with
            | error failure => simp [fresh] at allocated
            | ok result =>
                rcases result with ⟨reference, heap, remaining⟩
                have extension := Copy.allocate_extension fresh (Nat.le_refl state.heap.nextMemory)
                have shape := Copy.allocate_post fresh
                have frame := MemoryOps.allocate_frame state.heap heap _ size remaining reference fresh
                simp only [fresh] at allocated
                cases allocated
                refine ⟨rfl, shape.1, extension.2.1, ?_, extension.2.2, ?_, extension.1, rfl, rfl, rfl, frame⟩
                · rw [shape.1]; rfl
                · rw [shape.2.1, extension.2.2, ← bytes]
                  exact MemoryOps.initialize_allocated state.heap size

theorem allocateStruct_root
    (allocated : allocateStruct registry limits (state : MachineState σ) identity = .ok (root, types, after)) :
    root.type = .structType identity .memory true ∧
      root.reference = MemoryOps.allocatedReference state.heap ∧
      root.reference.region = .memory state.heap.invocation ∧ root.reference.byteCell = false ∧
      root.reference.address.toNat = state.heap.nextMemory ∧
      after.heap.allocated root.reference.address.toNat (32*types.length) = true ∧
      Copy.MemoryExtension state.heap.nextMemory state.heap after.heap ∧ StateFrame state after := by
  unfold allocateStruct at allocated
  cases checked : eligibleAt registry limits.aggregateFuel (.memory state.heap.invocation) (.structType identity .memory true) with
  | error failure => simp [checked] at allocated
  | ok _ =>
      simp only [checked, Bind.bind, Except.bind] at allocated
      cases definition : registry.structFields identity with
      | none => simp [definition] at allocated
      | some fields =>
          simp only [definition, List.length_map] at allocated
          cases sized : MemoryOps.arraySize fields.length false false with
          | error failure => simp [sized] at allocated
          | ok size =>
              have bytes : size = 32*fields.length := by
                simpa [Copy.rootSize] using (Copy.arraySize_rootSize (size := some 0) sized)
              simp only [sized] at allocated
              cases fresh : MemoryOps.allocate state.heap state.materializationRemaining size with
              | error failure => simp [fresh] at allocated
              | ok result =>
                  rcases result with ⟨reference, heap, remaining⟩
                  have extension := Copy.allocate_extension fresh (Nat.le_refl state.heap.nextMemory)
                  have shape := Copy.allocate_post fresh
                  have frame := MemoryOps.allocate_frame state.heap heap _ size remaining reference fresh
                  simp only [fresh] at allocated
                  cases allocated
                  refine ⟨rfl, shape.1, extension.2.1, ?_, extension.2.2, ?_, extension.1, rfl, rfl, rfl, frame⟩
                  · rw [shape.1]; rfl
                  · simp only [List.length_map]
                    rw [shape.2.1, extension.2.2, ← bytes]
                    exact MemoryOps.initialize_allocated state.heap size

theorem writeCell_steps
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    ∃ value heap remaining cell,
      Copy.bind registry limits.aggregateFuel state.materializationRemaining state.heap type source = .ok (value, heap, remaining) ∧
      Access.advance root.reference (index*32) = .ok cell ∧
      Defaults.writeMemoryValue heap cell value = .ok after.heap ∧
      after.materializationRemaining = remaining ∧ StateFrame state after := by
  unfold writeCell at written
  change (do
    let (value, heap, remaining) ← Copy.bind registry limits.aggregateFuel state.materializationRemaining state.heap type source
    let cell ← Access.advance root.reference (index*32)
    let heap ← Defaults.writeMemoryValue heap cell value
    pure {state with heap, materializationRemaining := remaining}) = .ok after at written
  cases converted : Copy.bind registry limits.aggregateFuel state.materializationRemaining state.heap type source with
  | error failure => simp [converted] at written
  | ok result =>
      rcases result with ⟨value, heap, remaining⟩
      have frame := Copy.bind_frame converted
      simp only [converted, Bind.bind, Except.bind] at written
      cases advanced : Access.advance root.reference (index*32) with
      | error failure => simp [advanced] at written
      | ok cell =>
          simp only [advanced] at written
          cases stored : Defaults.writeMemoryValue heap cell value with
          | error failure => simp [stored] at written
          | ok final =>
              have last := Defaults.writeMemoryValue_frame heap final cell value stored
              simp only [stored] at written
              cases written
              exact ⟨value, heap, remaining, cell, rfl, rfl, stored, rfl,
                rfl, rfl, rfl, last.1.trans frame.1, last.2.1.trans frame.2⟩

/-- An actual 32-byte scalar encoding or pointer packet, without an ownership
tree restriction on the referenced object's address. -/
def EncodedCell (heap : Heap) (address : Nat) (value : Value) : Prop :=
  ∃ word, Copy.WordEncoding value word ∧ heap.allocated address 32 = true ∧
    heap.execution.memory.read address 32 = wordBytes word

theorem writeCell_packet
    (memory : root.reference.region = .memory invocation)
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    ∃ value heap remaining,
      Copy.bind registry limits.aggregateFuel state.materializationRemaining state.heap type source = .ok (value, heap, remaining) ∧
      EncodedCell after.heap (root.reference.address.toNat+index*32) value ∧
      after.materializationRemaining = remaining ∧ StateFrame state after := by
  rcases writeCell_steps written with ⟨value, heap, remaining, cell, converted, advanced, stored, budget, frame⟩
  have position := Copy.advance_memory root.reference (index*32) memory advanced
  have padded := Copy.advance_memory_padded memory advanced
  rcases Copy.writeMemoryValue_word cell value position.1 padded stored with ⟨word, encoding, extent, shape⟩
  refine ⟨value, heap, remaining, converted, ?_, budget, frame⟩
  refine ⟨word, encoding, ?_, ?_⟩
  · rw [← position.2, shape]; exact extent
  · rw [← position.2, shape]
    simpa only [Contract.Interaction.wordBytes_length] using MemoryOps.snapshotCopy_contents heap cell.address.toNat (wordBytes word)

theorem writeCell_extension
    (memory : root.reference.region = .memory invocation)
    (frontier : cutoff ≤ state.heap.nextMemory)
    (before : cutoff ≤ root.reference.address.toNat+index*32)
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    Copy.MemoryExtension cutoff state.heap after.heap := by
  rcases writeCell_steps written with ⟨value, heap, remaining, cell, converted, advanced, stored, _, _⟩
  have position := Copy.advance_memory root.reference (index*32) memory advanced
  have first := (bind_extension converted).weaken frontier
  have last := Copy.writeMemoryValue_extension cell value position.1
    (by simpa only [position.2] using before) stored
  exact first.trans last

/-- Conversion allocations cannot destroy old allocated packets, and the
actual destination store is separate when the old packet ends before it. -/
theorem writeCell_old_packet
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true)
    (above : 96 ≤ address) (extent : state.heap.allocated address count = true)
    (before : address+count ≤ root.reference.address.toNat+index*32)
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    after.heap.allocated address count = true ∧
      after.heap.execution.memory.read address count = state.heap.execution.memory.read address count := by
  have bound := Defaults.Representation.allocated_end_le_frontier valid extent
  have extension := writeCell_extension memory bound before written
  exact ⟨extension.allocated extent, extension.reads address count above (Nat.le_refl _)⟩

theorem EncodedCell.after_writeCell
    (packet : EncodedCell state.heap address value)
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true) (above : 96 ≤ address)
    (before : address+32 ≤ root.reference.address.toNat+index*32)
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    EncodedCell after.heap address value := by
  rcases packet with ⟨word, encoding, extent, bytes⟩
  have preserved := writeCell_old_packet memory valid above extent before written
  exact ⟨word, encoding, preserved.1, preserved.2.trans bytes⟩

theorem value_supported_of_noReference (value : Value) (noReference : value.reference = none) :
    value.type.scalarSupported = true := by
  rcases value with ⟨type, data⟩
  cases type <;> simp_all [Value.reference, SType.scalarSupported]
  all_goals cases data

theorem EncodedCell.scalar_rep (packet : EncodedCell heap address value) (noReference : value.reference = none) :
    Copy.ScalarPacket heap value.type address (.scalar value) := by
  rcases packet with ⟨word, encoding, extent, bytes⟩
  have supported := value_supported_of_noReference value noReference
  have converted := Static.convert_identity .implicit value.type value.value supported
    (show Static.Allowed .implicit value.type value.type from Or.inl rfl)
  refine ⟨value, value.value, word, rfl, ?_, ?_, extent, bytes⟩
  · simp only [Copy.convertScalar, converted]
  · simpa only [Copy.WordEncoding, noReference] using encoding

theorem EncodedCell.scalar_read (packet : EncodedCell heap address value)
    (noReference : value.reference = none) (bound : address < 2^256) :
    Access.read heap ⟨value.type, Copy.memoryReference heap (BitVec.ofNat 256 address)⟩ = .ok value := by
  have represented := packet.scalar_rep noReference
  rcases represented.accessRead bound with ⟨source, result, same, converted, read⟩
  cases same
  have identity := Static.convert_identity .implicit value.type value.value
    (value_supported_of_noReference value noReference)
    (show Static.Allowed .implicit value.type value.type from Or.inl rfl)
  have equal : result = value := by simpa only [Copy.convertScalar, identity, Except.ok.injEq] using converted.symm
  subst result
  exact read

theorem bind_alias_reference
    (planned : planTransfer registry fuel true source.type type = .ok kind)
    (alias : kind = .storageAlias ∨ kind = .memoryAlias ∨ kind = .calldataAlias)
    (bound : Copy.bind registry fuel budget heap type source = .ok (value, after, remaining)) :
    after = heap ∧ remaining = budget ∧ ∃ reference, source.reference = some reference ∧
      value.reference = some {reference with bindingCell := none} := by
  unfold Copy.bind at bound
  simp only [planned, Bind.bind, Except.bind] at bound
  rcases alias with rfl | rfl | rfl
  all_goals
    change (do let value ← Copy.alias heap type source; pure (value, heap, budget)) = .ok (value, after, remaining) at bound
    cases aliased : Copy.alias heap type source with
    | error failure => simp [aliased] at bound
    | ok converted =>
        have references := Copy.alias_reference aliased
        simp only [aliased, Bind.bind, Except.bind, Pure.pure, Except.pure] at bound
        cases bound
        exact ⟨rfl, rfl, references⟩

theorem EncodedCell.pointer_word (packet : EncodedCell heap address value)
    (reference : value.reference = some target) :
    heap.execution.memory.read address 32 = wordBytes target.address := by
  rcases packet with ⟨word, encoding, _, bytes⟩
  have same : word = target.address := by simpa only [Copy.WordEncoding, reference] using encoding
  exact bytes.trans (congrArg wordBytes same)

/-- A memory reference argument retains the exact address, region, slice and
lifetime descriptor. The constructor cell contains that same physical pointer. -/
theorem writeCell_alias_packet
    (memory : root.reference.region = .memory invocation)
    (planned : planTransfer registry limits.aggregateFuel true source.type type = .ok .memoryAlias)
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    ∃ original value, source.reference = some original ∧
      value.reference = some {original with bindingCell := none} ∧
      EncodedCell after.heap (root.reference.address.toNat+index*32) value ∧
      after.heap.execution.memory.read (root.reference.address.toNat+index*32) 32 = wordBytes original.address := by
  rcases writeCell_packet memory written with ⟨value, heap, remaining, converted, packet, _, _⟩
  rcases bind_alias_reference planned (Or.inr (Or.inl rfl)) converted with ⟨_, _, original, sourceRef, valueRef⟩
  exact ⟨original, value, sourceRef, valueRef, packet,
    packet.pointer_word (target := {original with bindingCell := none}) valueRef⟩

/-- Distinct constructor indices are separated by their actual 32-byte word
positions. No logical-path or hash-separation premise is used. -/
theorem earlier_cell_after_write
    (packet : EncodedCell state.heap (root.reference.address.toNat+earlier*32) value)
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true)
    (above : 96 ≤ root.reference.address.toNat) (order : earlier < later)
    (written : writeCell registry limits (state : MachineState σ) root later type source = .ok after) :
    EncodedCell after.heap (root.reference.address.toNat+earlier*32) value :=
  packet.after_writeCell memory valid (by omega) (by omega) written

theorem earlier_scalar_read_after_write
    (packet : EncodedCell state.heap (root.reference.address.toNat+earlier*32) value)
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true)
    (above : 96 ≤ root.reference.address.toNat) (order : earlier < later)
    (scalar : value.reference = none)
    (bound : root.reference.address.toNat+earlier*32 < 2^256)
    (written : writeCell registry limits (state : MachineState σ) root later type source = .ok after) :
    Access.read after.heap ⟨value.type, Copy.memoryReference after.heap
      (BitVec.ofNat 256 (root.reference.address.toNat+earlier*32))⟩ = .ok value :=
  (earlier_cell_after_write packet memory valid above order written).scalar_read scalar bound

/-- Both sides of the physical word store are framed. Conversion may allocate
new children, but it preserves every already allocated packet below the old
frontier. The destination is compared as an actual memory interval. -/
theorem writeCell_disjoint_packet
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true)
    (above : 96 ≤ address) (extent : state.heap.allocated address count = true)
    (separate : address+count ≤ root.reference.address.toNat+index*32 ∨
      root.reference.address.toNat+index*32+32 ≤ address)
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    after.heap.allocated address count = true ∧
      after.heap.execution.memory.read address count = state.heap.execution.memory.read address count := by
  rcases writeCell_steps written with ⟨value, heap, remaining, cell, converted, advanced, stored, _, _⟩
  have position := Copy.advance_memory root.reference (index*32) memory advanced
  have padded := Copy.advance_memory_padded memory advanced
  have extension := bind_extension converted
  have bound := Defaults.Representation.allocated_end_le_frontier valid extent
  rcases Copy.writeMemoryValue_word cell value position.1 padded stored with ⟨word, _, _, shape⟩
  refine ⟨?_, ?_⟩
  · rw [shape]
    exact extension.allocated extent
  · rw [shape]
    exact (MemoryOps.snapshotCopy_frame heap cell.address.toNat (wordBytes word) address count
      (by simpa only [position.2, Contract.Interaction.wordBytes_length] using separate)).trans
      (extension.reads address count above bound)

theorem EncodedCell.after_disjoint_write
    (packet : EncodedCell state.heap address value)
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true) (above : 96 ≤ address)
    (separate : address+32 ≤ root.reference.address.toNat+index*32 ∨
      root.reference.address.toNat+index*32+32 ≤ address)
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    EncodedCell after.heap address value := by
  rcases packet with ⟨word, encoding, extent, bytes⟩
  have preserved := writeCell_disjoint_packet memory valid above extent separate written
  exact ⟨word, encoding, preserved.1, preserved.2.trans bytes⟩

theorem other_cell_after_write
    (packet : EncodedCell state.heap (root.reference.address.toNat+other*32) value)
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true)
    (above : 96 ≤ root.reference.address.toNat) (different : other ≠ index)
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    EncodedCell after.heap (root.reference.address.toNat+other*32) value :=
  packet.after_disjoint_write memory valid (by omega) (by omega) written

theorem other_scalar_read_after_write
    (packet : EncodedCell state.heap (root.reference.address.toNat+other*32) value)
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true)
    (above : 96 ≤ root.reference.address.toNat) (different : other ≠ index)
    (scalar : value.reference = none) (bound : root.reference.address.toNat+other*32 < 2^256)
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    Access.read after.heap ⟨value.type, Copy.memoryReference after.heap
      (BitVec.ofNat 256 (root.reference.address.toNat+other*32))⟩ = .ok value :=
  (other_cell_after_write packet memory valid above different written).scalar_read scalar bound

theorem writeCell_validFrontier
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true)
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    MemoryOps.validFrontier after.heap = true := by
  rcases writeCell_steps written with ⟨value, heap, remaining, cell, converted, advanced, stored, _, _⟩
  have position := Copy.advance_memory root.reference (index*32) memory advanced
  have padded := Copy.advance_memory_padded memory advanced
  rcases Copy.writeMemoryValue_word cell value position.1 padded stored with ⟨word, _, _, shape⟩
  rw [shape]
  exact (bind_extension converted).valid valid

/-- An actual sequence of constructor conversion/store stages. The outputs
record the values returned by the real implicit conversions, including aliases
and newly copied references. No representation postcondition is assumed. -/
inductive CellWriteTrace (registry : Registry) (limits : Limits) (root : Place) :
    MachineState σ → List (Nat × Value) → MachineState σ → Prop where
  | nil (state) : CellWriteTrace registry limits root state [] state
  | next (index : Nat) (type : SType) (source value : Value)
      (converted : Copy.bind registry limits.aggregateFuel state.materializationRemaining state.heap type source =
        .ok (value, heap, remaining))
      (written : writeCell registry limits state root index type source = .ok middle)
      (tail : CellWriteTrace registry limits root middle values after) :
      CellWriteTrace registry limits root state ((index, value) :: values) after

theorem CellWriteTrace.validFrontier
    (trace : CellWriteTrace registry limits root state values after)
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true) :
    MemoryOps.validFrontier after.heap = true := by
  induction trace with
  | nil => exact valid
  | next _ _ _ _ _ written _ ih => exact ih (writeCell_validFrontier memory valid written)

theorem CellWriteTrace.preserves_packet
    (trace : CellWriteTrace registry limits root state values after)
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true) (above : 96 ≤ root.reference.address.toNat)
    (different : other ∉ values.map Prod.fst)
    (packet : EncodedCell state.heap (root.reference.address.toNat+other*32) value) :
    EncodedCell after.heap (root.reference.address.toNat+other*32) value := by
  induction trace with
  | nil => exact packet
  | next index _ _ _ _ written _ ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at different
      exact ih (writeCell_validFrontier memory valid written) different.2
        (other_cell_after_write packet memory valid above different.1 written)

/-- Any duplicate-free traversal of successful constructor stores represents
all its converted outputs, independently of ascending/descending index order.
This applies to the complete struct conversion/store phase and to arbitrary
permutations of the same stores. Argument evaluation is a separate phase. -/
theorem CellWriteTrace.packets
    (trace : CellWriteTrace registry limits root state values after)
    (memory : root.reference.region = .memory invocation)
    (valid : MemoryOps.validFrontier state.heap = true) (above : 96 ≤ root.reference.address.toNat)
    (distinct : (values.map Prod.fst).Nodup) :
    ∀ index value, (index, value) ∈ values →
      EncodedCell after.heap (root.reference.address.toNat+index*32) value := by
  induction trace with
  | nil => simp
  | next index type source value converted written tail ih =>
      simp only [List.map_cons, List.nodup_cons] at distinct
      intro observed result member
      rcases List.mem_cons.mp member with head | rest
      · cases head
        rcases writeCell_packet memory written with ⟨actual, heap, remaining, actualConversion, packet, _, _⟩
        rw [converted] at actualConversion
        cases actualConversion
        exact tail.preserves_packet memory (writeCell_validFrontier memory valid written) above distinct.1 packet
      · exact ih (writeCell_validFrontier memory valid written) distinct.2 observed result rest

end Solidity.Execution.Constructors
