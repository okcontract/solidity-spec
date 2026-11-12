/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy.Laws
import Solidity.Core.Aggregates.ScalarRepresentation
import Solidity.Core.Aggregates.MemoryConstructionFrame

/-! Physical memory predicates, packet frames and typed observations. These
relations describe actual used memory, without assuming a constructor succeeds.
-/
namespace Solidity.Aggregates.Copy
open Core Static
open Contract.Interaction (Word Memory wordBytes bytesWord)

def memoryReference (heap : Heap) (address : Word) : Reference :=
  {region := .memory heap.invocation, address}

def byteType (string pointer : Bool) : SType :=
  if string then .string .memory pointer else .bytes .memory pointer

def rootSize (size : Option Nat) (length : Nat) : Nat :=
  (if size.isNone then 32 else 0)+32*length

def dataStart (address : Word) (size : Option Nat) : Nat :=
  address.toNat+(if size.isNone then 32 else 0)

/-- This is an actual scalar encoding at a physical cell, not an equation
between two executions of the materializer. -/
def ScalarPacket (heap : Heap) (type : SType) (address : Nat) (contents : Contents) : Prop :=
  ∃ source : Value, ∃ value : type.Value, ∃ word : Word,
    contents = .scalar source ∧ convertScalar type source = .ok ⟨type, value⟩ ∧
    encodeMemory type value = .ok word ∧
    heap.allocated address 32 = true ∧
    heap.execution.memory.read address 32 = wordBytes word

mutual
/-- The `lower` bound applies to every object in this freshly allocated tree.
Each pointer child additionally begins after the entire parent allocation. -/
inductive TreeRep (registry : Registry) (heap : Heap) :
    Nat → SType → Word → Contents → Prop where
  | array (element : SType) (size : Option Nat) (pointer : Bool) (address : Word)
      (values : List Contents)
      (base : lower ≤ address.toNat)
      (bounded : address.toNat+rootSize size values.length ≤ MemoryOps.maximumMemory)
      (extent : heap.allocated address.toNat (rootSize size values.length) = true)
      (length : size.all (· = values.length))
      (header : size.isNone = true → heap.execution.memory.read address.toNat 32 =
        wordBytes (BitVec.ofNat 256 values.length))
      (cells : ∀ index value, values[index]? = some value →
        CellRep registry heap lower (address.toNat+rootSize size values.length)
          (atLocation element .memory false) (dataStart address size+index*32) value) :
      TreeRep registry heap lower (.array element size .memory pointer) address (.array sourceElement values)
  | structure (identity : Nat) (pointer : Bool) (address : Word)
      (fields : List (String × SType)) (values : List Contents)
      (base : lower ≤ address.toNat)
      (bounded : address.toNat+32*fields.length ≤ MemoryOps.maximumMemory)
      (extent : heap.allocated address.toNat (32*fields.length) = true)
      (definition : registry.structFields identity = some fields)
      (length : fields.length = values.length)
      (cells : ∀ index field value, fields[index]? = some field → values[index]? = some value →
        CellRep registry heap lower (address.toNat+32*fields.length)
          (atLocation field.2 .memory false) (address.toNat+index*32) value) :
      TreeRep registry heap lower (.structType identity .memory pointer) address (.structure identity values)
  | bytes (string pointer : Bool) (address : Word) (values : List UInt8)
      (base : lower ≤ address.toNat)
      (bounded : address.toNat+32+values.length ≤ MemoryOps.maximumMemory)
      (extent : heap.allocated address.toNat (32+values.length) = true)
      (header : heap.execution.memory.read address.toNat 32 = wordBytes (BitVec.ofNat 256 values.length))
      (payload : heap.execution.memory.read (address.toNat+32) values.length = values) :
      TreeRep registry heap lower (byteType string pointer) address (.bytes string values)

/-- Pointer cells own a separate tree beginning above `floor`. Inline scalar
cells contain the canonical word encoding of their converted snapshot value. -/
inductive CellRep (registry : Registry) (heap : Heap) :
    Nat → Nat → SType → Nat → Contents → Prop where
  | scalar (type : SType) (address : Nat) (contents : Contents)
      (range : lower ≤ address ∧ address+32 ≤ floor)
      (packet : ScalarPacket heap type address contents) :
      CellRep registry heap lower floor type address contents
  | pointer (type : SType) (address : Nat) (target : Word) (contents : Contents)
      (range : lower ≤ address ∧ address+32 ≤ floor)
      (extent : heap.allocated address 32 = true)
      (packet : heap.execution.memory.read address 32 = wordBytes target)
      (tree : TreeRep registry heap floor type target contents) :
      CellRep registry heap lower floor type address contents
end

/-- Preservation is stated only for actual allocated packets. A cutoff frame
can discharge it using the checked old-allocation frontier invariant. -/
def PacketFrame (lower : Nat) (before after : Heap) : Prop :=
  ∀ address count, lower ≤ address → before.allocated address count = true →
    after.allocated address count = true ∧
      after.execution.memory.read address count = before.execution.memory.read address count

theorem PacketFrame.weaken (frame : PacketFrame lower before after) (bound : lower ≤ upper) :
    PacketFrame upper before after :=
  fun address count above extent => frame address count (Nat.le_trans bound above) extent

theorem ScalarPacket.frame (packet : ScalarPacket before type address contents)
    (frame : PacketFrame lower before after) (above : lower ≤ address) :
    ScalarPacket after type address contents := by
  rcases packet with ⟨source, value, word, same, converted, encoded, extent, bytes⟩
  have preserved := frame address 32 above extent
  exact ⟨source, value, word, same, converted, encoded, preserved.1, preserved.2.trans bytes⟩

mutual
theorem TreeRep.frame (tree : TreeRep registry before lower type address contents)
    (frame : PacketFrame lower before after) : TreeRep registry after lower type address contents := by
  cases tree with
  | array element size pointer address values base bounded extent length header cells =>
      refine .array element size pointer address values base bounded
        (frame _ _ base extent).1 length ?_ ?_
      · intro dynamic
        have contains : before.allocated address.toNat 32 = true := by
          cases size with
          | some count => cases dynamic
          | none =>
              simp only [Heap.allocated, List.any_eq_true] at extent ⊢
              rcases extent with ⟨allocation, member, bound⟩
              refine ⟨allocation, member, ?_⟩
              simp only [Bool.and_eq_true, decide_eq_true_eq] at bound ⊢
              exact ⟨bound.1, by simp only [rootSize, Option.isNone_none, ↓reduceIte] at bound; omega⟩
        exact (frame _ _ base contains).2.trans (header dynamic)
      · intro index value member
        exact CellRep.frame (cells index value member) frame
  | «structure» identity pointer address fields values base bounded extent definition length cells =>
      refine .structure identity pointer address fields values base bounded
        (frame _ _ base extent).1 definition length ?_
      intro index field value member valueMember
      exact CellRep.frame (cells index field value member valueMember) frame
  | bytes string pointer address values base bounded extent header payload =>
      have headerExtent : before.allocated address.toNat 32 = true := by
        simp only [Heap.allocated, List.any_eq_true] at extent ⊢
        rcases extent with ⟨allocation, member, bound⟩
        refine ⟨allocation, member, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at bound ⊢
        exact ⟨bound.1, by omega⟩
      have payloadExtent : before.allocated (address.toNat+32) values.length = true := by
        simp only [Heap.allocated, List.any_eq_true] at extent ⊢
        rcases extent with ⟨allocation, member, bound⟩
        refine ⟨allocation, member, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at bound ⊢
        exact ⟨by omega, by omega⟩
      exact .bytes string pointer address values base bounded (frame _ _ base extent).1
        ((frame _ _ base headerExtent).2.trans header)
        ((frame _ _ (by omega) payloadExtent).2.trans payload)
termination_by 2*sizeOf contents
decreasing_by
  all_goals
    first
    | have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? valueMember)
    | have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? member)
    simp_wf
    simp_all +arith <;> omega

theorem CellRep.frame (cell : CellRep registry before lower floor type address contents)
    (frame : PacketFrame lower before after) : CellRep registry after lower floor type address contents := by
  cases cell with
  | scalar type address contents range packet =>
      exact .scalar type address contents range (packet.frame frame range.1)
  | pointer type address target contents range extent packet tree =>
      have preserved := frame address 32 range.1 extent
      exact .pointer type address target contents range preserved.1 (preserved.2.trans packet)
        (tree.frame (frame.weaken (by omega)))
termination_by 2*sizeOf contents+1
decreasing_by simp_wf <;> omega
end

theorem allocated_subrange (heap : Heap) (base size address count : Nat)
    (extent : heap.allocated base size = true)
    (start : base ≤ address) (stop : address+count ≤ base+size) :
    heap.allocated address count = true := by
  simp only [Heap.allocated, List.any_eq_true] at extent ⊢
  rcases extent with ⟨allocation, member, bound⟩
  refine ⟨allocation, member, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at bound ⊢
  exact ⟨by omega, by omega⟩

theorem allocated_frontier (heap : Heap) (address count : Nat)
    (valid : MemoryOps.validFrontier heap = true)
    (extent : heap.allocated address count = true) : address+count ≤ heap.nextMemory := by
  simp only [Heap.allocated, List.any_eq_true] at extent
  rcases extent with ⟨allocation, member, bound⟩
  have old := MemoryOps.validFrontier_old_separate heap allocation valid member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at bound
  omega

theorem MemoryExtension.allocated (extension : MemoryExtension cutoff before after)
    (extent : before.allocated address count = true) : after.allocated address count = true := by
  simp only [Heap.allocated, List.any_eq_true] at extent ⊢
  rcases extent with ⟨allocation, member, bound⟩
  exact ⟨allocation, extension.allocations allocation member, bound⟩

theorem MemoryExtension.packetFrame (extension : MemoryExtension before.nextMemory before after)
    (valid : MemoryOps.validFrontier before = true) : PacketFrame 96 before after := by
  intro address count above extent
  have stop := allocated_frontier before address count valid extent
  refine ⟨?_, extension.reads address count above stop⟩
  simp only [Heap.allocated, List.any_eq_true] at extent ⊢
  rcases extent with ⟨allocation, member, bound⟩
  exact ⟨allocation, extension.allocations allocation member, bound⟩

theorem CellRep.weaken (cell : CellRep registry heap lower floor type address contents)
    (bound : smaller ≤ lower) : CellRep registry heap smaller floor type address contents := by
  cases cell with
  | scalar type address contents range packet =>
      exact .scalar type address contents ⟨Nat.le_trans bound range.1, range.2⟩ packet
  | pointer type address target contents range extent packet tree =>
      exact .pointer type address target contents ⟨Nat.le_trans bound range.1, range.2⟩ extent packet tree

theorem TreeRep.weaken (tree : TreeRep registry heap lower type address contents)
    (bound : smaller ≤ lower) : TreeRep registry heap smaller type address contents := by
  cases tree with
  | array element size pointer address values base bounded extent length header cells =>
      exact .array element size pointer address values (Nat.le_trans bound base) bounded extent length header
        (fun index value member => (cells index value member).weaken bound)
  | «structure» identity pointer address fields values base bounded extent definition length cells =>
      exact .structure identity pointer address fields values (Nat.le_trans bound base) bounded extent definition length
        (fun index field value member valueMember => (cells index field value member valueMember).weaken bound)
  | bytes string pointer address values base bounded extent header payload =>
      exact .bytes string pointer address values (Nat.le_trans bound base) bounded extent header payload

theorem TreeRep.base (tree : TreeRep registry heap lower type address contents) : lower ≤ address.toNat := by
  cases tree <;> assumption

theorem TreeRep.isReference (tree : TreeRep registry heap lower type address contents) : isReference type = true := by
  cases tree <;> try rfl
  simp only [byteType]
  split <;> rfl

theorem TreeRep.after_materialization (tree : TreeRep registry before lower type address contents)
    (above : 96 ≤ lower) (valid : MemoryOps.validFrontier before = true)
    (written : materializeMemory registry fuel budget before copiedType copiedContents = .ok (value, after, remaining)) :
    TreeRep registry after lower type address contents :=
  tree.frame ((materializeMemory_extension written).packetFrame valid |>.weaken above)

def ValueRep (registry : Registry) (heap : Heap) (lower : Nat) (type : SType)
    (contents : Contents) (value : Value) : Prop :=
  match contents with
  | .scalar source => convertScalar type source = .ok value
  | _ => ∃ address, retag type (memoryReference heap address) = .ok value ∧
      TreeRep registry heap lower type address contents

theorem PacketFrame.snapshotCopy (heap : Heap) (address lower : Nat) (bytes : List UInt8)
    (before : address+bytes.length ≤ lower) :
    PacketFrame lower heap (MemoryOps.snapshotCopy heap address bytes) := by
  intro offset count above extent
  exact ⟨extent, MemoryOps.snapshotCopy_frame heap address bytes offset count (Or.inr (by omega))⟩

theorem atLocation_repeat (type : SType) (first second : Location) (firstPointer secondPointer : Bool) :
    atLocation (atLocation type first firstPointer) second secondPointer = atLocation type second secondPointer := by
  cases type <;> simp only [atLocation]
  case array element size location pointer =>
    rw [atLocation_repeat element first second false false]
termination_by type

theorem storageBytes_not_reference (sized : storageBytes type = some bytes) :
    isReference type = false := by
  cases type <;> simp_all [storageBytes, isReference, referenceLocation]

theorem ScalarPacket.read (packet : ScalarPacket heap type address contents)
    (bound : address < 2^256) :
    ∃ source : Value, ∃ value : type.Value,
      contents = .scalar source ∧ convertScalar type source = .ok ⟨type, value⟩ ∧
      readScalar heap ⟨type, memoryReference heap (BitVec.ofNat 256 address)⟩ = .ok value := by
  rcases packet with ⟨source, value, word, same, converted, encoded, extent, bytes⟩
  refine ⟨source, value, same, converted, ?_⟩
  have decoded := decodeMemory_encode_success type value word encoded
  have sized := encodeMemory_storageBytes type value word encoded
  rcases sized with ⟨count, sized⟩
  simp [readScalar, sized, memoryReference, scalarCellBytes, checkExtent,
    Nat.mod_eq_of_lt bound, extent, bytes, Contract.Interaction.bytesWord_wordBytes, decoded]
  rfl

theorem ScalarPacket.accessRead (packet : ScalarPacket heap type address contents)
    (bound : address < 2^256) :
    ∃ source : Value, ∃ value : Value,
      contents = .scalar source ∧ convertScalar type source = .ok value ∧
      Access.read heap ⟨type, memoryReference heap (BitVec.ofNat 256 address)⟩ = .ok value := by
  rcases packet.read bound with ⟨source, represented, same, converted, read⟩
  refine ⟨source, ⟨type, represented⟩, same, converted, ?_⟩
  have sized : ∃ bytes, storageBytes type = some bytes := by
    rcases packet with ⟨source, value, word, _, _, encoded, _, _⟩
    exact encodeMemory_storageBytes type value word encoded
  rcases sized with ⟨bytes, sized⟩
  have location : referenceLocation type = none := by
    cases type <;> simp_all [storageBytes, referenceLocation]
  have valid : Access.validate heap ⟨type, memoryReference heap (BitVec.ofNat 256 address)⟩ = .ok () := by
    simp [Access.validate, Access.regionMatches, location, memoryReference, sized, Access.checkGuards]
    rfl
  have scalar := storageBytes_not_reference sized
  simp only [Access.read, valid, Bind.bind, Except.bind, scalar, Bool.false_eq_true, ↓reduceIte, read]
  rfl

theorem memory_readWord_packet (extent : heap.allocated address 32 = true)
    (packet : heap.execution.memory.read address 32 = wordBytes word)
    (bound : address < 2^256) :
    Access.readWord heap (memoryReference heap (BitVec.ofNat 256 address)) = .ok word := by
  simp [Access.readWord, memoryReference, checkExtent, Nat.mod_eq_of_lt bound, extent,
    packet, Contract.Interaction.bytesWord_wordBytes]
  rfl

theorem memory_validate_reference (location : referenceLocation type = some .memory) :
    Access.validate heap ⟨type, memoryReference heap address⟩ = .ok () := by
  simp [Access.validate, Access.regionMatches, location, memoryReference, Access.checkGuards]
  rfl

theorem TreeRep.location (tree : TreeRep registry heap lower type address contents) :
    referenceLocation type = some .memory := by
  cases tree <;> try rfl
  simp only [byteType]
  split <;> rfl

/-- The physical header/fixed-extent representation gives the actual typed
length operation used by subsequent source accesses. -/
theorem TreeRep.length (tree : TreeRep registry heap lower type address contents) :
    match contents with
    | .array _ values => Access.length heap ⟨type, memoryReference heap address⟩ = .ok values.length
    | .bytes _ values => Access.length heap ⟨type, memoryReference heap address⟩ = .ok values.length
    | _ => True := by
  cases tree with
  | array element size pointer address values base bounded extent length header cells =>
      have valid := memory_validate_reference (heap := heap) (address := address)
        (type := .array element size .memory pointer) rfl
      cases size with
      | some count =>
          have same : count = values.length := by simpa using length
          subst count
          simp only [Access.length, valid, Bind.bind, Except.bind]
          rfl
      | none =>
          have countBound : values.length < 2^256 := by
            have maximum : MemoryOps.maximumMemory < 2^256 := by decide
            simp only [rootSize, Option.isNone_none, ↓reduceIte] at bounded
            omega
          have rootBound : address.toNat < 2^256 := address.isLt
          have extentHeader := allocated_subrange heap address.toNat (rootSize none values.length)
            address.toNat 32 extent (Nat.le_refl _) (by simp [rootSize])
          have read := memory_readWord_packet extentHeader (header rfl) rootBound
          have readAt : Access.readWord heap (memoryReference heap address) =
              .ok (BitVec.ofNat 256 values.length) := by simpa using read
          change (do
            Access.validate heap ⟨.array element none .memory pointer, memoryReference heap address⟩
            let word ← Access.readWord heap (memoryReference heap address)
            pure word.toNat) = .ok values.length
          simp only [valid, readAt, Bind.bind, Except.bind]
          change Except.ok ((BitVec.ofNat 256 values.length).toNat) = (Except.ok values.length : Result Nat)
          simp [Nat.mod_eq_of_lt countBound]
  | «structure» => trivial
  | bytes string pointer address values base bounded extent header payload =>
      have valid := memory_validate_reference (heap := heap) (address := address)
        (type := byteType string pointer) (by cases string <;> rfl)
      have countBound : values.length < 2^256 := by
        have maximum : MemoryOps.maximumMemory < 2^256 := by decide
        omega
      have extentHeader := allocated_subrange heap address.toNat (32+values.length) address.toNat 32
        extent (Nat.le_refl _) (by omega)
      have read := memory_readWord_packet extentHeader header address.isLt
      have readAt : Access.readWord heap (memoryReference heap address) =
          .ok (BitVec.ofNat 256 values.length) := by simpa using read
      have rule : Access.length heap ⟨byteType string pointer, memoryReference heap address⟩ =
          (do
            Access.validate heap ⟨byteType string pointer, memoryReference heap address⟩
            let word ← Access.readWord heap (memoryReference heap address)
            pure word.toNat) := by cases string <;> rfl
      rw [rule]
      simp only [valid, readAt, Bind.bind, Except.bind]
      change Except.ok ((BitVec.ofNat 256 values.length).toNat) = (Except.ok values.length : Result Nat)
      simp [Nat.mod_eq_of_lt countBound]

/-- Pointer-cell lookup recovers the exact represented subtree. Scalar cells
cannot be misclassified as references because their codec has scalar size. -/
theorem CellRep.pointer_read (cell : CellRep registry heap lower floor type address contents)
    (reference : isReference type = true) (bound : address < 2^256) :
    ∃ target, Access.readWord heap (memoryReference heap (BitVec.ofNat 256 address)) = .ok target ∧
      TreeRep registry heap floor type target contents := by
  cases cell with
  | scalar type address contents range packet =>
      rcases packet with ⟨source, value, word, _, _, encoded, _, _⟩
      rcases encodeMemory_storageBytes type value word encoded with ⟨bytes, sized⟩
      have scalar := storageBytes_not_reference sized
      rw [scalar] at reference
      cases reference
  | pointer type address target contents range extent packet tree =>
      exact ⟨target, memory_readWord_packet extent packet bound, tree⟩


end Solidity.Aggregates.Copy
