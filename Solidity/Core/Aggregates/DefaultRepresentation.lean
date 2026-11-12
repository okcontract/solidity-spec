/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Representation.Cells
import Solidity.Core.Aggregates.DefaultConstructionFrame

/-! Default construction uses the canonical shared zero-slot object for empty
dynamic references. These used-packet trees allow precisely that preexisting
object in addition to fresh objects above a construction frontier. In contrast,
the stronger copy TreeRep requires every pointer child to follow its parent.
Neither relation promises arbitrary unused padding or fringe bytes. -/
namespace Solidity.Aggregates.Defaults.Representation
open Static
open Contract.Interaction (Word wordBytes bytesWord)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

mutual
inductive Object (registry : Registry) (heap : Heap) : Nat → SType → Word → Contents → Prop where
  | emptyArray (element : SType) (pointer : Bool)
      (extent : heap.allocated 96 32 = true)
      (header : bytesWord (heap.execution.memory.read 96 32) = 0) :
      Object registry heap lower (.array element none .memory pointer) 96 (.array element [])
  | emptyBytes (string pointer : Bool)
      (extent : heap.allocated 96 32 = true)
      (header : bytesWord (heap.execution.memory.read 96 32) = 0) :
      Object registry heap lower (Copy.byteType string pointer) 96 (.bytes string [])
  | array (element : SType) (size : Option Nat) (pointer : Bool) (address : Word)
      (values : List Contents)
      (base : lower ≤ address.toNat)
      (bounded : address.toNat+Copy.rootSize size values.length ≤ MemoryOps.maximumMemory)
      (extent : heap.allocated address.toNat (Copy.rootSize size values.length) = true)
      (length : size.all (· = values.length))
      (header : size.isNone = true → heap.execution.memory.read address.toNat 32 =
        wordBytes (BitVec.ofNat 256 values.length))
      (cells : ∀ index value, values[index]? = some value →
        Cell registry heap lower (address.toNat+Copy.rootSize size values.length) (atLocation element .memory false)
          (Copy.dataStart address size+index*32) value) :
      Object registry heap lower (.array element size .memory pointer) address (.array sourceElement values)
  | structure (identity : Nat) (pointer : Bool) (address : Word)
      (fields : List (String × SType)) (values : List Contents)
      (base : lower ≤ address.toNat)
      (bounded : address.toNat+32*fields.length ≤ MemoryOps.maximumMemory)
      (extent : heap.allocated address.toNat (32*fields.length) = true)
      (definition : registry.structFields identity = some fields)
      (length : fields.length = values.length)
      (cells : ∀ index field value, fields[index]? = some field → values[index]? = some value →
        Cell registry heap lower (address.toNat+32*fields.length) (atLocation field.2 .memory false) (address.toNat+index*32) value) :
      Object registry heap lower (.structType identity .memory pointer) address (.structure identity values)
  | bytes (string pointer : Bool) (address : Word) (values : List UInt8)
      (base : lower ≤ address.toNat)
      (bounded : address.toNat+32+values.length ≤ MemoryOps.maximumMemory)
      (extent : heap.allocated address.toNat (32+values.length) = true)
      (header : heap.execution.memory.read address.toNat 32 = wordBytes (BitVec.ofNat 256 values.length))
      (payload : heap.execution.memory.read (address.toNat+32) values.length = values) :
      Object registry heap lower (Copy.byteType string pointer) address (.bytes string values)

inductive Cell (registry : Registry) (heap : Heap) : Nat → Nat → SType → Nat → Contents → Prop where
  | scalar (type : SType) (address : Nat) (contents : Contents)
      (range : lower ≤ address ∧ address+32 ≤ floor) (packet : Copy.ScalarPacket heap type address contents) :
      Cell registry heap lower floor type address contents
  | pointer (type : SType) (address : Nat) (target : Word) (contents : Contents)
      (range : lower ≤ address ∧ address+32 ≤ floor)
      (extent : heap.allocated address 32 = true)
      (packet : heap.execution.memory.read address 32 = wordBytes target)
      (object : Object registry heap floor type target contents) :
      Cell registry heap lower floor type address contents
end

/-- Every observed packet is fresh above `lower`, or is the shared empty
header at96. Other preexisting objects are not silently treated as fresh. -/
def Frame (lower : Nat) (before after : Heap) : Prop :=
  ∀ address count, (lower ≤ address ∨ address = 96 ∧ count = 32) →
    before.allocated address count = true →
      after.allocated address count = true ∧
        after.execution.memory.read address count = before.execution.memory.read address count

theorem Frame.of_packetFrame (packets : Copy.PacketFrame 96 before after) (above : 96 ≤ lower) :
    Frame lower before after := by
  intro address count observed extent
  apply packets address count _ extent
  rcases observed with fresh | ⟨rfl, rfl⟩
  · omega
  · exact Nat.le_refl _

theorem Frame.weaken (preserved : Frame lower before after) (bound : lower ≤ upper) :
    Frame upper before after := by
  intro address count observed extent
  apply preserved address count _ extent
  rcases observed with fresh | shared
  · exact Or.inl (Nat.le_trans bound fresh)
  · exact Or.inr shared

mutual
theorem Object.frame (object : Object registry before lower type address contents)
    (preserved : Frame lower before after) : Object registry after lower type address contents := by
  cases object with
  | emptyArray element pointer extent header =>
      have packet := preserved 96 32 (Or.inr ⟨rfl, rfl⟩) extent
      exact .emptyArray element pointer packet.1 (by rw [packet.2]; exact header)
  | emptyBytes string pointer extent header =>
      have packet := preserved 96 32 (Or.inr ⟨rfl, rfl⟩) extent
      exact .emptyBytes string pointer packet.1 (by rw [packet.2]; exact header)
  | array element size pointer address values base bounded extent length header cells =>
      have packet := preserved address.toNat (Copy.rootSize size values.length) (Or.inl base) extent
      refine .array element size pointer address values base bounded packet.1 length ?_ ?_
      · intro dynamic
        have headExtent := Copy.allocated_subrange before address.toNat _ address.toNat 32
          extent (Nat.le_refl _) (by simp [Copy.rootSize, dynamic])
        exact (preserved _ _ (Or.inl base) headExtent).2.trans (header dynamic)
      · intro index value member
        exact (cells index value member).frame preserved
  | «structure» identity pointer address fields values base bounded extent definition length cells =>
      refine .structure identity pointer address fields values base bounded
        (preserved _ _ (Or.inl base) extent).1 definition length ?_
      intro index field value member entry
      exact (cells index field value member entry).frame preserved
  | bytes string pointer address values base bounded extent header payload =>
      have headExtent := Copy.allocated_subrange before address.toNat _ address.toNat 32
        extent (Nat.le_refl _) (by omega)
      have dataExtent := Copy.allocated_subrange before address.toNat _ (address.toNat+32) values.length
        extent (by omega) (by omega)
      exact .bytes string pointer address values base bounded
        (preserved _ _ (Or.inl base) extent).1
        ((preserved _ _ (Or.inl base) headExtent).2.trans header)
        ((preserved _ _ (Or.inl (by omega)) dataExtent).2.trans payload)
termination_by 2*sizeOf contents
decreasing_by
  all_goals
    first
    | have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? entry)
    | have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? member)
    simp_wf
    simp_all +arith <;> omega

theorem Cell.frame (cell : Cell registry before lower floor type address contents)
    (preserved : Frame lower before after) : Cell registry after lower floor type address contents := by
  cases cell with
  | scalar type address contents range packet =>
      exact .scalar type address contents range
        (packet.frame (fun address count bound extent => preserved address count (Or.inl bound) extent) range.1)
  | pointer type address target contents range extent packet object =>
      have same := preserved address 32 (Or.inl range.1) extent
      exact .pointer type address target contents range same.1 (same.2.trans packet)
        (object.frame (preserved.weaken (by omega)))
termination_by 2*sizeOf contents+1
decreasing_by simp_wf <;> simp_all +arith <;> omega
end

theorem Cell.weaken (cell : Cell registry heap upper floor type address contents)
    (bound : lower ≤ upper) : Cell registry heap lower floor type address contents := by
  cases cell with
  | scalar type address contents range packet => exact .scalar type address contents ⟨Nat.le_trans bound range.1, range.2⟩ packet
  | pointer type address target contents range extent packet object =>
      exact .pointer type address target contents ⟨Nat.le_trans bound range.1, range.2⟩ extent packet object

theorem Object.weaken (object : Object registry heap upper type address contents)
    (bound : lower ≤ upper) : Object registry heap lower type address contents := by
  cases object with
  | emptyArray element pointer extent header => exact .emptyArray element pointer extent header
  | emptyBytes string pointer extent header => exact .emptyBytes string pointer extent header
  | array element size pointer address values base bounded extent length header cells =>
      exact .array element size pointer address values (Nat.le_trans bound base) bounded extent length header
        (fun index value member => (cells index value member).weaken bound)
  | «structure» identity pointer address fields values base bounded extent definition length cells =>
      exact .structure identity pointer address fields values (Nat.le_trans bound base) bounded extent definition length
        (fun index field value member entry => (cells index field value member entry).weaken bound)
  | bytes string pointer address values base bounded extent header payload =>
      exact .bytes string pointer address values (Nat.le_trans bound base) bounded extent header payload

mutual
theorem Object.of_fresh (object : Copy.TreeRep registry heap lower type address contents) :
    Object registry heap lower type address contents := by
  cases object with
  | array element size pointer address values base bounded extent length header cells =>
      exact .array element size pointer address values base bounded extent length header
        (fun index value member => Cell.of_fresh (cells index value member))
  | «structure» identity pointer address fields values base bounded extent definition length cells =>
      exact .structure identity pointer address fields values base bounded extent definition length
        (fun index field value member entry => Cell.of_fresh (cells index field value member entry))
  | bytes string pointer address values base bounded extent header payload =>
      exact .bytes string pointer address values base bounded extent header payload
termination_by 2*sizeOf contents
decreasing_by
  all_goals
    first
    | have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? entry)
    | have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? member)
    simp_wf
    simp_all +arith <;> omega

theorem Cell.of_fresh (cell : Copy.CellRep registry heap lower floor type address contents) :
    Cell registry heap lower floor type address contents := by
  cases cell with
  | scalar type address contents range packet => exact .scalar type address contents range packet
  | pointer type address target contents range extent packet object =>
      exact .pointer type address target contents range extent packet (Object.of_fresh object)
termination_by 2*sizeOf contents+1
decreasing_by simp_wf <;> simp_all +arith <;> omega
end

def ValueRep (registry : Registry) (heap : Heap) (lower : Nat) (type : SType)
    (contents : Contents) (value : Value) : Prop :=
  match contents with
  | .scalar source => Copy.convertScalar type source = .ok value
  | _ => ∃ address, Copy.retag type (Copy.memoryReference heap address) = .ok value ∧
      Object registry heap lower type address contents

inductive DefaultContents (registry : Registry) : SType → Contents → Prop where
  | scalar (type : SType) (zero : type.Value) (default : defaultScalar type = some zero) :
      DefaultContents registry type (.scalar ⟨type, zero⟩)
  | arrayEmpty (element : SType) (pointer : Bool) :
      DefaultContents registry (.array element none .memory pointer) (.array element [])
  | arrayFixed (element : SType) (count : Nat) (pointer : Bool) (values : List Contents)
      (length : values.length = count)
      (defaults : ∀ (index : Nat) value, values[index]? = some value →
        DefaultContents registry (atLocation element .memory false) value) :
      DefaultContents registry (.array element (some count) .memory pointer) (.array element values)
  | structure (identity : Nat) (pointer : Bool) (fields : List (String × SType)) (values : List Contents)
      (definition : registry.structFields identity = some fields)
      (length : values.length = fields.length)
      (defaults : ∀ (index : Nat) field value, fields[index]? = some field → values[index]? = some value →
        DefaultContents registry (atLocation field.2 .memory false) value) :
      DefaultContents registry (.structType identity .memory pointer) (.structure identity values)
  | bytes (string pointer : Bool) :
      DefaultContents registry (Copy.byteType string pointer) (.bytes string [])

/-- Memory constructors normalize nested array locations without changing the
root pointer marker. Resolved caller types are already in this form. -/
def normalizedType : SType → SType
  | .array element size .memory pointer => .array (atLocation element .memory false) size .memory pointer
  | type => type

theorem normalizedType_atLocation (type : SType) (pointer : Bool) :
    normalizedType (atLocation type .memory pointer) = atLocation type .memory pointer := by
  cases type <;> simp [normalizedType, atLocation, Copy.atLocation_repeat]

theorem defaultScalar_supported (default : defaultScalar type = some zero) :
    type.scalarSupported = true := by
  cases type <;> simp_all [defaultScalar, SType.scalarSupported]

theorem defaultScalar_rep (default : defaultScalar type = some zero) :
    DefaultContents registry type (.scalar ⟨type, zero⟩) ∧
      ValueRep registry heap lower type (.scalar ⟨type, zero⟩) ⟨type, zero⟩ := by
  refine ⟨.scalar type zero default, ?_⟩
  have converted := Static.convert_identity .implicit type zero (defaultScalar_supported default)
    (show Static.Allowed .implicit type type from Or.inl rfl)
  simp only [ValueRep, Copy.convertScalar, converted]

theorem emptyReference_packet (loaded : emptyReference heap = .ok reference) :
    reference = Copy.memoryReference heap 96 ∧ heap.allocated 96 32 = true ∧
      bytesWord (heap.execution.memory.read 96 32) = 0 := by
  cases allocated : heap.allocated 96 32 with
  | false => simp [emptyReference, checkExtent, allocated] at loaded
  | true =>
      by_cases clean : bytesWord (heap.execution.memory.read 96 32) = 0
      · have same : reference = Copy.memoryReference heap 96 := by
          simpa [emptyReference, checkExtent, allocated, clean, Copy.memoryReference] using loaded.symm
        exact ⟨same, rfl, clean⟩
      · simp [emptyReference, checkExtent, allocated] at loaded
        split at loaded
        · rename_i zero; exact False.elim (clean zero)
        · cases loaded

theorem Frame.snapshotCopy (heap : Heap) (cell origin : Nat) (packet : List UInt8)
    (before : cell+packet.length ≤ origin) (aboveZero : 128 ≤ cell) :
    Frame origin heap (MemoryOps.snapshotCopy heap cell packet) := by
  intro address count observed extent
  refine ⟨extent, ?_⟩
  apply MemoryOps.snapshotCopy_frame
  rcases observed with fresh | ⟨rfl, rfl⟩
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

theorem writeMemoryValue_rep (represented : ValueRep registry heap origin type contents value)
    (cell : Reference) (memory : cell.region = .memory invocation) (padded : cell.byteCell = false)
    (range : lower ≤ cell.address.toNat ∧ cell.address.toNat+32 ≤ floor)
    (aboveZero : 128 ≤ cell.address.toNat) (fresh : floor ≤ origin)
    (written : writeMemoryValue heap cell value = .ok after) :
    Cell registry after lower floor type cell.address.toNat contents := by
  cases contents with
  | scalar source =>
      exact .scalar type cell.address.toNat (.scalar source) range
        (Copy.writeMemoryValue_scalar_rep source value type cell represented memory padded written)
  | array sourceElement values | «structure» identity values | bytes string values =>
      rcases represented with ⟨address, tagged, object⟩
      have reference := Copy.retag_reference tagged
      rcases Copy.writeMemoryValue_word cell value memory padded written with ⟨word, encoding, extent, shape⟩
      have wordEq : word = address := by
        simpa only [Copy.WordEncoding, reference, Copy.memoryReference] using encoding
      rw [wordEq] at shape
      have objectAfter := object.frame (Frame.snapshotCopy heap cell.address.toNat origin (wordBytes address)
        (by simp only [Contract.Interaction.wordBytes_length]; omega) aboveZero)
      rw [← shape] at objectAfter
      refine .pointer type cell.address.toNat address _ range ?_ ?_ (objectAfter.weaken fresh)
      · rw [shape]; exact extent
      · rw [shape]
        simpa only [Contract.Interaction.wordBytes_length] using
          MemoryOps.snapshotCopy_contents heap cell.address.toNat (wordBytes address)

theorem Cell.after_value_store (represented : Cell registry heap lower floor type address contents)
    (cell : Reference) (value : Value)
    (memory : cell.region = .memory invocation) (padded : cell.byteCell = false)
    (before : address+32 ≤ cell.address.toNat) (inside : cell.address.toNat+32 ≤ floor)
    (aboveZero : 128 ≤ cell.address.toNat)
    (written : writeMemoryValue heap cell value = .ok after) :
    Cell registry after lower floor type address contents := by
  rcases Copy.writeMemoryValue_word cell value memory padded written with ⟨word, _, _, shape⟩
  have preserved : after.execution.memory.read address 32 = heap.execution.memory.read address 32 := by
    rw [shape]
    exact MemoryOps.snapshotCopy_frame heap cell.address.toNat (wordBytes word) address 32 (Or.inl before)
  cases represented with
  | scalar type address contents range packet =>
      rcases packet with ⟨source, represented, encoded, same, converted, encoding, extent, bytes⟩
      refine .scalar type address contents range ⟨source, represented, encoded, same, converted, encoding, ?_, ?_⟩
      · rw [shape]; exact extent
      · exact preserved.trans bytes
  | pointer type address target contents range extent packet object =>
      have objectAfter := object.frame (Frame.snapshotCopy heap cell.address.toNat floor (wordBytes word)
        (by simpa only [Contract.Interaction.wordBytes_length] using inside) aboveZero)
      rw [← shape] at objectAfter
      refine .pointer type address target contents range ?_ (preserved.trans packet) objectAfter
      rw [shape]; exact extent

def MakesDefaultRep (registry : Registry) (makeDefault : MakeDefault) : Prop :=
  ∀ heap budget type value after remaining,
    MemoryOps.validFrontier heap = true →
    makeDefault heap budget type = .ok (value, after, remaining) →
    ∃ contents, DefaultContents registry (normalizedType type) contents ∧
      ValueRep registry after heap.nextMemory (normalizedType type) contents value

structure CellStep (registry : Registry) (before after : Heap) (lower floor : Nat)
    (type : SType) (address : Nat) : Prop where
  valid : MemoryOps.validFrontier after = true
  frontier : floor ≤ after.nextMemory
  current : ∃ contents, DefaultContents registry type contents ∧ Cell registry after lower floor type address contents
  previous : ∀ oldType oldAddress oldContents, oldAddress+32 ≤ address →
    Cell registry before lower floor oldType oldAddress oldContents →
    Cell registry after lower floor oldType oldAddress oldContents

theorem initializeCell_rep (makeDefault : MakeDefault) (correct : MakesDefaultRep registry makeDefault)
    (safe : MakesDefaultExtension makeDefault) (data : Reference)
    (region : data.region = .memory invocation) (valid : MemoryOps.validFrontier heap = true)
    (minimum : 128 ≤ lower)
    (range : lower ≤ data.address.toNat+entry.2*32 ∧ data.address.toNat+entry.2*32+32 ≤ floor)
    (frontier : floor ≤ heap.nextMemory)
    (written : initializeCell makeDefault data (heap, budget) entry = .ok (after, remaining)) :
    CellStep registry heap after lower floor (atLocation entry.1 .memory false)
      (data.address.toNat+entry.2*32) := by
  unfold initializeCell at written
  cases made : makeDefault heap budget (atLocation entry.1 .memory false) with
  | error failure => simp [made] at written <;> cases written
  | ok result =>
      rcases result with ⟨value, built, rest⟩
      have represented := correct heap budget _ value built rest valid made
      simp only [normalizedType_atLocation] at represented
      rcases represented with ⟨contents, defaults, represented⟩
      have extension := safe heap budget _ value built rest made
      have builtValid := extension.valid valid
      simp only [made, Bind.bind, Except.bind] at written
      cases reserved : reserve rest 32 with
      | error failure => simp [reserved] at written <;> cases written
      | ok available =>
          simp only [reserved] at written
          cases advanced : Access.advance data (entry.2*32) with
          | error failure => simp [advanced] at written <;> cases written
          | ok cell =>
              have position := Copy.advance_memory data (entry.2*32) region advanced
              have padded := Copy.advance_memory_padded region advanced
              simp only [advanced] at written
              cases stored : writeMemoryValue built cell value with
              | error failure => simp [stored] at written <;> cases written
              | ok final =>
                  have finalFrame := Copy.writeMemoryValue_extension cell value position.1 (Nat.zero_le _) stored
                  have current := writeMemoryValue_rep represented cell position.1 padded
                    (by simpa only [position.2] using range) (by omega) frontier stored
                  simp only [stored] at written
                  cases written
                  refine ⟨finalFrame.valid builtValid,
                    Nat.le_trans frontier (Nat.le_trans extension.grows finalFrame.grows), ⟨contents, defaults, ?_⟩, ?_⟩
                  · simpa only [position.2] using current
                  · intro oldType oldAddress oldContents before old
                    have oldBuilt := old.frame (Frame.of_packetFrame (extension.packetFrame valid) (by omega))
                    exact oldBuilt.after_value_store cell value position.1 padded
                      (by simpa only [position.2] using before)
                      (by simpa only [position.2] using range.2) (by omega) stored

theorem initializeCells_rep (makeDefault : MakeDefault) (correct : MakesDefaultRep registry makeDefault)
    (safe : MakesDefaultExtension makeDefault) (data : Reference)
    (region : data.region = .memory invocation) (valid : MemoryOps.validFrontier heap = true)
    (minimum : 128 ≤ lower) (base : lower ≤ data.address.toNat)
    (span : data.address.toNat+types.length*32 ≤ floor) (frontier : floor ≤ heap.nextMemory)
    (written : initializeCells makeDefault heap budget data types = .ok (after, remaining)) :
    ∀ (index : Nat) type, types[index]? = some type →
      ∃ contents, DefaultContents registry (atLocation type .memory false) contents ∧
        Cell registry after lower floor (atLocation type .memory false)
          (data.address.toNat+index*32) contents := by
  unfold initializeCells at written
  cases reserved : reserve budget types.length with
  | error failure => simp [reserved] at written <;> cases written
  | ok available =>
      simp only [reserved, Bind.bind, Except.bind] at written
      let property := fun stop (state : Heap × Nat) =>
        MemoryOps.validFrontier state.1 = true ∧ floor ≤ state.1.nextMemory ∧
          ∀ (index : Nat) type, index < stop → types[index]? = some type →
            ∃ contents, DefaultContents registry (atLocation type .memory false) contents ∧
              Cell registry state.1 lower floor (atLocation type .memory false)
                (data.address.toNat+index*32) contents
      have initial : property 0 (heap, available) := ⟨valid, frontier, by intro index type outside; omega⟩
      have final := Copy.foldlM_zipIdx_invariant (initializeCell makeDefault data) types 0 property initial
        (fun entry state next member prior done => by
          rcases entry with ⟨type, index⟩
          have lookup : types[index]? = some type := List.mk_mem_zipIdx_iff_getElem?.mp member
          have inside := (List.getElem?_eq_some_iff.mp lookup).1
          have step := initializeCell_rep makeDefault correct safe data region prior.1 minimum
            (by constructor <;> dsimp only <;> omega) prior.2.1 done
          refine ⟨step.valid, step.frontier, ?_⟩
          intro earlier oldType before lookupEarlier
          by_cases same : earlier = index
          · subst earlier
            have sameType : oldType = type := Option.some.inj (lookupEarlier.symm.trans lookup)
            subst oldType
            exact step.current
          · rcases prior.2.2 earlier oldType (by omega) lookupEarlier with ⟨contents, defaults, old⟩
            exact ⟨contents, defaults, step.previous _ _ _ (by omega) old⟩)
        written
      intro index type lookup
      exact final.2.2 index type (by simpa using (List.getElem?_eq_some_iff.mp lookup).1) lookup

end Solidity.Aggregates.Defaults.Representation
