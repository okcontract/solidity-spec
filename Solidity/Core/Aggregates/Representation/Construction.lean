/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Representation.Cells
import Solidity.Core.Aggregates.Copy.Frames

/-! Direct physical correctness of array, struct and byte construction and the
fuel-indexed materializer. Primitive packet and prefix laws are imported below
these constructors rather than reconstructed here. -/
namespace Solidity.Aggregates.Copy
open Core Static
open Contract.Interaction (Word Memory wordBytes bytesWord)

theorem initializeArrayHeader_packet (reference : Reference)
    (region : reference.region = .memory invocation) (padded : reference.byteCell = false)
    (written : initializeArrayHeader heap budget reference count dynamic = .ok (data, after, remaining)) :
    data.address.toNat = reference.address.toNat+(if dynamic then 32 else 0) ∧
    (dynamic = true → after.execution.memory.read reference.address.toNat 32 =
      wordBytes (BitVec.ofNat 256 count)) := by
  cases dynamic with
  | false => cases written; exact ⟨by simp, by intro impossible; cases impossible⟩
  | true =>
      unfold initializeArrayHeader at written
      cases reserved : reserve budget 32 with
      | error failure => simp [reserved] at written <;> cases written
      | ok available =>
          simp only [reserved, Bind.bind, Except.bind] at written
          cases stored : Defaults.writeMemoryValue heap reference ⟨.uint 31, BitVec.ofNat 256 count⟩ with
          | error failure => simp [stored] at written <;> cases written
          | ok filled =>
              rcases writeMemoryValue_word reference _ region padded stored with ⟨word, encoded, _, shape⟩
              have wordEq : word = BitVec.ofNat 256 count := by
                simpa [WordEncoding, Value.reference, encodeMemory] using encoded.symm
              rw [wordEq] at shape
              simp only [stored] at written
              cases advanced : Access.advance reference 32 with
              | error failure => simp [advanced] at written <;> cases written
              | ok result =>
                  have position := advance_memory reference 32 region advanced
                  simp only [advanced] at written
                  cases written
                  refine ⟨position.2, ?_⟩
                  intro _
                  rw [shape]
                  simpa only [Contract.Interaction.wordBytes_length] using
                    MemoryOps.snapshotCopy_contents heap reference.address.toNat (wordBytes (BitVec.ofNat 256 count))

theorem arraySize_rootSize (sized : MemoryOps.arraySize count false size.isNone = .ok bytes) :
    bytes = rootSize size count := by
  unfold MemoryOps.arraySize at sized
  split at sized
  · cases sized
  · cases size <;> simpa [rootSize, Nat.mul_comm, Nat.add_comm] using (Except.ok.inj sized).symm

theorem validFrontier_minimum (valid : MemoryOps.validFrontier heap = true) : 128 ≤ heap.nextMemory := by
  simp only [MemoryOps.validFrontier, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1.1

theorem memoryArray_rep (materialize : Materialize) (correct : MakesValueRep registry materialize)
    (safe : MakesMemoryExtension materialize) (frames : MakesFrame materialize)
    (valid : MemoryOps.validFrontier heap = true)
    (written : memoryArray materialize heap budget element size pointer values = .ok (value, after, remaining)) :
    ValueRep registry after heap.nextMemory (.array element size .memory pointer) (.array sourceElement values) value := by
  have invocation := (memoryArray_frame materialize frames heap after budget remaining element size pointer values value written).2
  unfold memoryArray at written
  split at written
  · cases written
  · rename_i compatible
    have length : size.all (· = values.length) := by
      cases size with
      | none => rfl
      | some count => simpa using compatible
    cases sized : MemoryOps.arraySize values.length false size.isNone with
    | error failure => simp [sized] at written <;> cases written
    | ok bytes =>
        have bytesEq := arraySize_rootSize sized
        simp only [sized, Bind.bind, Except.bind] at written
        cases allocated : MemoryOps.allocate heap budget bytes with
        | error failure => simp [allocated] at written <;> cases written
        | ok result =>
            rcases result with ⟨reference, fresh, available⟩
            have allocation := allocate_extension allocated (Nat.le_refl heap.nextMemory)
            have post := allocate_post allocated
            have rootExtent : fresh.allocated reference.address.toNat (rootSize size values.length) = true := by
              rw [post.2.1, allocation.2.2, ← bytesEq]
              exact MemoryOps.initialize_allocated heap bytes
            have rootFloor : reference.address.toNat+rootSize size values.length ≤ fresh.nextMemory := by
              rw [post.2.1, allocation.2.2, ← bytesEq]
              exact Nat.add_le_add_left (MemoryOps.roundedSize_covers bytes) heap.nextMemory
            have padded : reference.byteCell = false := by rw [post.1]; rfl
            simp only [allocated] at written
            cases initialized : initializeArrayHeader fresh available reference values.length size.isNone with
            | error failure => simp [initialized] at written <;> cases written
            | ok result =>
                rcases result with ⟨data, populated, rest⟩
                have headerFrame := initializeArrayHeader_extension reference allocation.2.1
                  (Nat.le_refl reference.address.toNat) initialized
                have header := initializeArrayHeader_packet reference allocation.2.1 padded initialized
                have populatedValid := headerFrame.1.valid (allocation.1.valid valid)
                have floorPopulated := Nat.le_trans rootFloor headerFrame.1.grows
                have dataBeforeFloor : data.address.toNat ≤ reference.address.toNat+rootSize size values.length := by
                  rw [header.1]; cases size <;> simp [rootSize] <;> omega
                simp only [initialized] at written
                cases reserved : reserve rest values.length with
                | error failure => simp [reserved] at written <;> cases written
                | ok allowance =>
                    simp only [reserved] at written
                    cases filled : values.zipIdx.foldlM (memoryCell materialize data element) (populated, allowance) with
                    | error failure => simp [filled] at written <;> cases written
                    | ok result =>
                        rcases result with ⟨final, unused⟩
                        have cells := fillMemory_rep (lower := heap.nextMemory) materialize correct safe values (fun _ => element) id
                          data headerFrame.2.1 populatedValid
                          (by have minimum := validFrontier_minimum valid; omega)
                          (by rw [header.1, allocation.2.2]; omega)
                          (by rw [header.1]; cases size <;> simp [rootSize] <;> omega)
                          floorPopulated filled
                        have completed := fold_extension (memoryCell materialize data element)
                          (fun heap budget entry after remaining frontier done =>
                            memoryCell_extension materialize safe data element headerFrame.2.1
                              (Nat.le_refl data.address.toNat) frontier done)
                          values.zipIdx (Nat.le_trans dataBeforeFloor floorPopulated) filled
                        simp only [filled] at written
                        have output := Except.ok.inj written
                        have sameHeap := congrArg (fun triple : Value × Heap × Nat => triple.2.1) output
                        have sameValue := congrArg (fun triple : Value × Heap × Nat => triple.1) output
                        dsimp only at sameHeap sameValue
                        have finalInvocation : final.invocation = heap.invocation :=
                          (congrArg Heap.invocation sameHeap).trans invocation
                        rw [← sameHeap, ← sameValue]
                        refine ⟨reference.address, ?_, ?_⟩
                        · have canonical : reference = memoryReference final reference.address := by
                            rw [post.1]
                            simp [MemoryOps.allocatedReference, memoryReference, finalInvocation]
                          rw [← canonical]
                          rfl
                        · refine .array element size pointer reference.address values
                            (by omega) ?_ (completed.allocated (headerFrame.1.allocated rootExtent)) length ?_ ?_
                          · have covered := MemoryOps.roundedSize_covers bytes
                            rw [allocation.2.2, ← bytesEq]
                            omega
                          · intro dynamic
                            exact (completed.reads reference.address.toNat 32
                              (by have minimum := validFrontier_minimum valid; omega)
                              (by rw [header.1, dynamic]; simp)).trans (header.2 dynamic)
                          · intro index contents member
                            simpa only [dataStart, header.1] using cells index contents member

theorem memoryStruct_rep (materialize : Materialize) (correct : MakesValueRep registry materialize)
    (safe : MakesMemoryExtension materialize) (frames : MakesFrame materialize)
    (valid : MemoryOps.validFrontier heap = true)
    (written : memoryStruct materialize registry heap budget identity pointer values = .ok (value, after, remaining)) :
    ValueRep registry after heap.nextMemory (.structType identity .memory pointer) (.structure identity values) value := by
  have invocation := (memoryStruct_frame materialize frames registry heap after budget remaining identity pointer values value written).2
  unfold memoryStruct at written
  cases definition : registry.structFields identity with
  | none => simp [definition] at written <;> cases written
  | some fields =>
      simp only [definition, Bind.bind, Except.bind] at written
      split at written
      · cases written
      · rename_i compatible
        have length : fields.length = values.length := by simpa using compatible
        cases sized : MemoryOps.arraySize fields.length false false with
        | error failure => simp [sized] at written <;> cases written
        | ok bytes =>
            have bytesEq : bytes = 32*fields.length := by
              simpa [rootSize] using (arraySize_rootSize (size := some 0) sized)
            simp only [sized] at written
            cases allocated : MemoryOps.allocate heap budget bytes with
            | error failure => simp [allocated] at written <;> cases written
            | ok result =>
                rcases result with ⟨reference, fresh, available⟩
                have allocation := allocate_extension allocated (Nat.le_refl heap.nextMemory)
                have post := allocate_post allocated
                have rootExtent : fresh.allocated reference.address.toNat (32*fields.length) = true := by
                  rw [post.2.1, allocation.2.2, ← bytesEq]
                  exact MemoryOps.initialize_allocated heap bytes
                have rootFloor : reference.address.toNat+32*fields.length ≤ fresh.nextMemory := by
                  rw [post.2.1, allocation.2.2, ← bytesEq]
                  exact Nat.add_le_add_left (MemoryOps.roundedSize_covers bytes) heap.nextMemory
                simp only [allocated] at written
                cases reserved : reserve available fields.length with
                | error failure => simp [reserved] at written <;> cases written
                | ok allowance =>
                    simp only [reserved] at written
                    cases filled : ((fields.map Prod.snd).zip values).zipIdx.foldlM
                        (memoryField materialize reference) (fresh, allowance) with
                    | error failure => simp [filled] at written <;> cases written
                    | ok result =>
                        rcases result with ⟨final, unused⟩
                        have cells := fillMemory_rep (lower := heap.nextMemory) materialize correct safe
                          ((fields.map Prod.snd).zip values) Prod.fst Prod.snd reference allocation.2.1
                          (allocation.1.valid valid) (by have minimum := validFrontier_minimum valid; omega)
                          (by omega) (by simp only [List.length_zip, List.length_map, length, Nat.min_self]; omega)
                          rootFloor filled
                        have completed := fold_extension (memoryField materialize reference)
                          (fun heap budget entry after remaining frontier done =>
                            memoryCell_extension materialize safe reference entry.1.1 allocation.2.1
                              (Nat.le_refl reference.address.toNat) frontier done)
                          ((fields.map Prod.snd).zip values).zipIdx
                          (by have grown := allocation.1.grows; omega) filled
                        simp only [filled] at written
                        have output := Except.ok.inj written
                        have sameHeap := congrArg (fun triple : Value × Heap × Nat => triple.2.1) output
                        have sameValue := congrArg (fun triple : Value × Heap × Nat => triple.1) output
                        dsimp only at sameHeap sameValue
                        have finalInvocation : final.invocation = heap.invocation :=
                          (congrArg Heap.invocation sameHeap).trans invocation
                        rw [← sameHeap, ← sameValue]
                        refine ⟨reference.address, ?_, ?_⟩
                        · have canonical : reference = memoryReference final reference.address := by
                            rw [post.1]
                            simp [MemoryOps.allocatedReference, memoryReference, finalInvocation]
                          rw [← canonical]
                          rfl
                        · refine .structure identity pointer reference.address fields values
                            (by omega) ?_ (completed.allocated rootExtent) definition length ?_
                          · have covered := MemoryOps.roundedSize_covers bytes
                            rw [allocation.2.2, ← bytesEq]
                            omega
                          · intro index field contents fieldMember valueMember
                            have member : ((fields.map Prod.snd).zip values)[index]? = some (field.2, contents) := by
                              apply List.getElem?_zip_eq_some.mpr
                              exact ⟨by simp [List.getElem?_map, fieldMember], valueMember⟩
                            exact cells index (field.2, contents) member

theorem initializeLength_packet (reference : Reference)
    (region : reference.region = .memory invocation) (padded : reference.byteCell = false)
    (written : Defaults.initializeLength heap budget reference count true = .ok (after, remaining)) :
    after.execution.memory.read reference.address.toNat 32 = wordBytes (BitVec.ofNat 256 count) := by
  unfold Defaults.initializeLength at written
  cases reserved : reserve budget 32 with
  | error failure => simp [reserved] at written <;> cases written
  | ok available =>
      simp only [reserved, Bind.bind, Except.bind] at written
      cases stored : Defaults.writeMemoryValue heap reference ⟨.uint 31, BitVec.ofNat 256 count⟩ with
      | error failure => simp [stored] at written <;> cases written
      | ok filled =>
          rcases writeMemoryValue_word reference _ region padded stored with ⟨word, encoded, _, shape⟩
          have wordEq : word = BitVec.ofNat 256 count := by
            simpa [WordEncoding, Value.reference, encodeMemory] using encoded.symm
          rw [wordEq] at shape
          simp only [stored] at written
          cases written
          rw [shape]
          simpa only [Contract.Interaction.wordBytes_length] using
            MemoryOps.snapshotCopy_contents heap reference.address.toNat (wordBytes (BitVec.ofNat 256 count))

theorem newBytes_object
    (created : Defaults.newBytes budget heap count string = .ok (value, after, remaining)) :
    ∃ reference,
      Defaults.asPlace value = .ok ⟨byteType string true, reference⟩ ∧
      reference = MemoryOps.allocatedReference heap ∧ reference.address.toNat = heap.nextMemory ∧
      reference.address.toNat+32+count ≤ MemoryOps.maximumMemory ∧
      after.allocated reference.address.toNat (32+count) = true ∧
      after.execution.memory.read reference.address.toNat 32 = wordBytes (BitVec.ofNat 256 count) := by
  unfold Defaults.newBytes at created
  cases sized : MemoryOps.arraySize count true true with
  | error failure => simp [sized] at created <;> cases created
  | ok bytes =>
      have bytesEq : bytes = MemoryOps.roundedSize count+32 := by
        unfold MemoryOps.arraySize at sized
        split at sized
        · cases sized
        · exact (Except.ok.inj sized).symm
      simp only [sized, Bind.bind, Except.bind] at created
      cases allocated : MemoryOps.allocate heap budget bytes with
      | error failure => simp [allocated] at created <;> cases created
      | ok result =>
          rcases result with ⟨reference, fresh, available⟩
          have allocation := allocate_extension allocated (Nat.le_refl heap.nextMemory)
          have post := allocate_post allocated
          have covered := MemoryOps.roundedSize_covers count
          have objectExtent : fresh.allocated reference.address.toNat (32+count) = true := by
            rw [post.2.1, allocation.2.2]
            exact allocated_subrange _ _ _ _ _ (MemoryOps.initialize_allocated heap bytes) (Nat.le_refl _) (by omega)
          simp only [allocated] at created
          cases initialized : Defaults.initializeLength fresh available reference count true with
          | error failure => simp [initialized] at created <;> cases created
          | ok result =>
              rcases result with ⟨filled, rest⟩
              have extension := initializeLength_extension reference allocation.2.1 (Nat.le_refl reference.address.toNat) initialized
              have packet := initializeLength_packet reference allocation.2.1 (by rw [post.1]; rfl) initialized
              simp only [initialized] at created
              have output := Except.ok.inj created
              have sameHeap := congrArg (fun triple : Value × Heap × Nat => triple.2.1) output
              have sameValue := congrArg (fun triple : Value × Heap × Nat => triple.1) output
              dsimp only at sameHeap sameValue
              rw [← sameHeap, ← sameValue]
              refine ⟨reference, ?_, post.1, allocation.2.2, ?_, extension.allocated objectExtent, packet⟩
              · cases string <;> rfl
              · have allocationCovered := MemoryOps.roundedSize_covers bytes
                rw [allocation.2.2]
                omega

theorem memoryBytes_rep (written : memoryBytes heap budget pointer string bytes = .ok (value, after, remaining)) :
    ValueRep registry after heap.nextMemory (byteType string pointer) (.bytes string bytes) value := by
  have invocation := (memoryBytes_frame heap after budget remaining pointer string bytes value written).2
  unfold memoryBytes at written
  cases created : Defaults.newBytes budget heap bytes.length string with
  | error failure => simp [created] at written <;> cases written
  | ok result =>
      rcases result with ⟨source, fresh, available⟩
      rcases newBytes_object created with ⟨reference, located, canonical, address, bounded, extent, header⟩
      simp only [created, Bind.bind, Except.bind, located] at written
      have region : reference.region = .memory heap.invocation := by rw [canonical]; rfl
      cases advanced : Access.advance reference 32 with
      | error failure => simp [advanced] at written <;> cases written
      | ok data =>
          have position := advance_memory reference 32 region advanced
          simp only [advanced] at written
          cases copied : writePacket fresh available data bytes with
          | error failure => simp [copied] at written <;> cases written
          | ok result =>
              rcases result with ⟨final, rest⟩
              have extension := writePacket_extension (Nat.zero_le data.address.toNat) copied
              have payload := writePacket_contents copied
              have oldHeader := writePacket_frame copied (offset := reference.address.toNat) (count := 32)
                (Or.inl (by omega))
              simp only [copied] at written
              cases tagged : retag (if string then .string .memory pointer else .bytes .memory pointer) reference with
              | error failure => simp [tagged] at written <;> cases written
              | ok result =>
                  simp only [tagged] at written
                  have output := Except.ok.inj written
                  have sameHeap := congrArg (fun triple : Value × Heap × Nat => triple.2.1) output
                  have sameValue := congrArg (fun triple : Value × Heap × Nat => triple.1) output
                  dsimp only at sameHeap sameValue
                  have finalInvocation : final.invocation = heap.invocation :=
                    (congrArg Heap.invocation sameHeap).trans invocation
                  rw [← sameHeap, ← sameValue]
                  refine ⟨reference.address, ?_, ?_⟩
                  · have referenceEq : reference = memoryReference final reference.address := by
                      rw [canonical]
                      simp [MemoryOps.allocatedReference, memoryReference, finalInvocation]
                    rw [← referenceEq]
                    exact tagged
                  · exact .bytes string pointer reference.address bytes (by omega) bounded
                      (extension.allocated extent) (oldHeader.trans header) (by simpa only [position.2] using payload)

theorem memoryScalar_rep
    (written : memoryScalar heap budget type source = .ok (value, after, remaining)) :
    ValueRep registry after heap.nextMemory type (.scalar source) value := by
  unfold memoryScalar at written
  cases converted : convertScalar type source with
  | error failure => simp [converted] at written <;> cases written
  | ok result =>
      simp only [converted, Bind.bind, Except.bind] at written
      have sameValue := congrArg (fun triple : Value × Heap × Nat => triple.1) (Except.ok.inj written)
      dsimp only at sameValue
      change convertScalar type source = .ok value
      rw [← sameValue]
      exact converted

theorem buildMemory_rep (registry : Registry) (fuel : Nat) : MakesValueRep registry (buildMemory registry fuel) := by
  induction fuel with
  | zero => intro budget heap type contents value after remaining valid written; cases written
  | succ fuel ih =>
      intro budget heap type contents value after remaining valid written
      have safe := buildMemory_extension registry fuel
      have frames := buildMemory_frame registry fuel
      cases contents with
      | scalar source =>
          have equation : buildMemory registry (fuel+1) budget heap type (.scalar source) =
              memoryScalar heap budget type source := by
            cases type <;> try rfl
            all_goals rename_i location pointer; cases location <;> rfl
          rw [equation] at written
          exact memoryScalar_rep written
      | array sourceElement values =>
          cases type <;> simp only [buildMemory] at written <;> try cases written
          case array element size location pointer =>
            cases location <;> simp only at written <;> try cases written
            exact memoryArray_rep _ ih safe frames valid written
      | «structure» sourceIdentity values =>
          cases type <;> simp only [buildMemory] at written <;> try cases written
          case structType identity location pointer =>
            cases location <;> simp only at written <;> try cases written
            split at written
            · cases written
            · rename_i sameIdentity
              have same : identity = sourceIdentity := by simpa using sameIdentity
              subst sourceIdentity
              exact memoryStruct_rep _ ih safe frames valid written
      | bytes string bytes =>
          cases type <;> simp only [buildMemory] at written <;> try cases written
          case bytes location pointer =>
            cases location <;> cases string <;> simp only at written <;> try cases written
            exact memoryBytes_rep written
          case string location pointer =>
            cases location <;> cases string <;> simp only at written <;> try cases written
            exact memoryBytes_rep written

/-- Successful fresh construction represents the entire finite input tree in
the actual memory packets. The induction proves installed scalar encodings,
nested pointer cells, length headers and byte payloads, not runner equality. -/
theorem materializeMemory_rep (valid : MemoryOps.validFrontier heap = true)
    (written : materializeMemory registry fuel budget heap type contents = .ok (value, after, remaining)) :
    ValueRep registry after heap.nextMemory type contents value := by
  unfold materializeMemory at written
  cases checked : eligibleAt registry fuel (.memory heap.invocation) type with
  | error failure => simp [checked] at written <;> cases written
  | ok _ =>
      simp only [checked, Bind.bind, Except.bind] at written
      exact buildMemory_rep registry fuel budget heap type contents value after remaining valid written

theorem materializeMemory_rep_and_frame (valid : MemoryOps.validFrontier heap = true)
    (written : materializeMemory registry fuel budget heap type contents = .ok (value, after, remaining)) :
    ValueRep registry after heap.nextMemory type contents value ∧
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation ∧
    MemoryExtension heap.nextMemory heap after :=
  ⟨materializeMemory_rep valid written, (materializeMemory_frame written).1,
    (materializeMemory_frame written).2, materializeMemory_extension written⟩

theorem bind_memoryCopy_rep (valid : MemoryOps.validFrontier heap = true)
    (planned : planTransfer registry fuel true source.type type = .ok .memoryCopy)
    (frozen : snapshotValue registry fuel budget heap source = .ok (contents, allowance))
    (written : bind registry fuel budget heap type source = .ok (value, after, remaining)) :
    ValueRep registry after heap.nextMemory type contents value ∧
    MemoryExtension heap.nextMemory heap after := by
  rw [bind_memoryCopy planned] at written
  simp only [frozen, Bind.bind, Except.bind] at written
  exact ⟨materializeMemory_rep valid written, materializeMemory_extension written⟩


end Solidity.Aggregates.Copy
