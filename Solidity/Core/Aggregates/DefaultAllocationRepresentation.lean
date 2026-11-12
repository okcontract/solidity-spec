/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.DefaultRepresentation
import Solidity.Core.Aggregates.Representation.Construction

namespace Solidity.Aggregates.Defaults.Representation
open Static
open Contract.Interaction (Word wordBytes)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

/-- Assemble all finite cell witnesses without assuming one representative
cell describes an array or struct. Every supplied index is retained. -/
theorem select_values (items : List α) (property : Nat → α → β → Prop)
    (found : ∀ (index : Nat) item, items[index]? = some item → ∃ value, property index item value) :
    ∃ values : List β, values.length = items.length ∧
      ∀ (index : Nat) item value, items[index]? = some item → values[index]? = some value →
        property index item value := by
  induction items generalizing property with
  | nil => exact ⟨[], rfl, by intro index item value impossible; simp at impossible⟩
  | cons item rest ih =>
      rcases found 0 item rfl with ⟨head, headProperty⟩
      have tailFound : ∀ (index : Nat) member, rest[index]? = some member →
          ∃ value, property (index+1) member value := by
        intro index member lookup
        exact found (index+1) member (by simpa using lookup)
      rcases ih (fun index member value => property (index+1) member value) tailFound with
        ⟨tail, length, tailProperty⟩
      refine ⟨head :: tail, by simp [length], ?_⟩
      intro index member value lookup entry
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup entry; subst member; subst value; exact headProperty
      | succ index => exact tailProperty index member value (by simpa using lookup) (by simpa using entry)

theorem allocateArray_rep (makeDefault : MakeDefault) (correct : MakesDefaultRep registry makeDefault)
    (safe : MakesDefaultExtension makeDefault) (valid : MemoryOps.validFrontier heap = true)
    (invocation : after.invocation = heap.invocation)
    (written : allocateArray makeDefault heap budget element count dynamic pointer = .ok (value, after, remaining)) :
    ∃ values, values.length = count ∧
      (∀ (index : Nat) contents, values[index]? = some contents →
        DefaultContents registry (atLocation element .memory false) contents) ∧
      ValueRep registry after heap.nextMemory
        (.array element (if dynamic then none else some count) .memory pointer) (.array element values) value := by
  unfold allocateArray at written
  cases sized : MemoryOps.arraySize count false dynamic with
  | error failure => simp [sized] at written <;> cases written
  | ok bytes =>
      let size := if dynamic then none else some count
      have isNone : size.isNone = dynamic := by cases dynamic <;> rfl
      have bytesEq : bytes = Copy.rootSize size count := by
        exact Copy.arraySize_rootSize (size := size) (by simpa only [isNone] using sized)
      simp only [sized, Bind.bind, Except.bind] at written
      cases allocated : MemoryOps.allocate heap budget bytes with
      | error failure => simp [allocated] at written <;> cases written
      | ok result =>
          rcases result with ⟨reference, fresh, available⟩
          have allocation := Copy.allocate_extension allocated (Nat.le_refl heap.nextMemory)
          have post := Copy.allocate_post allocated
          have rootExtent : fresh.allocated reference.address.toNat (Copy.rootSize size count) = true := by
            rw [post.2.1, allocation.2.2, ← bytesEq]
            exact MemoryOps.initialize_allocated heap bytes
          have rootFloor : reference.address.toNat+Copy.rootSize size count ≤ fresh.nextMemory := by
            rw [post.2.1, allocation.2.2, ← bytesEq]
            exact Nat.add_le_add_left (MemoryOps.roundedSize_covers bytes) heap.nextMemory
          have padded : reference.byteCell = false := by rw [post.1]; rfl
          simp only [allocated] at written
          cases initialized : initializeLength fresh available reference count dynamic with
          | error failure => simp [initialized] at written <;> cases written
          | ok result =>
              rcases result with ⟨populated, rest⟩
              have headerFrame := Copy.initializeLength_extension reference allocation.2.1
                (Nat.le_refl reference.address.toNat) initialized
              have populatedValid := headerFrame.valid (allocation.1.valid valid)
              have floorPopulated := Nat.le_trans rootFloor headerFrame.grows
              simp only [initialized] at written
              cases advanced : arrayDataReference reference dynamic with
              | error failure => simp [advanced] at written <;> cases written
              | ok data =>
                  have dataRegion := arrayDataReference_memory reference allocation.2.1 (Nat.le_refl _) advanced
                  have dataAddress : data.address.toNat = reference.address.toNat+(if dynamic then 32 else 0) := by
                    cases dynamic with
                    | false => cases advanced; simp
                    | true => exact (Copy.advance_memory reference 32 allocation.2.1 advanced).2
                  have dataBeforeFloor : data.address.toNat ≤ reference.address.toNat+Copy.rootSize size count := by
                    rw [dataAddress]; cases dynamic <;> simp [Copy.rootSize, size] <;> omega
                  simp only [advanced] at written
                  cases reserved : reserve rest count with
                  | error failure => simp [reserved] at written <;> cases written
                  | ok allowance =>
                      simp only [reserved] at written
                      cases filled : initializeCells makeDefault populated allowance data (List.replicate count element) with
                      | error failure => simp [filled] at written <;> cases written
                      | ok result =>
                          rcases result with ⟨final, unused⟩
                          have cells := initializeCells_rep (lower := heap.nextMemory) makeDefault correct safe data
                            dataRegion.1 populatedValid (Copy.validFrontier_minimum valid)
                            (by rw [dataAddress, allocation.2.2]; omega)
                            (by rw [dataAddress]; cases dynamic <;> simp [Copy.rootSize, size] <;> omega)
                            floorPopulated filled
                          rcases select_values (List.replicate count element)
                            (fun index type contents => DefaultContents registry (atLocation type .memory false) contents ∧
                              Cell registry final heap.nextMemory (reference.address.toNat+Copy.rootSize size count)
                                (atLocation type .memory false) (data.address.toNat+index*32) contents) cells with
                            ⟨values, length, packets⟩
                          have length : values.length = count := by simpa using length
                          have completed := initializeCells_extension makeDefault safe data dataRegion.1
                            (Nat.le_refl data.address.toNat) (Nat.le_trans dataBeforeFloor floorPopulated) filled
                          simp only [filled] at written
                          have output := Except.ok.inj written
                          have sameHeap := congrArg (fun triple : Value × Heap × Nat => triple.2.1) output
                          have sameValue := congrArg (fun triple : Value × Heap × Nat => triple.1) output
                          dsimp only at sameHeap sameValue
                          have finalInvocation : final.invocation = heap.invocation :=
                            (congrArg Heap.invocation sameHeap).trans invocation
                          rw [← sameHeap, ← sameValue]
                          have packetAt : ∀ (index : Nat) contents, values[index]? = some contents →
                              DefaultContents registry (atLocation element .memory false) contents ∧
                                Cell registry final heap.nextMemory (reference.address.toNat+Copy.rootSize size count)
                                  (atLocation element .memory false) (data.address.toNat+index*32) contents := by
                            intro index contents member
                            have inside : index < count := by have := (List.getElem?_eq_some_iff.mp member).1; omega
                            exact packets index element contents (by simp [inside]) member
                          refine ⟨values, length, fun index contents member => (packetAt index contents member).1,
                            reference.address, ?_, ?_⟩
                          · have canonical : reference = Copy.memoryReference final reference.address := by
                              rw [post.1]
                              simp [MemoryOps.allocatedReference, Copy.memoryReference, finalInvocation]
                            rw [← canonical]
                            cases dynamic <;> rfl
                          · refine .array element size pointer reference.address values (by omega) ?_
                              ?_ ?_ ?_ ?_
                            · have covered := MemoryOps.roundedSize_covers bytes
                              rw [allocation.2.2, length, ← bytesEq]
                              omega
                            · rw [length]
                              exact completed.allocated (headerFrame.allocated rootExtent)
                            · cases dynamic <;> simp [size, length]
                            · intro isDynamic
                              have dynamicTrue : dynamic = true := by
                                cases dynamic <;> simp_all [size]
                              have initializedTrue := initialized
                              rw [dynamicTrue] at initializedTrue
                              have packet := Copy.initializeLength_packet reference allocation.2.1 padded initializedTrue
                              rw [length]
                              exact (completed.reads reference.address.toNat 32
                                (by have minimum := Copy.validFrontier_minimum valid; omega)
                                (by rw [dataAddress, dynamicTrue]; simp)).trans packet
                            · intro index contents member
                              simpa only [Copy.dataStart, dataAddress, isNone, length] using (packetAt index contents member).2

theorem allocateStruct_rep (makeDefault : MakeDefault) (correct : MakesDefaultRep registry makeDefault)
    (safe : MakesDefaultExtension makeDefault) (valid : MemoryOps.validFrontier heap = true)
    (invocation : after.invocation = heap.invocation)
    (written : allocateStruct makeDefault registry heap budget identity pointer = .ok (value, after, remaining)) :
    ∃ contents, DefaultContents registry (.structType identity .memory pointer) contents ∧
      ValueRep registry after heap.nextMemory (.structType identity .memory pointer) contents value := by
  unfold allocateStruct at written
  cases definition : registry.structFields identity with
  | none => simp [definition] at written
  | some fields =>
      simp only [definition, Bind.bind, Except.bind] at written
      cases sized : MemoryOps.arraySize fields.length false false with
      | error failure => simp [sized] at written
      | ok bytes =>
          have bytesEq : bytes = 32*fields.length := by
            simpa [Copy.rootSize] using (Copy.arraySize_rootSize (size := some 0) sized)
          simp only [sized] at written
          cases allocated : MemoryOps.allocate heap budget bytes with
          | error failure => simp [allocated] at written
          | ok result =>
              rcases result with ⟨reference, fresh, available⟩
              have allocation := Copy.allocate_extension allocated (Nat.le_refl heap.nextMemory)
              have post := Copy.allocate_post allocated
              have rootExtent : fresh.allocated reference.address.toNat (32*fields.length) = true := by
                rw [post.2.1, allocation.2.2, ← bytesEq]
                exact MemoryOps.initialize_allocated heap bytes
              have rootFloor : reference.address.toNat+32*fields.length ≤ fresh.nextMemory := by
                rw [post.2.1, allocation.2.2, ← bytesEq]
                exact Nat.add_le_add_left (MemoryOps.roundedSize_covers bytes) heap.nextMemory
              simp only [allocated] at written
              cases filled : initializeCells makeDefault fresh available reference (fields.map Prod.snd) with
              | error failure => simp [filled] at written
              | ok result =>
                  rcases result with ⟨final, unused⟩
                  have cells := initializeCells_rep (lower := heap.nextMemory) makeDefault correct safe
                    reference allocation.2.1 (allocation.1.valid valid) (Copy.validFrontier_minimum valid)
                    (by omega) (by simp only [List.length_map]; omega) rootFloor filled
                  have found : ∀ (index : Nat) field, fields[index]? = some field →
                      ∃ contents, DefaultContents registry (atLocation field.2 .memory false) contents ∧
                        Cell registry final heap.nextMemory (reference.address.toNat+32*fields.length)
                          (atLocation field.2 .memory false) (reference.address.toNat+index*32) contents := by
                    intro index field member
                    exact cells index field.2 (by simp [List.getElem?_map, member])
                  rcases select_values fields
                    (fun index field contents => DefaultContents registry (atLocation field.2 .memory false) contents ∧
                      Cell registry final heap.nextMemory (reference.address.toNat+32*fields.length)
                        (atLocation field.2 .memory false) (reference.address.toNat+index*32) contents) found with
                    ⟨values, length, packets⟩
                  have completed := initializeCells_extension makeDefault safe reference allocation.2.1
                    (Nat.le_refl reference.address.toNat) (by have grown := allocation.1.grows; omega) filled
                  simp only [filled] at written
                  have output := Except.ok.inj written
                  have sameHeap := congrArg (fun triple : Value × Heap × Nat => triple.2.1) output
                  have sameValue := congrArg (fun triple : Value × Heap × Nat => triple.1) output
                  dsimp only at sameHeap sameValue
                  have finalInvocation : final.invocation = heap.invocation :=
                    (congrArg Heap.invocation sameHeap).trans invocation
                  rw [← sameHeap, ← sameValue]
                  refine ⟨.structure identity values, ?_, reference.address, ?_, ?_⟩
                  · exact .structure identity pointer fields values definition length
                      (fun index field contents member entry => (packets index field contents member entry).1)
                  · have canonical : reference = Copy.memoryReference final reference.address := by
                      rw [post.1]
                      simp [MemoryOps.allocatedReference, Copy.memoryReference, finalInvocation]
                    rw [← canonical]
                    rfl
                  · refine .structure identity pointer reference.address fields values
                      (by omega) ?_ (completed.allocated rootExtent) definition length.symm ?_
                    · have covered := MemoryOps.roundedSize_covers bytes
                      rw [allocation.2.2, ← bytesEq]
                      omega
                    · intro index field contents member entry
                      exact (packets index field contents member entry).2

end Solidity.Aggregates.Defaults.Representation
