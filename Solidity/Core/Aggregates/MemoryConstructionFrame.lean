/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy.Laws

/-! Fresh construction retains every previous allocation registration and
preserves slices from the zero slot upward below its entry frontier.
The cutoff form composes across recursive child construction and cell stores. -/
namespace Solidity.Aggregates.Copy
open Static
open Contract.Interaction (Word Memory wordBytes)

private theorem frame_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem frame_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] frame_map_error frame_map_ok
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

structure MemoryExtension (cutoff : Nat) (before after : Heap) : Prop where
  valid : MemoryOps.validFrontier before = true → MemoryOps.validFrontier after = true
  grows : before.nextMemory ≤ after.nextMemory
  allocations : ∀ allocation ∈ before.allocations, allocation ∈ after.allocations
  reads : ∀ offset count, 96 ≤ offset → offset + count ≤ cutoff →
    after.execution.memory.read offset count = before.execution.memory.read offset count

theorem MemoryExtension.refl (cutoff : Nat) (heap : Heap) : MemoryExtension cutoff heap heap :=
  ⟨id, Nat.le_refl _, fun _ h => h, fun _ _ _ _ => rfl⟩

theorem MemoryExtension.trans (first : MemoryExtension cutoff before middle)
    (second : MemoryExtension cutoff middle after) : MemoryExtension cutoff before after :=
  ⟨second.valid ∘ first.valid, Nat.le_trans first.grows second.grows,
    fun allocation old => second.allocations allocation (first.allocations allocation old),
    fun offset count start stop => (second.reads offset count start stop).trans
      (first.reads offset count start stop)⟩

theorem MemoryExtension.weaken (extension : MemoryExtension upper before after)
    (bound : cutoff ≤ upper) : MemoryExtension cutoff before after :=
  {extension with reads := fun offset count start stop =>
    extension.reads offset count start (Nat.le_trans stop bound)}

theorem writeScalar_extension (place : Place) (value : place.type.Value)
    (region : place.reference.region = .memory invocation)
    (above : cutoff ≤ place.reference.address.toNat)
    (written : writeScalar heap place value = .ok after) :
    MemoryExtension cutoff heap after := by
  unfold writeScalar at written
  cases sized : storageBytes place.type with
  | none => simp [sized] at written
  | some bytes =>
      simp only [sized, region, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
      split at written
      · cases written
      · split at written
        · cases written
        · cases extent : checkExtent heap place.reference (scalarCellBytes place.reference) with
          | error failure => simp [extent] at written
          | ok _ =>
              simp only [extent] at written
              cases byteFlag : place.reference.byteCell <;>
                simp only [byteFlag, Bool.false_eq_true, ↓reduceIte] at written
              all_goals
                split at written
                · cases written
                · cases written
                  refine ⟨fun valid => valid, Nat.le_refl _, fun _ h => h, ?_⟩
                  intro offset count _ stop
                  exact Memory.read_write_disjoint _ offset count _ _ (Or.inl (by omega))

theorem writeMemoryValue_extension (cell : Reference) (value : Value)
    (region : cell.region = .memory invocation) (above : cutoff ≤ cell.address.toNat)
    (written : Defaults.writeMemoryValue heap cell value = .ok after) :
    MemoryExtension cutoff heap after := by
  unfold Defaults.writeMemoryValue at written
  simp only [region] at written
  split at written
  · cases written
  · split at written
    · cases written
    · cases reference : value.reference with
      | none =>
          simp only [reference] at written
          exact writeScalar_extension ⟨value.type, cell⟩ value.value region above written
      | some pointer =>
          simp only [reference] at written
          split at written
          · cases written
          · split at written
            · cases written
            · split at written
              · cases written
              · cases pointerExtent : checkExtent heap pointer 0 with
                | error failure => simp [pointerExtent] at written
                | ok _ =>
                    simp only [pointerExtent] at written
                    cases cellExtent : checkExtent heap cell 32 with
                    | error failure => simp [cellExtent] at written
                    | ok _ =>
                        simp only [cellExtent] at written
                        cases written
                        refine ⟨fun valid => valid, Nat.le_refl _, fun _ h => h, ?_⟩
                        intro offset count _ stop
                        exact Memory.read_write_disjoint _ offset count _ _ (Or.inl (by omega))

theorem initializeBytes_extension (heap : Heap) (size : Nat)
    (above : cutoff ≤ heap.nextMemory) :
    MemoryExtension cutoff heap (MemoryOps.initializeBytes heap size) := by
  refine ⟨fun valid => MemoryOps.initialize_preserves_frontier heap size valid,
    by simp [MemoryOps.initializeBytes], ?_, ?_⟩
  · intro allocation member; exact List.mem_cons_of_mem _ member
  · intro offset count start stop
    exact MemoryOps.initialize_frame heap size offset count (Or.inl (by omega)) (Or.inr start)

theorem allocate_extension
    (allocated : MemoryOps.allocate heap budget size = .ok (reference, after, remaining))
    (above : cutoff ≤ heap.nextMemory) :
    MemoryExtension cutoff heap after ∧ reference.region = .memory heap.invocation ∧
    reference.address.toNat = heap.nextMemory := by
  by_cases valid : MemoryOps.validAllocationContext heap = true
  · by_cases fits : heap.nextMemory + MemoryOps.roundedSize size ≤ MemoryOps.maximumMemory
    · by_cases enough : MemoryOps.roundedSize size+32 ≤ budget
      · rw [MemoryOps.allocate_success heap budget size valid fits enough] at allocated
        cases allocated
        exact ⟨initializeBytes_extension heap size above, rfl,
          MemoryOps.allocatedReference_address heap size fits⟩
      · rw [MemoryOps.allocate_host_exhausted heap budget size valid fits (by omega)] at allocated
        cases allocated
    · rw [MemoryOps.allocate_resource_failure heap budget size valid (by omega)] at allocated
      cases allocated
  · have invalid : MemoryOps.validAllocationContext heap = false := Bool.eq_false_iff.mpr valid
    simp only [MemoryOps.allocate, invalid, Bool.not_false, ↓reduceIte] at allocated
    cases allocated

theorem allocate_post
    (allocated : MemoryOps.allocate heap budget size = .ok (reference, after, remaining)) :
    reference = MemoryOps.allocatedReference heap ∧
    after = MemoryOps.initializeBytes heap size ∧
    heap.nextMemory + MemoryOps.roundedSize size ≤ MemoryOps.maximumMemory := by
  by_cases valid : MemoryOps.validAllocationContext heap = true
  · by_cases fits : heap.nextMemory + MemoryOps.roundedSize size ≤ MemoryOps.maximumMemory
    · by_cases enough : MemoryOps.roundedSize size+32 ≤ budget
      · rw [MemoryOps.allocate_success heap budget size valid fits enough] at allocated
        cases allocated
        exact ⟨rfl, rfl, fits⟩
      · rw [MemoryOps.allocate_host_exhausted heap budget size valid fits (by omega)] at allocated
        cases allocated
    · rw [MemoryOps.allocate_resource_failure heap budget size valid (by omega)] at allocated
      cases allocated
  · have invalid : MemoryOps.validAllocationContext heap = false := Bool.eq_false_iff.mpr valid
    simp only [MemoryOps.allocate, invalid, Bool.not_false, ↓reduceIte] at allocated
    cases allocated

theorem advance_memory (reference : Reference) (bytes : Nat)
    (region : reference.region = .memory invocation)
    (advanced : Access.advance reference bytes = .ok target) :
    target.region = .memory invocation ∧ target.address.toNat = reference.address.toNat + bytes := by
  unfold Access.advance at advanced
  simp only [region] at advanced
  split at advanced
  · rename_i bound
    cases advanced
    exact ⟨region, by simp [rebase, Nat.mod_eq_of_lt bound]⟩
  · cases advanced

def MakesMemoryExtension (materialize : Materialize) : Prop :=
  ∀ budget heap type contents value after remaining,
    materialize budget heap type contents = .ok (value, after, remaining) →
    MemoryExtension heap.nextMemory heap after

theorem memoryCell_extension (materialize : Materialize)
    (safe : MakesMemoryExtension materialize) (data : Reference) (type : SType)
    (region : data.region = .memory invocation) (above : cutoff ≤ data.address.toNat)
    (frontier : cutoff ≤ heap.nextMemory)
    (written : memoryCell materialize data type (heap, budget) entry = .ok (after, remaining)) :
    MemoryExtension cutoff heap after := by
  unfold memoryCell at written
  cases made : materialize budget heap (atLocation type .memory false) entry.1 with
  | error failure => simp [made] at written
  | ok result =>
      rcases result with ⟨value, next, rest⟩
      have first := (safe budget heap _ entry.1 value next rest made).weaken frontier
      simp only [made, Bind.bind, Except.bind] at written
      cases reserved : reserve rest 32 with
      | error failure => simp [reserved] at written
      | ok available =>
          simp only [reserved] at written
          cases advanced : Access.advance data (entry.2*32) with
          | error failure => simp [advanced] at written
          | ok cell =>
              have position := advance_memory data (entry.2*32) region advanced
              simp only [advanced] at written
              cases stored : Defaults.writeMemoryValue next cell value with
              | error failure => simp [stored] at written
              | ok final =>
                  simp only [stored] at written
                  have last := writeMemoryValue_extension cell value position.1
                    (by omega : cutoff ≤ cell.address.toNat) stored
                  cases written
                  exact first.trans last

theorem fold_extension (step : (Heap × Nat) → α → Result (Heap × Nat))
    (safe : ∀ heap budget item after remaining, cutoff ≤ heap.nextMemory →
      step (heap, budget) item = .ok (after, remaining) → MemoryExtension cutoff heap after)
    (items : List α) (frontier : cutoff ≤ heap.nextMemory)
    (written : items.foldlM step (heap, budget) = .ok (after, remaining)) :
    MemoryExtension cutoff heap after := by
  induction items generalizing heap budget with
  | nil => cases written; exact .refl cutoff after
  | cons item rest ih =>
      rw [List.foldlM_cons] at written
      cases first : step (heap, budget) item with
      | error failure => simp [first] at written
      | ok result =>
          rcases result with ⟨next, available⟩
          simp only [first, Bind.bind, Except.bind] at written
          have extension := safe heap budget item next available frontier first
          exact extension.trans (ih (Nat.le_trans frontier extension.grows) written)

theorem initializeArrayHeader_extension (reference : Reference)
    (region : reference.region = .memory invocation) (above : cutoff ≤ reference.address.toNat)
    (written : initializeArrayHeader heap budget reference count dynamic = .ok (data, after, remaining)) :
    MemoryExtension cutoff heap after ∧ data.region = .memory invocation ∧
    cutoff ≤ data.address.toNat := by
  cases dynamic with
  | false =>
      cases written
      exact ⟨.refl cutoff _, region, above⟩
  | true =>
      unfold initializeArrayHeader at written
      cases reserved : reserve budget 32 with
      | error failure => simp [reserved] at written
      | ok available =>
          simp only [reserved, Bind.bind, Except.bind] at written
          cases stored : Defaults.writeMemoryValue heap reference ⟨.uint 31, BitVec.ofNat 256 count⟩ with
          | error failure => simp [stored] at written
          | ok next =>
              simp only [stored] at written
              cases advanced : Access.advance reference 32 with
              | error failure => simp [advanced] at written
              | ok result =>
                  have position := advance_memory reference 32 region advanced
                  have extension := writeMemoryValue_extension reference _ region above stored
                  simp only [advanced] at written
                  cases written
                  exact ⟨extension, position.1, by omega⟩

theorem memoryArray_extension (materialize : Materialize) (safe : MakesMemoryExtension materialize)
    (written : memoryArray materialize heap budget element size pointer values = .ok (value, after, remaining)) :
    MemoryExtension heap.nextMemory heap after := by
  unfold memoryArray at written
  split at written
  · cases written
  · cases sized : MemoryOps.arraySize values.length false size.isNone with
    | error failure => simp [sized] at written
    | ok bytes =>
        simp only [sized, Bind.bind, Except.bind] at written
        cases allocated : MemoryOps.allocate heap budget bytes with
        | error failure => simp [allocated] at written
        | ok result =>
            rcases result with ⟨reference, next, available⟩
            have first := allocate_extension allocated (Nat.le_refl heap.nextMemory)
            simp only [allocated] at written
            cases initialized : initializeArrayHeader next available reference values.length size.isNone with
            | error failure => simp [initialized] at written
            | ok result =>
                rcases result with ⟨data, populated, rest⟩
                have second := initializeArrayHeader_extension reference first.2.1
                  (by omega : heap.nextMemory ≤ reference.address.toNat) initialized
                simp only [initialized] at written
                cases reserved : reserve rest values.length with
                | error failure => simp [reserved] at written
                | ok finalBudget =>
                    simp only [reserved] at written
                    cases filled : values.zipIdx.foldlM (memoryCell materialize data element)
                        (populated, finalBudget) with
                    | error failure => simp [filled] at written
                    | ok result =>
                        rcases result with ⟨final, unused⟩
                        have third := fold_extension (memoryCell materialize data element)
                          (fun heap budget item after remaining frontier done =>
                            memoryCell_extension materialize safe data element second.2.1 second.2.2 frontier done)
                          values.zipIdx ((first.1.trans second.1).grows) filled
                        simp only [filled] at written
                        cases written
                        exact (first.1.trans second.1).trans third

theorem memoryStruct_extension (materialize : Materialize) (safe : MakesMemoryExtension materialize)
    (written : memoryStruct materialize registry heap budget identity pointer values = .ok (value, after, remaining)) :
    MemoryExtension heap.nextMemory heap after := by
  unfold memoryStruct at written
  cases fields : registry.structFields identity with
  | none => simp [fields] at written
  | some members =>
      simp only [fields] at written
      split at written
      · cases written
      · cases sized : MemoryOps.arraySize members.length false false with
        | error failure => simp [sized] at written
        | ok bytes =>
            simp only [sized, Bind.bind, Except.bind] at written
            cases allocated : MemoryOps.allocate heap budget bytes with
            | error failure => simp [allocated] at written
            | ok result =>
                rcases result with ⟨reference, next, available⟩
                have first := allocate_extension allocated (Nat.le_refl heap.nextMemory)
                simp only [allocated] at written
                cases reserved : reserve available members.length with
                | error failure => simp [reserved] at written
                | ok rest =>
                    simp only [reserved] at written
                    cases filled : ((members.map Prod.snd).zip values).zipIdx.foldlM
                        (memoryField materialize reference) (next, rest) with
                    | error failure => simp [filled] at written
                    | ok result =>
                        rcases result with ⟨final, unused⟩
                        have second := fold_extension (memoryField materialize reference)
                          (fun heap budget item after remaining frontier done =>
                            memoryCell_extension materialize safe reference item.1.1 first.2.1
                              (by omega : _ ≤ reference.address.toNat) frontier done)
                          _ first.1.grows filled
                        simp only [filled] at written
                        cases written
                        exact first.1.trans second

theorem initializeLength_extension (reference : Reference)
    (region : reference.region = .memory invocation) (above : cutoff ≤ reference.address.toNat)
    (written : Defaults.initializeLength heap budget reference count dynamic = .ok (after, remaining)) :
    MemoryExtension cutoff heap after := by
  cases dynamic with
  | false => cases written; exact .refl cutoff _
  | true =>
      unfold Defaults.initializeLength at written
      cases reserved : reserve budget 32 with
      | error failure => simp [reserved] at written
      | ok rest =>
          simp only [reserved, Bind.bind, Except.bind] at written
          cases stored : Defaults.writeMemoryValue heap reference ⟨.uint 31, BitVec.ofNat 256 count⟩ with
          | error failure => simp [stored] at written
          | ok final =>
              simp only [stored] at written
              cases written
              exact writeMemoryValue_extension reference _ region above stored

theorem newBytes_extension
    (written : Defaults.newBytes budget heap count string = .ok (value, after, remaining)) :
    MemoryExtension heap.nextMemory heap after ∧
    (∀ reference, value.reference = some reference →
      reference.region = .memory heap.invocation ∧ heap.nextMemory ≤ reference.address.toNat) := by
  unfold Defaults.newBytes at written
  cases sized : MemoryOps.arraySize count true true with
  | error failure => simp [sized] at written
  | ok bytes =>
      simp only [sized, Bind.bind, Except.bind] at written
      cases allocated : MemoryOps.allocate heap budget bytes with
      | error failure => simp [allocated] at written
      | ok result =>
          rcases result with ⟨reference, next, available⟩
          have first := allocate_extension allocated (Nat.le_refl heap.nextMemory)
          simp only [allocated] at written
          cases initialized : Defaults.initializeLength next available reference count true with
          | error failure => simp [initialized] at written
          | ok result =>
              rcases result with ⟨final, rest⟩
              have second := initializeLength_extension reference first.2.1
                (by omega : heap.nextMemory ≤ reference.address.toNat) initialized
              simp only [initialized] at written
              cases string <;> cases written
              all_goals
                refine ⟨first.1.trans second, ?_⟩
                intro pointer same
                cases same
                exact ⟨first.2.1, Nat.le_of_eq first.2.2.symm⟩

theorem writePacket_extension (above : cutoff ≤ reference.address.toNat)
    (written : writePacket heap budget reference bytes = .ok (after, remaining)) :
    MemoryExtension cutoff heap after := by
  rw [writePacket_shape written]
  refine ⟨fun valid => valid, Nat.le_refl _, fun _ h => h, ?_⟩
  intro offset count _ stop
  exact MemoryOps.snapshotCopy_frame heap reference.address.toNat bytes offset count (Or.inl (by omega))

theorem memoryBytes_extension
    (written : memoryBytes heap budget pointer string bytes = .ok (value, after, remaining)) :
    MemoryExtension heap.nextMemory heap after := by
  unfold memoryBytes at written
  cases created : Defaults.newBytes budget heap bytes.length string with
  | error failure => simp [created] at written
  | ok result =>
      rcases result with ⟨source, next, available⟩
      have first := newBytes_extension created
      simp only [created, Bind.bind, Except.bind] at written
      cases located : Defaults.asPlace source with
      | error failure => simp [located] at written
      | ok place =>
          have reference : source.reference = some place.reference := by
            unfold Defaults.asPlace at located
            cases same : source.reference with
            | none => simp [same] at located
            | some pointer =>
                simp only [same] at located
                cases located
                rfl
          have position := first.2 place.reference reference
          simp only [located] at written
          cases advanced : Access.advance place.reference 32 with
          | error failure => simp [advanced] at written
          | ok data =>
              have address := advance_memory place.reference 32 position.1 advanced
              simp only [advanced] at written
              cases stored : writePacket next available data bytes with
              | error failure => simp [stored] at written
              | ok result =>
                  rcases result with ⟨final, rest⟩
                  have second := writePacket_extension
                    (by omega : heap.nextMemory ≤ data.address.toNat) stored
                  simp only [stored] at written
                  cases tagged : retag (if string then .string .memory pointer else .bytes .memory pointer)
                      place.reference with
                  | error failure => simp [tagged] at written
                  | ok output =>
                      simp only [tagged] at written
                      cases written
                      exact first.1.trans second

theorem buildMemory_extension (registry : Registry) (fuel : Nat) :
    MakesMemoryExtension (buildMemory registry fuel) := by
  induction fuel with
  | zero => intro budget heap type contents value after remaining done; cases done
  | succ fuel ih =>
      intro budget heap type contents value after remaining done
      unfold buildMemory at done
      split at done
      · exact memoryArray_extension _ ih done
      · split at done
        · cases done
        · exact memoryStruct_extension _ ih done
      · exact memoryBytes_extension done
      · exact memoryBytes_extension done
      · unfold memoryScalar at done
        rename_i _ _ source
        cases converted : convertScalar type source with
        | error failure => simp [converted] at done
        | ok output =>
            simp only [converted] at done
            cases done
            exact .refl _ _
      · cases done

theorem materializeMemory_extension
    (written : materializeMemory registry fuel budget heap type contents = .ok (value, after, remaining)) :
    MemoryExtension heap.nextMemory heap after := by
  unfold materializeMemory at written
  cases checked : eligibleAt registry fuel (.memory heap.invocation) type with
  | error failure => simp [checked] at written
  | ok _ =>
      simp only [checked, Bind.bind, Except.bind] at written
      exact buildMemory_extension registry fuel budget heap type contents value after remaining written

end Solidity.Aggregates.Copy
