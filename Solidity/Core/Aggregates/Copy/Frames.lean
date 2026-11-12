/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy.Laws

namespace Solidity.Aggregates.Copy
open Core Static
open Contract.Interaction (Word Memory wordBytes bytesWord)

def Frame (before after : Heap) : Prop :=
  after.execution.world = before.execution.world ∧ after.invocation = before.invocation

private theorem Frame.refl (heap : Heap) : Frame heap heap := ⟨rfl, rfl⟩

private theorem Frame.trans (first : Frame before middle) (last : Frame middle after) :
    Frame before after := ⟨last.1.trans first.1, last.2.trans first.2⟩

def MakesFrame (materialize : Materialize) : Prop :=
  ∀ budget heap type contents value after remaining,
    materialize budget heap type contents = .ok (value, after, remaining) → Frame heap after

private theorem result_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem result_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] result_map_error result_map_ok

private theorem fold_frame (step : (Heap × Nat) → α → Result (Heap × Nat))
    (safe : ∀ heap budget item after remaining,
      step (heap, budget) item = .ok (after, remaining) → Frame heap after)
    (items : List α) (heap after : Heap) (budget remaining : Nat)
    (written : items.foldlM step (heap, budget) = .ok (after, remaining)) : Frame heap after := by
  induction items generalizing heap budget with
  | nil => cases written; exact Frame.refl after
  | cons item rest ih =>
      rw [List.foldlM_cons] at written
      cases first : step (heap, budget) item with
      | error failure => simp [first] at written <;> cases written
      | ok result =>
          rcases result with ⟨next, available⟩
          simp only [first, Bind.bind, Except.bind] at written
          exact (safe heap budget item next available first).trans (ih next available written)

private theorem memoryCell_frame (materialize : Materialize) (safe : MakesFrame materialize)
    (data : Reference) (type : SType) (heap after : Heap) (budget remaining : Nat)
    (entry : Contents × Nat)
    (written : memoryCell materialize data type (heap, budget) entry = .ok (after, remaining)) :
    Frame heap after := by
  unfold memoryCell at written
  cases made : materialize budget heap (atLocation type .memory false) entry.1 with
  | error failure => simp [made] at written <;> cases written
  | ok result =>
      rcases result with ⟨value, next, rest⟩
      have first := safe budget heap _ entry.1 value next rest made
      simp only [made, Bind.bind, Except.bind] at written
      cases reserved : reserve rest 32 with
      | error failure => simp [reserved] at written <;> cases written
      | ok available =>
          simp only [reserved] at written
          cases advanced : Access.advance data (entry.2*32) with
          | error failure => simp [advanced] at written <;> cases written
          | ok reference =>
              simp only [advanced] at written
              cases stored : Defaults.writeMemoryValue next reference value with
              | error failure => simp [stored] at written <;> cases written
              | ok final =>
                  simp only [stored] at written
                  have last := Defaults.writeMemoryValue_frame next final reference value stored
                  cases written
                  exact first.trans ⟨last.1, last.2.1⟩

private theorem initializeArrayHeader_frame (heap after : Heap) (budget remaining count : Nat)
    (reference data : Reference) (dynamic : Bool)
    (written : initializeArrayHeader heap budget reference count dynamic = .ok (data, after, remaining)) :
    Frame heap after := by
  cases dynamic with
  | false =>
      have frame := Frame.refl heap
      cases written
      exact frame
  | true =>
      unfold initializeArrayHeader at written
      cases reserved : reserve budget 32 with
      | error failure => simp [reserved] at written <;> cases written
      | ok available =>
          simp only [reserved, Bind.bind, Except.bind] at written
          cases stored : Defaults.writeMemoryValue heap reference ⟨.uint 31, BitVec.ofNat 256 count⟩ with
          | error failure => simp [stored] at written <;> cases written
          | ok final =>
              simp only [stored] at written
              cases advanced : Access.advance reference 32 with
              | error failure => simp [advanced] at written <;> cases written
              | ok next =>
                  simp only [advanced] at written
                  have frame := Defaults.writeMemoryValue_frame heap final reference _ stored
                  cases written
                  exact ⟨frame.1, frame.2.1⟩

theorem memoryArray_frame (materialize : Materialize) (safe : MakesFrame materialize)
    (heap after : Heap) (budget remaining : Nat) (element : SType) (size : Option Nat)
    (pointer : Bool) (values : List Contents) (value : Value)
    (written : memoryArray materialize heap budget element size pointer values =
      .ok (value, after, remaining)) : Frame heap after := by
  unfold memoryArray at written
  split at written
  · cases written
  · cases sized : MemoryOps.arraySize values.length false size.isNone with
    | error failure => simp [sized] at written <;> cases written
    | ok bytes =>
        simp only [sized, Bind.bind, Except.bind] at written
        cases allocated : MemoryOps.allocate heap budget bytes with
        | error failure => simp [allocated] at written <;> cases written
        | ok result =>
            rcases result with ⟨reference, fresh, available⟩
            have first := MemoryOps.allocate_frame heap fresh budget bytes available reference allocated
            simp only [allocated] at written
            cases header : initializeArrayHeader fresh available reference values.length size.isNone with
            | error failure => simp [header] at written <;> cases written
            | ok result =>
                rcases result with ⟨data, initialized, rest⟩
                have second := initializeArrayHeader_frame fresh initialized available rest _ reference data _ header
                simp only [header] at written
                cases reserved : reserve rest values.length with
                | error failure => simp [reserved] at written <;> cases written
                | ok allowance =>
                    simp only [reserved] at written
                    cases filled : values.zipIdx.foldlM (memoryCell materialize data element) (initialized, allowance) with
                    | error failure => simp [filled] at written <;> cases written
                    | ok result =>
                        rcases result with ⟨final, left⟩
                        simp only [filled] at written
                        have last := fold_frame (memoryCell materialize data element)
                          (fun heap budget item after remaining h =>
                            memoryCell_frame materialize safe data element heap after budget remaining item h)
                          _ initialized final allowance left filled
                        cases written
                        exact (show Frame heap fresh from first).trans (second.trans last)

theorem memoryStruct_frame (materialize : Materialize) (safe : MakesFrame materialize)
    (registry : Registry) (heap after : Heap) (budget remaining identity : Nat)
    (pointer : Bool) (values : List Contents) (value : Value)
    (written : memoryStruct materialize registry heap budget identity pointer values =
      .ok (value, after, remaining)) : Frame heap after := by
  unfold memoryStruct at written
  cases fields : registry.structFields identity with
  | none => simp [fields] at written <;> cases written
  | some members =>
      simp only [fields, Bind.bind, Except.bind] at written
      split at written
      · cases written
      · cases sized : MemoryOps.arraySize members.length false false with
        | error failure => simp [sized] at written <;> cases written
        | ok bytes =>
            simp only [sized] at written
            cases allocated : MemoryOps.allocate heap budget bytes with
            | error failure => simp [allocated] at written <;> cases written
            | ok result =>
                rcases result with ⟨reference, fresh, available⟩
                have first := MemoryOps.allocate_frame heap fresh budget bytes available reference allocated
                simp only [allocated] at written
                cases reserved : reserve available members.length with
                | error failure => simp [reserved] at written <;> cases written
                | ok allowance =>
                    simp only [reserved] at written
                    cases filled : ((members.map Prod.snd).zip values).zipIdx.foldlM
                        (memoryField materialize reference) (fresh, allowance) with
                    | error failure => simp [filled] at written <;> cases written
                    | ok result =>
                        rcases result with ⟨final, left⟩
                        simp only [filled] at written
                        have last := fold_frame (memoryField materialize reference)
                          (fun heap budget item after remaining h =>
                            memoryCell_frame materialize safe reference item.1.1 heap after budget remaining
                              (item.1.2, item.2) h)
                          _ fresh final allowance left filled
                        cases written
                        exact (show Frame heap fresh from first).trans last

theorem memoryBytes_frame (heap after : Heap) (budget remaining : Nat)
    (pointer string : Bool) (bytes : List UInt8) (value : Value)
    (written : memoryBytes heap budget pointer string bytes = .ok (value, after, remaining)) :
    Frame heap after := by
  unfold memoryBytes at written
  cases allocated : Defaults.newBytes budget heap bytes.length string with
  | error failure => simp [allocated] at written <;> cases written
  | ok result =>
      rcases result with ⟨freshValue, fresh, available⟩
      have first := Defaults.newBytes_frame budget available bytes.length heap fresh string freshValue allocated
      simp only [allocated, Bind.bind, Except.bind] at written
      cases placed : Defaults.asPlace freshValue with
      | error failure => simp [placed] at written <;> cases written
      | ok place =>
          simp only [placed] at written
          cases advanced : Access.advance place.reference 32 with
          | error failure => simp [advanced] at written <;> cases written
          | ok data =>
              simp only [advanced] at written
              cases copied : writePacket fresh available data bytes with
              | error failure => simp [copied] at written <;> cases written
              | ok result =>
                  rcases result with ⟨final, left⟩
                  have shape := writePacket_shape copied
                  have last : Frame fresh final := by rw [shape]; exact ⟨rfl, rfl⟩
                  simp only [copied] at written
                  cases tagged : retag (if string then .string .memory pointer else .bytes .memory pointer) place.reference with
                  | error failure => simp [tagged] at written <;> cases written
                  | ok taggedValue =>
                      simp only [tagged] at written
                      cases written
                      exact (show Frame heap fresh from first).trans last

private theorem memoryScalar_frame
    (written : memoryScalar heap budget type source = .ok (value, after, remaining)) :
    Frame heap after := by
  unfold memoryScalar at written
  cases converted : convertScalar type source with
  | error failure => simp [converted] at written <;> cases written
  | ok result =>
      simp only [converted] at written
      have frame := Frame.refl heap
      cases written
      exact frame

theorem buildMemory_frame (registry : Registry) (fuel : Nat) :
    MakesFrame (buildMemory registry fuel) := by
  induction fuel with
  | zero => intro budget heap type contents value after remaining written; cases written
  | succ fuel ih =>
      intro budget heap type contents value after remaining written
      cases contents with
      | scalar source =>
          have equation : buildMemory registry (fuel+1) budget heap type (.scalar source) =
              memoryScalar heap budget type source := by
            cases type <;> try rfl
            all_goals rename_i location pointer; cases location <;> rfl
          rw [equation] at written
          exact memoryScalar_frame written
      | array sourceElement values =>
          cases type <;> simp only [buildMemory] at written <;> try cases written
          case array element size location pointer =>
            cases location <;> simp only at written <;> try cases written
            exact memoryArray_frame _ ih _ _ _ _ _ _ _ _ _ written
      | «structure» sourceIdentity values =>
          cases type <;> simp only [buildMemory] at written <;> try cases written
          case structType identity location pointer =>
            cases location <;> simp only at written <;> try cases written
            split at written
            · cases written
            · exact memoryStruct_frame _ ih _ _ _ _ _ _ _ _ _ written
      | bytes string bytes =>
          cases type <;> simp only [buildMemory] at written <;> try cases written
          case bytes location pointer =>
            cases location <;> cases string <;> simp only at written <;> try cases written
            exact memoryBytes_frame _ _ _ _ _ _ _ _ written
          case string location pointer =>
            cases location <;> cases string <;> simp only at written <;> try cases written
            exact memoryBytes_frame _ _ _ _ _ _ _ _ written

theorem materializeMemory_frame
    (written : materializeMemory registry fuel budget heap type contents = .ok (value, after, remaining)) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation := by
  unfold materializeMemory at written
  cases eligible : eligibleAt registry fuel (.memory heap.invocation) type with
  | error failure => simp [eligible] at written <;> cases written
  | ok _ =>
      simp only [eligible, Bind.bind, Except.bind] at written
      exact buildMemory_frame registry fuel budget heap type contents value after remaining written

theorem bind_frame
    (written : bind registry fuel budget heap type source = .ok (value, after, remaining)) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation := by
  cases planned : planTransfer registry fuel true source.type type with
  | error failure => simp only [bind, planned, Bind.bind, Except.bind] at written; cases written
  | ok kind =>
      rw [bind_of_plan planned] at written
      cases kind <;> simp only at written
      all_goals try cases written
      case scalarConversion => exact memoryScalar_frame written
      case storageAlias | memoryAlias | calldataAlias =>
        cases aliased : alias heap type source with
        | error failure => simp [aliased] at written <;> cases written
        | ok result =>
            simp only [aliased] at written
            have frame := Frame.refl heap
            cases written
            exact frame
      case memoryCopy =>
        cases frozen : snapshotValue registry fuel budget heap source with
        | error failure => simp [frozen] at written <;> cases written
        | ok result =>
            rcases result with ⟨contents, available⟩
            simp only [frozen, Bind.bind, Except.bind] at written
            exact materializeMemory_frame written

private theorem accessWrite_memory_frame (memory : place.reference.region = .memory invocation)
    (written : Access.write heap place value = .ok after) : Frame heap after := by
  unfold Access.write at written
  cases valid : Access.validate heap place with
  | error failure => simp [valid] at written <;> cases written
  | ok _ =>
      simp only [valid, Bind.bind, Except.bind] at written
      split at written
      · have frame := writeScalar_memory_frame heap after place _ invocation memory written
        exact ⟨frame.1, frame.2.1⟩
      · cases written

private theorem copyToStorage_ne_memory (memory : target.reference.region = .memory invocation)
    (written : copyToStorage registry fuel budget heap source target = .ok (after, remaining)) : False := by
  cases fuel with
  | zero => cases written
  | succ fuel =>
      unfold copyToStorage at written
      cases validSource : Access.validate heap source with
      | error failure => simp [validSource] at written <;> cases written
      | ok _ =>
          simp only [validSource, Bind.bind, Except.bind] at written
          cases validTarget : Access.validate heap target with
          | error failure => simp [validTarget] at written <;> cases written
          | ok _ => simp [validTarget, memory] at written

private theorem memoryBinding_frame (result : Result (Value × Heap × Nat))
    (safe : ∀ value copied available, result = .ok (value, copied, available) → Frame heap copied)
    (written : (do
      let cell ← bindingReference destination
      let (value, copied, available) ← result
      return (← Defaults.writeMemoryValue copied cell value, available)) = .ok (after, remaining)) :
    Frame heap after := by
  cases captured : bindingReference destination with
  | error failure => simp [captured] at written <;> cases written
  | ok cell =>
      simp only [captured, Bind.bind, Except.bind] at written
      cases bound : result with
      | error failure => simp [bound] at written <;> cases written
      | ok output =>
          rcases output with ⟨value, copied, available⟩
          have first := safe value copied available bound
          simp only [bound] at written
          cases stored : Defaults.writeMemoryValue copied cell value with
          | error failure => simp [stored] at written <;> cases written
          | ok final =>
              have last := Defaults.writeMemoryValue_frame copied final cell value stored
              simp only [stored] at written
              cases written
              exact first.trans ⟨last.1, last.2.1⟩

/-- A memory scalar assignment or captured pointer rebinding cannot change
the persistent/transient world, including when rebinding first makes a copy. -/
theorem assign_memory_frame (memory : destination.reference.region = .memory invocation)
    (written : assign registry fuel budget heap destination source = .ok (after, remaining)) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation := by
  have original := written
  unfold assign at written
  cases valid : Access.validate heap destination with
  | error failure => simp [valid] at written <;> cases written
  | ok _ =>
      simp only [valid, Bind.bind, Except.bind] at written
      cases planned : planTransfer registry fuel false source.type destination.type with
      | error failure => simp [planned] at written <;> cases written
      | ok kind =>
          simp only [planned] at written
          cases kind <;> simp only at written
          case scalarConversion =>
            cases converted : convertScalar destination.type source with
            | error failure => simp [converted] at written <;> cases written
            | ok value =>
                simp only [converted] at written
                cases stored : Access.write heap destination value with
                | error failure => simp [stored] at written <;> cases written
                | ok final =>
                    have frame := accessWrite_memory_frame memory stored
                    simp only [stored] at written
                    cases written
                    exact frame
          case storageCopy =>
            cases placed : Defaults.asPlace source with
            | error failure => simp [placed] at written <;> cases written
            | ok place =>
                simp only [placed] at written
                exact False.elim (copyToStorage_ne_memory memory written)
          case memoryAlias =>
            rw [assign_of_plan valid planned] at original
            apply memoryBinding_frame _ ?_ original
            intro value copied available bound
            cases aliased : alias heap destination.type source with
            | error failure => simp [aliased] at bound
            | ok result =>
                simp only [aliased, Bind.bind, Except.bind, Pure.pure, Except.pure] at bound
                cases bound
                exact Frame.refl heap
          case memoryCopy =>
            rw [assign_of_plan valid planned] at original
            apply memoryBinding_frame _ ?_ original
            intro value copied available bound
            cases frozen : snapshotValue registry fuel budget heap source with
            | error failure => simp only [frozen, Bind.bind, Except.bind] at bound; cases bound
            | ok result =>
                rcases result with ⟨contents, rest⟩
                simp only [frozen, Bind.bind, Except.bind] at bound
                exact materializeMemory_frame bound
          case storageAlias | calldataAlias => cases written


end Solidity.Aggregates.Copy
