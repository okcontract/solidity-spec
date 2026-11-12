/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.StorageCopyRepresentation
import Solidity.Core.Aggregates.StorageMutationRepresentation

/-! Recursive ordered storage-copy derivations. The judgments expose the
source value/packet, conversion, resize, captured member positions and child
order. They are independent of the complete copy function's result equation.
The executable equivalences below establish both coverage and realizability. -/
namespace Solidity.Aggregates.Copy
open Core Static
open Contract.Interaction (Word)

abbrev CopyRelation := Nat → Heap → Place → Place → List StorageEvent → Heap × Nat → Prop

private theorem copied_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem copied_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] copied_map_error copied_map_ok Bind.bind Except.bind Pure.pure Except.pure

theorem access_write_storage_trace
    (storage : StorageRegion target.reference.region)
    (written : Access.write heap target value = .ok after) :
    ∃ events, StorageTrace heap events after := by
  unfold Access.write at written
  cases checked : Access.validate heap target with
  | error failure => simp [checked] at written
  | ok _ =>
      simp only [checked, Bind.bind, Except.bind] at written
      split at written
      · exact writeScalar_storage_trace _ _ storage written
      · cases written

inductive ScalarCopyRule (budget : Nat) (source target : Place) :
    Heap → List StorageEvent → Heap × Nat → Prop where
  | step (before after : Heap) (value converted : Value) (events : List StorageEvent)
      (read : Access.read before source = .ok value)
      (conversion : convertScalar target.type value = .ok converted)
      (written : Access.write before target converted = .ok after)
      (trace : StorageTrace before events after) :
      ScalarCopyRule budget source target before events (after, budget)

theorem ScalarCopyRule.trace
    (copied : ScalarCopyRule budget source target before events after) : StorageTrace before events after.1 := by
  cases copied with | step _ _ _ _ _ _ _ traced => exact traced

theorem scalarCopy_iff (storage : StorageRegion target.reference.region) :
    scalarCopy before budget source target = .ok after ↔
    ∃ events, ScalarCopyRule budget source target before events after := by
  unfold scalarCopy
  constructor
  · intro finished
    cases read : Access.read before source with
    | error failure => simp [read] at finished
    | ok value =>
        simp only [read, Bind.bind, Except.bind] at finished
        cases conversion : convertScalar target.type value with
        | error failure => simp [conversion] at finished
        | ok converted =>
            simp only [conversion] at finished
            cases written : Access.write before target converted with
            | error failure => simp [written] at finished
            | ok next =>
                simp only [written, Pure.pure, Except.pure] at finished
                cases finished
                obtain ⟨events, trace⟩ := access_write_storage_trace storage written
                exact ⟨events, .step before next value converted events read conversion written trace⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | step _ _ _ _ read conversion written _ => simp only [read, conversion, written, Bind.bind, Except.bind, Pure.pure, Except.pure]

inductive StorageBytesRule (budget : Nat) (source target : Reference) :
    Heap → List StorageEvent → Heap × Nat → Prop where
  | step (before : Heap) (header : Word) (count : Nat) (events : List StorageEvent) (after : Heap × Nat)
      (loaded : HeaderRead before source header count)
      (copied : BytesTransfer (.storage source count) target count budget before events after) :
      StorageBytesRule budget source target before (.load source.region source.address header :: events) after

theorem StorageBytesRule.trace
    (copied : StorageBytesRule budget source target before events after) : StorageTrace before events after.1 := by
  cases copied with | step _ _ _ _ loaded copied => exact .load loaded.read copied.trace

theorem streamBytes_iff : streamBytes before budget source target = .ok after ↔
    ∃ events, StorageBytesRule budget source target before events after := by
  unfold streamBytes
  constructor
  · intro finished
    cases loaded : StorageBytes.loadHeader before source with
    | error failure => simp [loaded] at finished
    | ok pair =>
        rcases pair with ⟨header, count⟩
        simp only [loaded, Bind.bind, Except.bind] at finished
        obtain ⟨events, copied⟩ := (writeBytesFrom_iff (source := ByteSource.storage source count)).mp finished
        exact ⟨_, .step before header count events after (loadHeader_iff.mp loaded) copied⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | step _ _ _ _ loaded copied =>
        simp only [loadHeader_iff.mpr loaded, Bind.bind, Except.bind]
        exact writeBytesFrom_iff.mpr ⟨_, copied⟩

inductive ArrayChild (child : CopyRelation) (registry : Registry) (fuel : Nat)
    (source target : Place) (sourceElement targetElement : SType) :
    Heap × Nat → Nat → List StorageEvent → Heap × Nat → Prop where
  | step (before : Heap × Nat) (index : Nat) (sourceChild targetChild : Place)
      (events : List StorageEvent) (after : Heap × Nat)
      (sourcePosition : storageElement registry fuel source sourceElement index = .ok sourceChild)
      (targetPosition : storageElement registry fuel target targetElement index = .ok targetChild)
      (copied : child before.2 before.1 sourceChild targetChild events after) :
      ArrayChild child registry fuel source target sourceElement targetElement before index events after

theorem arrayChild_iff {copy : StorageCopyCall} {child : CopyRelation} (law : ∀ budget heap source target after,
    copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after) :
    (do
      let a ← storageElement registry fuel source sourceElement index
      let b ← storageElement registry fuel target targetElement index
      copy before.2 before.1 a b) = .ok after ↔
    ∃ events, ArrayChild child registry fuel source target sourceElement targetElement before index events after := by
  constructor
  · intro finished
    cases a : storageElement registry fuel source sourceElement index with
    | error failure => simp [a] at finished
    | ok sourceChild =>
        simp only [a, Bind.bind, Except.bind] at finished
        cases b : storageElement registry fuel target targetElement index with
        | error failure => simp [b] at finished
        | ok targetChild =>
            simp only [b] at finished
            obtain ⟨events, copied⟩ := (law _ _ _ _ _).mp finished
            exact ⟨events, .step before index sourceChild targetChild events after a b copied⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | step _ _ _ _ a b copied => simp only [a, b, Bind.bind, Except.bind]; exact (law _ _ _ _ _).mpr ⟨_, copied⟩

inductive StorageArrayRule (child : CopyRelation) (registry : Registry) (fuel budget : Nat)
    (source target : Place) (sourceElement targetElement : SType) :
    Heap → List StorageEvent → Heap × Nat → Prop where
  | scalars (before middle : Heap) (count available remaining sourceBytes targetBytes : Nat)
      (sourceData targetData : Reference) (resizeEvents copyEvents : List StorageEvent) (after : Heap × Nat)
      (length : Access.length before source = .ok count)
      (bounded : ¬((storageBytes targetElement).isSome = true ∧ MemoryOps.maximumMemory < count))
      (reserved : reserve budget count = .ok available)
      (resized : StorageArrays.resize registry fuel available before target count = .ok (middle, remaining))
      (resizeTrace : StorageTrace before resizeEvents middle)
      (sourceSized : storageBytes sourceElement = some sourceBytes)
      (targetSized : storageBytes targetElement = some targetBytes)
      (sourcePosition : Access.arrayData source = .ok sourceData)
      (targetPosition : Access.arrayData target = .ok targetData)
      (copied : ScalarStream sourceElement targetElement sourceData targetData sourceBytes targetBytes
        count remaining middle copyEvents after) :
      StorageArrayRule child registry fuel budget source target sourceElement targetElement before
        (resizeEvents ++ copyEvents) after
  | references (before middle : Heap) (count available remaining : Nat)
      (resizeEvents copyEvents : List StorageEvent) (after : Heap × Nat)
      (length : Access.length before source = .ok count)
      (bounded : ¬((storageBytes targetElement).isSome = true ∧ MemoryOps.maximumMemory < count))
      (reserved : reserve budget count = .ok available)
      (resized : StorageArrays.resize registry fuel available before target count = .ok (middle, remaining))
      (resizeTrace : StorageTrace before resizeEvents middle)
      (sourceSized : storageBytes sourceElement = none)
      (targetSized : storageBytes targetElement = none)
      (copied : CopyFold (ArrayChild child registry fuel source target sourceElement targetElement)
        (middle, remaining) (List.range count) copyEvents after) :
      StorageArrayRule child registry fuel budget source target sourceElement targetElement before
        (resizeEvents ++ copyEvents) after

theorem storageArrayCopy_iff {copy : StorageCopyCall} {child : CopyRelation} (law : ∀ budget heap source target after,
    copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after) :
    storageArrayCopy copy registry fuel budget before source target sourceElement targetElement = .ok after ↔
    ∃ events, StorageArrayRule child registry fuel budget source target sourceElement targetElement before events after := by
  unfold storageArrayCopy
  constructor
  · intro finished
    cases length : Access.length before source with
    | error failure => simp [length] at finished
    | ok count =>
        simp only [length, Bind.bind, Except.bind] at finished
        split at finished
        · cases finished
        · rename_i bounded
          have bounds : ¬((storageBytes targetElement).isSome = true ∧ MemoryOps.maximumMemory < count) := by simpa using bounded
          cases reserved : reserve budget count with
          | error failure => simp [reserved] at finished
          | ok available =>
              simp only [reserved] at finished
              cases resized : StorageArrays.resize registry fuel available before target count with
              | error failure => simp [resized] at finished
              | ok pair =>
                  rcases pair with ⟨middle, remaining⟩
                  simp only [resized] at finished
                  obtain ⟨resizeEvents, resizeTrace⟩ := StorageArrays.resize_trace resized
                  cases sourceSized : storageBytes sourceElement with
                  | some sourceBytes =>
                      cases targetSized : storageBytes targetElement with
                      | none => simp [sourceSized, targetSized] at finished
                      | some targetBytes =>
                          simp only [sourceSized, targetSized] at finished
                          cases sourcePosition : Access.arrayData source with
                          | error failure => simp [sourcePosition] at finished
                          | ok sourceData =>
                              simp only [sourcePosition] at finished
                              cases targetPosition : Access.arrayData target with
                              | error failure => simp [targetPosition] at finished
                              | ok targetData =>
                                  simp only [targetPosition] at finished
                                  obtain ⟨events, copied⟩ := streamScalars_iff.mp finished
                                  exact ⟨_, .scalars before middle count available remaining sourceBytes targetBytes
                                    sourceData targetData resizeEvents events after length bounds reserved resized resizeTrace
                                    sourceSized targetSized sourcePosition targetPosition copied⟩
                  | none =>
                      cases targetSized : storageBytes targetElement with
                      | some bytes => simp [sourceSized, targetSized] at finished
                      | none =>
                          simp only [sourceSized, targetSized] at finished
                          obtain ⟨events, copied⟩ := (CopyFold.iff_foldlM _
                            (fun _ _ _ => arrayChild_iff law) _ _ _).mp finished
                          exact ⟨_, .references before middle count available remaining resizeEvents events after
                            length bounds reserved resized resizeTrace sourceSized targetSized copied⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | scalars _ count _ _ _ _ _ _ _ _ _ length bounded reserved resized _ a b c d copied =>
        have chosen : ¬((storageBytes targetElement).isSome && decide (MemoryOps.maximumMemory < count)) = true := by simpa using bounded
        simp only [length, Bind.bind, Except.bind]
        rw [if_neg chosen]
        simp only [Pure.pure, Except.pure, reserved, resized, a, b, c, d]
        exact streamScalars_iff.mpr ⟨_, copied⟩
    | references _ count _ _ _ _ _ length bounded reserved resized _ a b copied =>
        have chosen : ¬((storageBytes targetElement).isSome && decide (MemoryOps.maximumMemory < count)) = true := by simpa using bounded
        simp only [length, Bind.bind, Except.bind]
        rw [if_neg chosen]
        simp only [Pure.pure, Except.pure, reserved, resized, a, b]
        exact (CopyFold.iff_foldlM _ (fun _ _ _ => arrayChild_iff law) _ _ _).mpr ⟨_, copied⟩

inductive StructChild (child : CopyRelation) (registry : Registry) (fuel : Nat) (source target : Place) :
    Heap × Nat → Nat → List StorageEvent → Heap × Nat → Prop where
  | step (before : Heap × Nat) (index : Nat) (sourceChild targetChild : Place)
      (events : List StorageEvent) (after : Heap × Nat)
      (sourcePosition : Access.field registry fuel before.1 (StorageArrays.captured source) index = .ok sourceChild)
      (targetPosition : Access.field registry fuel before.1 (StorageArrays.captured target) index = .ok targetChild)
      (copied : child before.2 before.1 (StorageArrays.captured sourceChild)
        (StorageArrays.captured targetChild) events after) :
      StructChild child registry fuel source target before index events after

theorem structChild_iff {copy : StorageCopyCall} {child : CopyRelation}
    (law : ∀ budget heap source target after,
      copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after) :
    (do
      let a ← Access.field registry fuel before.1 (StorageArrays.captured source) index
      let b ← Access.field registry fuel before.1 (StorageArrays.captured target) index
      copy before.2 before.1 (StorageArrays.captured a) (StorageArrays.captured b)) = .ok after ↔
    ∃ events, StructChild child registry fuel source target before index events after := by
  constructor
  · intro finished
    cases a : Access.field registry fuel before.1 (StorageArrays.captured source) index with
    | error failure => simp [a] at finished
    | ok sourceChild =>
        simp only [a, Bind.bind, Except.bind] at finished
        cases b : Access.field registry fuel before.1 (StorageArrays.captured target) index with
        | error failure => simp [b] at finished
        | ok targetChild =>
            simp only [b] at finished
            obtain ⟨events, copied⟩ := (law _ _ _ _ _).mp finished
            exact ⟨events, .step before index sourceChild targetChild events after a b copied⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | step _ _ _ _ a b copied =>
        simp only [a, b, Bind.bind, Except.bind]
        exact (law _ _ _ _ _).mpr ⟨_, copied⟩

inductive StorageStructRule (child : CopyRelation) (registry : Registry) (fuel budget : Nat)
    (source target : Place) (identity targetIdentity : Nat) :
    Heap → List StorageEvent → Heap × Nat → Prop where
  | step (before : Heap) (fields : List (String × SType)) (available : Nat)
      (events : List StorageEvent) (after : Heap × Nat)
      (same : identity = targetIdentity)
      (metadata : registry.structFields identity = some fields)
      (reserved : reserve budget fields.length = .ok available)
      (copied : CopyFold (StructChild child registry fuel source target)
        (before, available) (List.range fields.length) events after) :
      StorageStructRule child registry fuel budget source target identity targetIdentity before events after

theorem storageStructCopy_iff {copy : StorageCopyCall} {child : CopyRelation}
    (law : ∀ budget heap source target after,
      copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after) :
    storageStructCopy copy registry fuel budget before source target identity targetIdentity = .ok after ↔
    ∃ events, StorageStructRule child registry fuel budget source target identity targetIdentity before events after := by
  unfold storageStructCopy
  constructor
  · intro finished
    by_cases same : identity = targetIdentity
    · have chosen : (identity != targetIdentity) = false := by simp [same]
      simp only [chosen, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at finished
      cases metadata : registry.structFields identity with
      | none => simp [metadata] at finished
      | some fields =>
          simp only [metadata] at finished
          cases reserved : reserve budget fields.length with
          | error failure => simp [reserved] at finished
          | ok available =>
              simp only [reserved] at finished
              obtain ⟨events, copied⟩ := (CopyFold.iff_foldlM _ (fun _ _ _ => structChild_iff law) _ _ _).mp finished
              exact ⟨events, .step before fields available events after same metadata reserved copied⟩
    · have chosen : (identity != targetIdentity) = true := by simp [same]
      simp [chosen] at finished
  · rintro ⟨_, copied⟩
    cases copied with
    | step fields _ _ _ same metadata reserved copied =>
        have chosen : (identity != targetIdentity) = false := by simp [same]
        simp only [chosen, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure, metadata, reserved]
        exact (CopyFold.iff_foldlM _ (fun _ _ _ => structChild_iff law) _ _ _).mpr ⟨_, copied⟩

inductive StorageBodyRule (child : CopyRelation) (registry : Registry) (fuel budget : Nat)
    (source target : Place) : Heap → List StorageEvent → Heap × Nat → Prop where
  | array (shape : storageCopyShape source.type target.type = .array a b)
      (copied : StorageArrayRule child registry fuel budget source target a b before events after) :
      StorageBodyRule child registry fuel budget source target before events after
  | structure (shape : storageCopyShape source.type target.type = .structure a b)
      (copied : StorageStructRule child registry fuel budget source target a b before events after) :
      StorageBodyRule child registry fuel budget source target before events after
  | bytes (shape : storageCopyShape source.type target.type = .bytes)
      (copied : StorageBytesRule budget source.reference target.reference before events after) :
      StorageBodyRule child registry fuel budget source target before events after
  | scalar (shape : storageCopyShape source.type target.type = .scalar)
      (copied : ScalarCopyRule budget source target before events after) :
      StorageBodyRule child registry fuel budget source target before events after

theorem storageCopyBody_iff {copy : StorageCopyCall} {child : CopyRelation}
    (law : ∀ budget heap source target after,
      copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after)
    (storage : StorageRegion target.reference.region) :
    storageCopyBody copy registry fuel budget before source target = .ok after ↔
    ∃ events, StorageBodyRule child registry fuel budget source target before events after := by
  unfold storageCopyBody
  constructor
  · intro finished
    cases shape : storageCopyShape source.type target.type with
    | array a b =>
        simp only [shape] at finished
        obtain ⟨events, copied⟩ := (storageArrayCopy_iff law).mp finished
        exact ⟨events, .array shape copied⟩
    | «structure» a b =>
        simp only [shape] at finished
        obtain ⟨events, copied⟩ := (storageStructCopy_iff law).mp finished
        exact ⟨events, .structure shape copied⟩
    | bytes =>
        simp only [shape] at finished
        obtain ⟨events, copied⟩ := streamBytes_iff.mp finished
        exact ⟨events, .bytes shape copied⟩
    | scalar =>
        simp only [shape] at finished
        obtain ⟨events, copied⟩ := (scalarCopy_iff storage).mp finished
        exact ⟨events, .scalar shape copied⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | array shape copied => rw [shape]; exact (storageArrayCopy_iff law).mpr ⟨_, copied⟩
    | «structure» shape copied => rw [shape]; exact (storageStructCopy_iff law).mpr ⟨_, copied⟩
    | bytes shape copied => rw [shape]; exact streamBytes_iff.mpr ⟨_, copied⟩
    | scalar shape copied => rw [shape]; exact (scalarCopy_iff storage).mpr ⟨_, copied⟩

/-- Exact-address reference self assignment precedes shape dispatch and raw
header decoding. Every other constructor retains the ordered recursive tree. -/
def StorageCopyRule (registry : Registry) : Nat → CopyRelation
  | 0, _, _, _, _, _, _ => False
  | fuel+1, budget, before, source, target, events, after =>
      Access.validate before source = .ok () ∧ Access.validate before target = .ok () ∧
      ∃ sourceOwner targetOwner,
        source.reference.region = .storage sourceOwner ∧ target.reference.region = .storage targetOwner ∧
        ((isReference source.type = true ∧ sourceOwner = targetOwner ∧
            source.reference.address = target.reference.address ∧ events = [] ∧ after = (before, budget)) ∨
         (¬(isReference source.type = true ∧ sourceOwner = targetOwner ∧
            source.reference.address = target.reference.address) ∧
          StorageBodyRule (StorageCopyRule registry fuel) registry fuel budget source target before events after))

theorem copyStorage_iff (registry : Registry) (fuel : Nat) :
    ∀ budget before source target after, copyStorage registry fuel budget before source target = .ok after ↔
      ∃ events, StorageCopyRule registry fuel budget before source target events after := by
  induction fuel with
  | zero => intro budget before source target after; simp [copyStorage, StorageCopyRule]
  | succ fuel ih =>
      intro budget before source target after
      rw [copyStorage]
      constructor
      · intro finished
        cases sourceChecked : Access.validate before source with
        | error failure => simp [sourceChecked] at finished
        | ok checkedValue =>
            cases checkedValue
            simp only [sourceChecked, Bind.bind, Except.bind] at finished
            cases targetChecked : Access.validate before target with
            | error failure => simp [targetChecked] at finished
            | ok checkedValue =>
                cases checkedValue
                simp only [targetChecked] at finished
                cases sourceRegion : source.reference.region with
                | transient owner | memory invocation | calldata invocation => simp [sourceRegion] at finished
                | storage sourceOwner =>
                    simp only [sourceRegion] at finished
                    cases targetRegion : target.reference.region with
                    | transient owner | memory invocation | calldata invocation => simp [targetRegion] at finished
                    | storage targetOwner =>
                        simp only [targetRegion] at finished
                        split at finished
                        · rename_i self
                          have selfCopy : isReference source.type = true ∧ sourceOwner = targetOwner ∧
                              source.reference.address = target.reference.address := by simpa [Bool.and_eq_true, and_assoc] using self
                          simp only [Pure.pure, Except.pure] at finished
                          cases finished
                          exact ⟨[], sourceChecked, targetChecked, sourceOwner, targetOwner,
                            sourceRegion, targetRegion, Or.inl ⟨selfCopy.1, selfCopy.2.1, selfCopy.2.2, rfl, rfl⟩⟩
                        · rename_i notSelf
                          have apart : ¬(isReference source.type = true ∧ sourceOwner = targetOwner ∧
                              source.reference.address = target.reference.address) := by simpa [Bool.and_eq_true, and_assoc] using notSelf
                          obtain ⟨events, copied⟩ := (storageCopyBody_iff ih (Or.inl ⟨_, targetRegion⟩)).mp finished
                          exact ⟨events, sourceChecked, targetChecked, sourceOwner, targetOwner,
                            sourceRegion, targetRegion, Or.inr ⟨apart, copied⟩⟩
      · rintro ⟨events, sourceChecked, targetChecked, sourceOwner, targetOwner, sourceRegion, targetRegion, copied⟩
        simp only [sourceChecked, targetChecked, Bind.bind, Except.bind, sourceRegion, targetRegion]
        rcases copied with ⟨reference, owner, address, rfl, rfl⟩ | ⟨apart, copied⟩
        · simp [reference, owner, address]
        · have notSelf : ¬(isReference source.type && sourceOwner == targetOwner &&
              source.reference.address == target.reference.address) = true := by simpa [Bool.and_eq_true, and_assoc] using apart
          rw [if_neg notSelf]
          exact (storageCopyBody_iff ih (Or.inl ⟨_, targetRegion⟩)).mpr ⟨events, copied⟩

theorem StorageArrayRule.trace
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      StorageTrace heap events after.1)
    (copied : StorageArrayRule child registry fuel budget source target a b before events after) :
    StorageTrace before events after.1 := by
  cases copied with
  | scalars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ resizeTrace _ _ _ _ copied =>
      exact resizeTrace.append copied.trace
  | references _ _ _ _ _ _ _ _ _ _ _ resizeTrace _ _ copied =>
      apply resizeTrace.append
      exact copied.trace Prod.fst (by
        intro _ _ _ _ step
        cases step with | step _ _ _ _ _ _ copied => exact law _ _ _ _ _ _ copied)

theorem StorageStructRule.trace
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      StorageTrace heap events after.1)
    (copied : StorageStructRule child registry fuel budget source target a b before events after) :
    StorageTrace before events after.1 := by
  cases copied with
  | step _ _ _ _ _ _ _ copied =>
      exact copied.trace Prod.fst (by
        intro _ _ _ _ step
        cases step with | step _ _ _ _ _ _ copied => exact law _ _ _ _ _ _ copied)

theorem StorageBodyRule.trace
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      StorageTrace heap events after.1)
    (copied : StorageBodyRule child registry fuel budget source target before events after) :
    StorageTrace before events after.1 := by
  cases copied with
  | array _ copied => exact copied.trace law
  | «structure» _ copied => exact copied.trace law
  | bytes _ copied => exact copied.trace
  | scalar _ copied => exact copied.trace

theorem StorageCopyRule.trace (registry : Registry) (fuel : Nat) :
    ∀ budget before source target events after,
      StorageCopyRule registry fuel budget before source target events after →
      StorageTrace before events after.1 := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ impossible; exact False.elim impossible
  | succ fuel ih =>
      intro budget before source target events after copied
      rcases copied with ⟨_, _, _, _, _, _, self | ⟨_, copied⟩⟩
      · rcases self with ⟨_, _, _, rfl, rfl⟩; exact .nil _
      · exact copied.trace ih

theorem copyStorage_trace (copied : copyStorage registry fuel budget before source target = .ok after) :
    ∃ events, StorageCopyRule registry fuel budget before source target events after ∧
      StorageTrace before events after.1 := by
  obtain ⟨events, rule⟩ := (copyStorage_iff registry fuel _ _ _ _ _).mp copied
  exact ⟨events, rule, StorageCopyRule.trace registry fuel _ _ _ _ _ _ rule⟩

theorem copyStorage_frame (copied : copyStorage registry fuel budget before source target = .ok after) :
    StorageFrame before after.1 := by
  obtain ⟨_, _, trace⟩ := copyStorage_trace copied
  exact trace.frame

/-- A produced physical packet survives exactly when subsequent stores are
separate from its account/slot. Logical path inequality and hash injectivity are
not premises. The prefix may overlap either source or target arbitrarily. -/
theorem packet_after_separate_suffix {owner : BitVec 160}
    (trace : StorageTrace before ((initial ++ [.store (.storage owner) slot word]) ++ final) after)
    (separate : PersistentSeparate final (owner.setWidth 256) slot) :
    Slot.read after (.storage owner) slot = .ok word := by
  simp only [Slot.read]
  rw [trace.persistent, List.foldl_append, persistent_untouched separate]
  simp [List.foldl_append, StorageEvent.persistent]

/-- A raw scalar representation uses the physical word and the actual scalar
codec. Dirty neighbors are unconstrained; unrepresentable dirty scalar fields
have no typed representation, rather than an invented panic value. -/
def StorageScalarPacket (heap : Heap) (place : Place) (value : place.type.Value) : Prop :=
  ∃ bytes word, storageBytes place.type = some bytes ∧ place.reference.byte.val + bytes ≤ 32 ∧
    Slot.read heap place.reference.region place.reference.address = .ok word ∧
    decodeStorage place.type ((Packed.extract (8*bytes) (8*place.reference.byte.val) word).setWidth 256) = .ok value

theorem StorageScalarPacket.read {owner : BitVec 160} (packet : StorageScalarPacket heap place value)
    (storage : place.reference.region = .storage owner) : readScalar heap place = .ok value := by
  rcases packet with ⟨bytes, word, sized, fits, loaded, decoded⟩
  simp only [readScalar, sized, Bind.bind, Except.bind, storage, Nat.not_lt.mpr fits, ↓reduceIte]
  rw [← storage] at *
  simp only [loaded]
  exact decoded

theorem scalar_packet_after_separate_suffix {owner : BitVec 160} {place : Place} {value : place.type.Value}
    (region : place.reference.region = .storage owner)
    (sized : storageBytes place.type = some bytes)
    (fits : place.reference.byte.val+bytes ≤ 32)
    (decoded : decodeStorage place.type ((Packed.extract (8*bytes)
      (8*place.reference.byte.val) word).setWidth 256) = .ok value)
    (trace : StorageTrace before ((initial ++ [.store (.storage owner) place.reference.address word]) ++ final) after)
    (separate : PersistentSeparate final (owner.setWidth 256) place.reference.address) :
    StorageScalarPacket after place value ∧ readScalar after place = .ok value := by
  have loaded := packet_after_separate_suffix trace separate
  have packet : StorageScalarPacket after place value :=
    ⟨bytes, word, sized, fits, by simpa only [region] using loaded, decoded⟩
  exact ⟨packet, packet.read region⟩

end Solidity.Aggregates.Copy
