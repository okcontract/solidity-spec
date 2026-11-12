/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.StorageCopyTraversal

/-! Memory/calldata sources are decoded at the native word/member boundaries.
These derivations retain those reads after preceding destination effects; they
do not replace the source with an eager snapshot. -/
namespace Solidity.Aggregates.Copy
open Core Static
open Contract.Interaction (Word)

private theorem immutable_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem immutable_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] immutable_map_error immutable_map_ok Bind.bind Except.bind Pure.pure Except.pure

inductive SelectedChild (child : CopyRelation)
    (sourcePosition targetPosition : Heap → Nat → Result Place) :
    Heap × Nat → Nat → List StorageEvent → Heap × Nat → Prop where
  | step (before : Heap × Nat) (index : Nat) (source target : Place)
      (events : List StorageEvent) (after : Heap × Nat)
      (selectedSource : sourcePosition before.1 index = .ok source)
      (selectedTarget : targetPosition before.1 index = .ok target)
      (copied : child before.2 before.1 source target events after) :
      SelectedChild child sourcePosition targetPosition before index events after

theorem selectedChild_iff {copy : StorageCopyCall} {child : CopyRelation}
    {sourcePosition targetPosition : Heap → Nat → Result Place} {before after : Heap × Nat} {index : Nat}
    (law : ∀ budget heap source target after,
      copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after) :
    (do
      let a ← sourcePosition before.1 index
      let b ← targetPosition before.1 index
      copy before.2 before.1 a b) = .ok after ↔
    ∃ events, SelectedChild child sourcePosition targetPosition before index events after := by
  constructor
  · intro finished
    cases a : sourcePosition before.1 index with
    | error failure => simp [a] at finished
    | ok source =>
        simp only [a, Bind.bind, Except.bind] at finished
        cases b : targetPosition before.1 index with
        | error failure => simp [b] at finished
        | ok target =>
            simp only [b] at finished
            obtain ⟨events, copied⟩ := (law _ _ _ _ _).mp finished
            exact ⟨events, .step before index source target events after a b copied⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | step _ _ _ _ a b copied =>
        simp only [a, b, Bind.bind, Except.bind]
        exact (law _ _ _ _ _).mpr ⟨_, copied⟩

theorem SelectedChild.trace
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      StorageTrace heap events after.1)
    (copied : SelectedChild child sourcePosition targetPosition before index events after) :
    StorageTrace before.1 events after.1 := by
  cases copied with | step _ _ _ _ _ _ copied => exact law _ _ _ _ _ _ copied

inductive ImmutableWord (registry : Registry) (fuel : Nat) (source : Place)
    (type : SType) (bytes count : Nat) (data : Reference) :
    Heap → Nat → List StorageEvent → Heap → Prop where
  | step (before after : Heap) (index : Nat) (word : Word)
      (read : sourceWord registry fuel before source type bytes (index*(32/bytes))
        (min (32/bytes) (count-index*(32/bytes))) = .ok word)
      (stored : Slot.write before data.region (data.address+BitVec.ofNat 256 index) word = .ok after) :
      ImmutableWord registry fuel source type bytes count data before index
        [.store data.region (data.address+BitVec.ofNat 256 index) word] after

theorem ImmutableWord.trace
    (copied : ImmutableWord registry fuel source type bytes count data before index events after) :
    StorageTrace before events after := by
  cases copied with | step _ _ _ _ stored => exact .write stored

theorem immutableWord_iff :
    (do
      let word ← sourceWord registry fuel before source type bytes (index*(32/bytes))
        (min (32/bytes) (count-index*(32/bytes)))
      Slot.write before data.region (data.address+BitVec.ofNat 256 index) word) = .ok after ↔
    ∃ events, ImmutableWord registry fuel source type bytes count data before index events after := by
  constructor
  · intro finished
    cases read : sourceWord registry fuel before source type bytes (index*(32/bytes))
        (min (32/bytes) (count-index*(32/bytes))) with
    | error failure => simp [read] at finished
    | ok word =>
        simp only [read, Bind.bind, Except.bind] at finished
        exact ⟨_, .step before after index word read finished⟩
  · rintro ⟨_, copied⟩
    cases copied with | step _ _ _ read stored => simp only [read, Bind.bind, Except.bind]; exact stored

inductive ImmutableScalarsRule (registry : Registry) (fuel budget : Nat)
    (source target : Place) (type : SType) (bytes count : Nat) :
    Heap → List StorageEvent → Heap × Nat → Prop where
  | step (before after : Heap) (available : Nat) (data : Reference) (events : List StorageEvent)
      (width : 0 < bytes ∧ bytes ≤ 32)
      (reserved : reserve budget (count+(count+32/bytes-1)/(32/bytes)) = .ok available)
      (position : Access.arrayData target = .ok data)
      (copied : CopyFold (ImmutableWord registry fuel source type bytes count data) before
        (List.range ((count+32/bytes-1)/(32/bytes))) events after) :
      ImmutableScalarsRule registry fuel budget source target type bytes count before events (after, available)

theorem ImmutableScalarsRule.trace
    (copied : ImmutableScalarsRule registry fuel budget source target type bytes count before events after) :
    StorageTrace before events after.1 := by
  cases copied with
  | step _ _ _ _ _ _ _ copied => exact copied.trace id (fun _ _ _ _ word => word.trace)

theorem copyImmutableScalars_iff :
    copyImmutableScalars registry fuel budget before source target type bytes count = .ok after ↔
    ∃ events, ImmutableScalarsRule registry fuel budget source target type bytes count before events after := by
  unfold copyImmutableScalars
  constructor
  · intro finished
    split at finished
    · cases finished
    · rename_i width
      have widths : 0 < bytes ∧ bytes ≤ 32 := by omega
      cases reserved : reserve budget (count+(count+32/bytes-1)/(32/bytes)) with
      | error failure => simp [reserved] at finished
      | ok available =>
          simp only [reserved, Bind.bind, Except.bind] at finished
          cases position : Access.arrayData target with
          | error failure => simp [position] at finished
          | ok data =>
              simp only [position] at finished
              cases written : (List.range ((count+32/bytes-1)/(32/bytes))).foldlM
                  (fun heap index => do
                    let word ← sourceWord registry fuel heap source type bytes (index*(32/bytes))
                      (min (32/bytes) (count-index*(32/bytes)))
                    Slot.write heap data.region (data.address+BitVec.ofNat 256 index) word) before with
              | error failure =>
                  have body := written
                  simp only [Bind.bind, Except.bind] at body
                  simp [body] at finished
              | ok next =>
                  have body := written
                  simp only [Bind.bind, Except.bind] at body
                  simp only [body, Pure.pure, Except.pure] at finished
                  cases finished
                  obtain ⟨events, copied⟩ := (CopyFold.iff_foldlM _ (fun _ _ _ => immutableWord_iff) _ _ _).mp written
                  exact ⟨events, .step before next available data events widths reserved position copied⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | step next available data _ width reserved position copied =>
        have body : (List.range ((count+32/bytes-1)/(32/bytes))).foldlM
            (fun heap index => do
              let word ← sourceWord registry fuel heap source type bytes (index*(32/bytes))
                (min (32/bytes) (count-index*(32/bytes)))
              Slot.write heap data.region (data.address+BitVec.ofNat 256 index) word) before = .ok next :=
          (CopyFold.iff_foldlM _ (fun _ _ _ => immutableWord_iff) _ _ _).mpr ⟨_, copied⟩
        simp only [Bind.bind, Except.bind] at body
        simp only [if_neg (by omega : ¬(bytes = 0 ∨ 32 < bytes)), Bind.bind, Except.bind,
          reserved, position, body, Pure.pure, Except.pure]

inductive ImmutableBytesRule (registry : Registry) (fuel budget : Nat) (source target : Place) :
    Heap → List StorageEvent → Heap × Nat → Prop where
  | step (before : Heap) (count : Nat) (events : List StorageEvent) (after : Heap × Nat)
      (length : Access.length before source = .ok count)
      (copied : BytesTransfer (.immutable registry fuel source) target.reference count budget before events after) :
      ImmutableBytesRule registry fuel budget source target before events after

theorem ImmutableBytesRule.trace
    (copied : ImmutableBytesRule registry fuel budget source target before events after) : StorageTrace before events after.1 := by
  cases copied with | step _ _ _ _ copied => exact copied.trace

theorem copyImmutableBytes_iff : copyImmutableBytes registry fuel budget before source target = .ok after ↔
    ∃ events, ImmutableBytesRule registry fuel budget source target before events after := by
  unfold copyImmutableBytes
  constructor
  · intro finished
    cases length : Access.length before source with
    | error failure => simp [length] at finished
    | ok count =>
        simp only [length, Bind.bind, Except.bind] at finished
        obtain ⟨events, copied⟩ := (writeBytesFrom_iff (source := ByteSource.immutable registry fuel source)).mp finished
        exact ⟨events, .step before count events after length copied⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | step _ _ _ length copied =>
        simp only [length, Bind.bind, Except.bind]
        exact writeBytesFrom_iff.mpr ⟨_, copied⟩

abbrev ImmutableArrayChild (child : CopyRelation) (registry : Registry) (fuel : Nat)
    (source target : Place) (element : SType) :=
  SelectedChild child (fun heap index => Access.index registry fuel heap source index)
    (fun _ index => storageElement registry fuel target element index)

theorem immutableArrayChild_iff {copy : StorageCopyCall} {child : CopyRelation}
    (law : ∀ budget heap source target after,
      copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after) :
    (do
      let a ← Access.index registry fuel before.1 source index
      let b ← storageElement registry fuel target element index
      copy before.2 before.1 a b) = .ok after ↔
    ∃ events, ImmutableArrayChild child registry fuel source target element before index events after :=
  selectedChild_iff (sourcePosition := fun heap index => Access.index registry fuel heap source index)
    (targetPosition := fun _ index => storageElement registry fuel target element index)
    (before := before) (after := after) (index := index) law

inductive ImmutableArrayRule (child : CopyRelation) (registry : Registry) (fuel budget : Nat)
    (source target : Place) (element : SType) : Heap → List StorageEvent → Heap × Nat → Prop where
  | scalars (before middle : Heap) (count available remaining bytes : Nat)
      (resizeEvents copyEvents : List StorageEvent) (after : Heap × Nat)
      (length : Access.length before source = .ok count)
      (bounded : ¬((storageBytes element).isSome = true ∧ MemoryOps.maximumMemory < count))
      (reserved : reserve budget count = .ok available)
      (resized : StorageArrays.resize registry fuel available before target count = .ok (middle, remaining))
      (resizeTrace : StorageTrace before resizeEvents middle)
      (sized : storageBytes element = some bytes)
      (copied : ImmutableScalarsRule registry fuel remaining source target element bytes count middle copyEvents after) :
      ImmutableArrayRule child registry fuel budget source target element before (resizeEvents ++ copyEvents) after
  | references (before middle : Heap) (count available remaining : Nat)
      (resizeEvents copyEvents : List StorageEvent) (after : Heap × Nat)
      (length : Access.length before source = .ok count)
      (bounded : ¬((storageBytes element).isSome = true ∧ MemoryOps.maximumMemory < count))
      (reserved : reserve budget count = .ok available)
      (resized : StorageArrays.resize registry fuel available before target count = .ok (middle, remaining))
      (resizeTrace : StorageTrace before resizeEvents middle)
      (sized : storageBytes element = none)
      (copied : CopyFold (ImmutableArrayChild child registry fuel source target element)
        (middle, remaining) (List.range count) copyEvents after) :
      ImmutableArrayRule child registry fuel budget source target element before (resizeEvents ++ copyEvents) after

theorem immutableArrayCopy_iff {copy : StorageCopyCall} {child : CopyRelation}
    (law : ∀ budget heap source target after,
      copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after) :
    immutableArrayCopy copy registry fuel budget before source target element = .ok after ↔
    ∃ events, ImmutableArrayRule child registry fuel budget source target element before events after := by
  unfold immutableArrayCopy
  constructor
  · intro finished
    cases length : Access.length before source with
    | error failure => simp [length] at finished
    | ok count =>
        simp only [length, Bind.bind, Except.bind] at finished
        split at finished
        · cases finished
        · rename_i bounded
          have bounds : ¬((storageBytes element).isSome = true ∧ MemoryOps.maximumMemory < count) := by simpa using bounded
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
                  cases sized : storageBytes element with
                  | some bytes =>
                      simp only [sized] at finished
                      obtain ⟨events, copied⟩ := copyImmutableScalars_iff.mp finished
                      exact ⟨_, .scalars before middle count available remaining bytes resizeEvents events after
                        length bounds reserved resized resizeTrace sized copied⟩
                  | none =>
                      simp only [sized, Pure.pure, Except.pure] at finished
                      obtain ⟨events, copied⟩ := (CopyFold.iff_foldlM _
                        (fun _ _ _ => immutableArrayChild_iff law) _ _ _).mp finished
                      exact ⟨_, .references before middle count available remaining resizeEvents events after
                        length bounds reserved resized resizeTrace sized copied⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | scalars _ count _ _ _ _ _ _ length bounded reserved resized _ sized copied =>
        have chosen : ¬((storageBytes element).isSome && decide (MemoryOps.maximumMemory < count)) = true := by simpa using bounded
        simp only [length, Bind.bind, Except.bind]
        rw [if_neg chosen]
        simp only [Pure.pure, Except.pure, reserved, resized, sized]
        exact copyImmutableScalars_iff.mpr ⟨_, copied⟩
    | references _ count _ _ _ _ _ length bounded reserved resized _ sized copied =>
        have chosen : ¬((storageBytes element).isSome && decide (MemoryOps.maximumMemory < count)) = true := by simpa using bounded
        simp only [length, Bind.bind, Except.bind]
        rw [if_neg chosen]
        simp only [Pure.pure, Except.pure, reserved, resized, sized]
        exact (CopyFold.iff_foldlM _ (fun _ _ _ => immutableArrayChild_iff law) _ _ _).mpr ⟨_, copied⟩

inductive ImmutableStructChild (child : CopyRelation) (registry : Registry) (fuel : Nat) (source target : Place) :
    Heap × Nat → Nat → List StorageEvent → Heap × Nat → Prop where
  | step (before : Heap × Nat) (index : Nat) (sourceChild targetChild : Place)
      (events : List StorageEvent) (after : Heap × Nat)
      (sourcePosition : Access.field registry fuel before.1 source index = .ok sourceChild)
      (targetPosition : Access.field registry fuel before.1 (StorageArrays.captured target) index = .ok targetChild)
      (copied : child before.2 before.1 sourceChild
        (StorageArrays.captured targetChild) events after) :
      ImmutableStructChild child registry fuel source target before index events after

theorem immutableStructChild_iff {copy : StorageCopyCall} {child : CopyRelation}
    (law : ∀ budget heap source target after,
      copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after) :
    (do
      let a ← Access.field registry fuel before.1 source index
      let b ← Access.field registry fuel before.1 (StorageArrays.captured target) index
      copy before.2 before.1 a (StorageArrays.captured b)) = .ok after ↔
    ∃ events, ImmutableStructChild child registry fuel source target before index events after := by
  constructor
  · intro finished
    cases a : Access.field registry fuel before.1 source index with
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

inductive ImmutableStructRule (child : CopyRelation) (registry : Registry) (fuel budget : Nat)
    (source target : Place) (identity targetIdentity : Nat) :
    Heap → List StorageEvent → Heap × Nat → Prop where
  | step (before : Heap) (fields : List (String × SType)) (available : Nat)
      (events : List StorageEvent) (after : Heap × Nat)
      (same : identity = targetIdentity)
      (metadata : registry.structFields identity = some fields)
      (reserved : reserve budget fields.length = .ok available)
      (copied : CopyFold (ImmutableStructChild child registry fuel source target)
        (before, available) (List.range fields.length) events after) :
      ImmutableStructRule child registry fuel budget source target identity targetIdentity before events after

theorem immutableStructCopy_iff {copy : StorageCopyCall} {child : CopyRelation}
    (law : ∀ budget heap source target after,
      copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after) :
    immutableStructCopy copy registry fuel budget before source target identity targetIdentity = .ok after ↔
    ∃ events, ImmutableStructRule child registry fuel budget source target identity targetIdentity before events after := by
  unfold immutableStructCopy
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
              obtain ⟨events, copied⟩ := (CopyFold.iff_foldlM _ (fun _ _ _ => immutableStructChild_iff law) _ _ _).mp finished
              exact ⟨events, .step before fields available events after same metadata reserved copied⟩
    · have chosen : (identity != targetIdentity) = true := by simp [same]
      simp [chosen] at finished
  · rintro ⟨_, copied⟩
    cases copied with
    | step fields _ _ _ same metadata reserved copied =>
        have chosen : (identity != targetIdentity) = false := by simp [same]
        simp only [chosen, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure, metadata, reserved]
        exact (CopyFold.iff_foldlM _ (fun _ _ _ => immutableStructChild_iff law) _ _ _).mpr ⟨_, copied⟩

inductive ImmutableBodyRule (child : CopyRelation) (registry : Registry) (fuel budget : Nat)
    (source target : Place) : Heap → List StorageEvent → Heap × Nat → Prop where
  | array (shape : immutableCopyShape source.type target.type = .array a b)
      (copied : ImmutableArrayRule child registry fuel budget source target b before events after) :
      ImmutableBodyRule child registry fuel budget source target before events after
  | structure (shape : immutableCopyShape source.type target.type = .structure a b)
      (copied : ImmutableStructRule child registry fuel budget source target a b before events after) :
      ImmutableBodyRule child registry fuel budget source target before events after
  | bytes (shape : immutableCopyShape source.type target.type = .bytes)
      (copied : ImmutableBytesRule registry fuel budget source target before events after) :
      ImmutableBodyRule child registry fuel budget source target before events after
  | scalar (shape : immutableCopyShape source.type target.type = .scalar)
      (copied : ScalarCopyRule budget source target before events after) :
      ImmutableBodyRule child registry fuel budget source target before events after

theorem immutableCopyBody_iff {copy : StorageCopyCall} {child : CopyRelation}
    (law : ∀ budget heap source target after,
      copy budget heap source target = .ok after ↔ ∃ events, child budget heap source target events after)
    (storage : StorageRegion target.reference.region) :
    immutableCopyBody copy registry fuel budget before source target = .ok after ↔
    ∃ events, ImmutableBodyRule child registry fuel budget source target before events after := by
  unfold immutableCopyBody
  constructor
  · intro finished
    cases shape : immutableCopyShape source.type target.type with
    | array a b =>
        simp only [shape] at finished
        obtain ⟨events, copied⟩ := (immutableArrayCopy_iff law).mp finished
        exact ⟨events, .array shape copied⟩
    | «structure» a b =>
        simp only [shape] at finished
        obtain ⟨events, copied⟩ := (immutableStructCopy_iff law).mp finished
        exact ⟨events, .structure shape copied⟩
    | bytes =>
        simp only [shape] at finished
        obtain ⟨events, copied⟩ := copyImmutableBytes_iff.mp finished
        exact ⟨events, .bytes shape copied⟩
    | scalar =>
        simp only [shape] at finished
        obtain ⟨events, copied⟩ := (scalarCopy_iff storage).mp finished
        exact ⟨events, .scalar shape copied⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | array shape copied => rw [shape]; exact (immutableArrayCopy_iff law).mpr ⟨_, copied⟩
    | «structure» shape copied => rw [shape]; exact (immutableStructCopy_iff law).mpr ⟨_, copied⟩
    | bytes shape copied => rw [shape]; exact copyImmutableBytes_iff.mpr ⟨_, copied⟩
    | scalar shape copied => rw [shape]; exact (scalarCopy_iff storage).mpr ⟨_, copied⟩

theorem ImmutableArrayRule.trace
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      StorageTrace heap events after.1)
    (copied : ImmutableArrayRule child registry fuel budget source target element before events after) :
    StorageTrace before events after.1 := by
  cases copied with
  | scalars _ _ _ _ _ _ _ _ _ _ _ _ resizeTrace _ copied => exact resizeTrace.append copied.trace
  | references _ _ _ _ _ _ _ _ _ _ _ resizeTrace _ copied =>
      exact resizeTrace.append (copied.trace Prod.fst (fun _ _ _ _ item => item.trace law))

theorem ImmutableStructRule.trace
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      StorageTrace heap events after.1)
    (copied : ImmutableStructRule child registry fuel budget source target a b before events after) :
    StorageTrace before events after.1 := by
  cases copied with
  | step _ _ _ _ _ _ _ copied =>
      exact copied.trace Prod.fst (by
        intro _ _ _ _ step
        cases step with | step _ _ _ _ _ _ copied => exact law _ _ _ _ _ _ copied)

theorem ImmutableBodyRule.trace
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      StorageTrace heap events after.1)
    (copied : ImmutableBodyRule child registry fuel budget source target before events after) :
    StorageTrace before events after.1 := by
  cases copied with
  | array _ copied => exact copied.trace law
  | «structure» _ copied => exact copied.trace law
  | bytes _ copied => exact copied.trace
  | scalar _ copied => exact copied.trace


/-- The source region selects the native storage stream or the immutable
member reader. Neither branch snapshots ahead of destination effects. -/
def CopyToStorageRule (registry : Registry) : Nat → CopyRelation
  | 0, _, _, _, _, _, _ => False
  | fuel+1, budget, before, source, target, events, after =>
      Access.validate before source = .ok () ∧ Access.validate before target = .ok () ∧
      ∃ targetOwner, target.reference.region = .storage targetOwner ∧
        ((∃ sourceOwner, source.reference.region = .storage sourceOwner ∧
            StorageCopyRule registry (fuel+1) budget before source target events after) ∨
         ((∀ sourceOwner, source.reference.region ≠ .storage sourceOwner) ∧
          ImmutableBodyRule (CopyToStorageRule registry fuel) registry fuel budget source target before events after))

theorem copyToStorage_iff (registry : Registry) (fuel : Nat) :
    ∀ budget before source target after, copyToStorage registry fuel budget before source target = .ok after ↔
      ∃ events, CopyToStorageRule registry fuel budget before source target events after := by
  induction fuel with
  | zero => intro budget before source target after; simp [copyToStorage, CopyToStorageRule]
  | succ fuel ih =>
      intro budget before source target after
      rw [copyToStorage]
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
                cases targetRegion : target.reference.region with
                | transient owner | memory invocation | calldata invocation => simp [targetRegion] at finished
                | storage targetOwner =>
                    simp only [targetRegion] at finished
                    cases sourceRegion : source.reference.region with
                    | storage sourceOwner =>
                        simp only [sourceRegion] at finished
                        obtain ⟨events, copied⟩ := (copyStorage_iff registry (fuel+1) _ _ _ _ _).mp finished
                        exact ⟨events, sourceChecked, targetChecked, targetOwner, targetRegion,
                          Or.inl ⟨sourceOwner, sourceRegion, copied⟩⟩
                    | transient owner | memory invocation | calldata invocation =>
                        simp only [sourceRegion] at finished
                        obtain ⟨events, copied⟩ := (immutableCopyBody_iff ih (Or.inl ⟨_, targetRegion⟩)).mp finished
                        exact ⟨events, sourceChecked, targetChecked, targetOwner, targetRegion,
                          Or.inr ⟨by intro other impossible; simp [sourceRegion] at impossible, copied⟩⟩
      · rintro ⟨events, sourceChecked, targetChecked, targetOwner, targetRegion, copied⟩
        simp only [sourceChecked, targetChecked, Bind.bind, Except.bind, targetRegion]
        rcases copied with ⟨sourceOwner, sourceRegion, copied⟩ | ⟨nonstorage, copied⟩
        · simp only [sourceRegion]
          exact (copyStorage_iff registry (fuel+1) _ _ _ _ _).mpr ⟨events, copied⟩
        · cases sourceRegion : source.reference.region with
          | storage sourceOwner => exact False.elim (nonstorage sourceOwner sourceRegion)
          | transient owner | memory invocation | calldata invocation =>
              exact (immutableCopyBody_iff ih (Or.inl ⟨_, targetRegion⟩)).mpr ⟨events, copied⟩

theorem CopyToStorageRule.trace (registry : Registry) (fuel : Nat) :
    ∀ budget before source target events after,
      CopyToStorageRule registry fuel budget before source target events after →
      StorageTrace before events after.1 := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ impossible; exact False.elim impossible
  | succ fuel ih =>
      intro budget before source target events after copied
      rcases copied with ⟨_, _, _, _, ⟨_, _, copied⟩ | ⟨_, copied⟩⟩
      · exact StorageCopyRule.trace registry (fuel+1) _ _ _ _ _ _ copied
      · exact copied.trace ih

theorem copyToStorage_trace (copied : copyToStorage registry fuel budget before source target = .ok after) :
    ∃ events, CopyToStorageRule registry fuel budget before source target events after ∧
      StorageTrace before events after.1 := by
  obtain ⟨events, rule⟩ := (copyToStorage_iff registry fuel _ _ _ _ _).mp copied
  exact ⟨events, rule, CopyToStorageRule.trace registry fuel _ _ _ _ _ _ rule⟩

theorem copyToStorage_frame (copied : copyToStorage registry fuel budget before source target = .ok after) :
    StorageFrame before after.1 := by
  obtain ⟨_, _, trace⟩ := copyToStorage_trace copied
  exact trace.frame

end Solidity.Aggregates.Copy
