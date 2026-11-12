/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.StorageMutationRepresentation

/-! Aggregate erasure has zero-valued physical stores, not merely an
unconstrained execution trace. Every actually touched cell becomes zero even
when logical paths collide. Mapping payloads are not enumerated; an observed
mapping cell is framed precisely when no physical erase store aliases it. -/
namespace Solidity.Aggregates.Deletion
open Core Static StorageArrays
open Contract.Interaction (Word)

def ZeroStores (events : List StorageEvent) : Prop :=
  ∀ region slot value, .store region slot value ∈ events → value = 0

def ZeroTrace (before after : Heap) : Prop :=
  ∃ events, StorageTrace before events after ∧ ZeroStores events

theorem ZeroTrace.refl (heap : Heap) : ZeroTrace heap heap :=
  ⟨[], .nil heap, by intro region slot value member; cases member⟩

theorem ZeroTrace.trans (first : ZeroTrace before middle) (last : ZeroTrace middle after) :
    ZeroTrace before after := by
  rcases first with ⟨initial, firstTrace, zeroPrefix⟩
  rcases last with ⟨final, suffix, zeroSuffix⟩
  refine ⟨initial ++ final, firstTrace.append suffix, ?_⟩
  intro region slot value member
  rcases List.mem_append.mp member with left | right
  · exact zeroPrefix region slot value left
  · exact zeroSuffix region slot value right

theorem ZeroTrace.load (read : Slot.read heap region slot = .ok value) : ZeroTrace heap heap := by
  refine ⟨[.load region slot value], .read read, ?_⟩
  intro region slot value member
  simp at member

theorem ZeroTrace.store (written : Slot.write before region slot 0 = .ok after) : ZeroTrace before after := by
  refine ⟨[.store region slot 0], .write written, ?_⟩
  intro selected address value member
  have same := List.mem_singleton.mp member
  cases same
  rfl

theorem ZeroTrace.journal (heap : Heap) (region : Region) (slot : Word)
    (oldLength newLength : Nat) (bytes : Bool) :
    ZeroTrace heap (heap.journalResize region slot oldLength newLength bytes) := by
  refine ⟨[.resize region slot oldLength newLength bytes], .journal heap _ _ _ _ _, ?_⟩
  intro selected address value member
  simp at member

theorem fold_zero_trace (project : State → Heap) (step : State → α → Result State)
    (safe : ∀ before item after, step before item = .ok after → ZeroTrace (project before) (project after))
    (items : List α) (written : items.foldlM step before = .ok after) :
    ZeroTrace (project before) (project after) := by
  induction items generalizing before with
  | nil => cases written; exact .refl _
  | cons item rest ih =>
      rw [List.foldlM_cons] at written
      cases first : step before item with
      | error failure => simp [first, Bind.bind, Except.bind] at written
      | ok middle =>
          simp only [first, Bind.bind, Except.bind] at written
          exact (safe before item middle first).trans (ih written)

/-- Aggregate references have no scalar width; a full-width scalar also owns
its entire physical word on every successful write. Unsupported scalar families
cannot manufacture a successful erase merely by satisfying this predicate. -/
def WholeCell (type : SType) : Prop := (storageBytes type).getD 32 = 32

theorem storageBytes_getD_bound (type : SType) : (storageBytes type).getD 32 ≤ 32 := by
  cases sized : storageBytes type with
  | none => simp
  | some bytes => exact (storageBytes_bound type bytes sized).2

theorem storageBytes_atLocation (type : SType) (location : Location) (pointer : Bool) :
    storageBytes (atLocation type location pointer) = storageBytes type := by cases type <;> rfl

theorem reference_whole (reference : isReference type = true) : WholeCell type := by
  cases type <;> simp_all [isReference, referenceLocation, WholeCell, storageBytes]

theorem encodeStorage_default (default : defaultScalar type = some value) :
    encodeStorage type value = .ok 0 := by
  cases type <;> simp only [defaultScalar] at default
  all_goals try (cases default <;> simp only [encodeStorage] <;> simp)
  case valueType identity base =>
    cases base with
    | payableAddress => cases default; rfl
    | scalar type => cases type <;> cases default <;> simp [encodeStorage, encodeCoreStorage, Elementary.core]
  case function visibility mutability parameters returns =>
    cases visibility with
    | internal => cases default; rfl
    | external => cases default; simp [encodeStorage, encodeExternal]

private theorem mutation_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem mutation_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] mutation_map_error mutation_map_ok Bind.bind Except.bind Pure.pure Except.pure

theorem scalarZero_zero (whole : WholeCell place.type) (storage : StorageRegion place.reference.region)
    (written : scalarZero heap place = .ok after) : ZeroTrace heap after := by
  unfold scalarZero at written
  cases default : defaultScalar place.type with
  | none => simp [default] at written
  | some value =>
      simp only [default] at written
      have encoded := encodeStorage_default default
      rcases storage with ⟨owner, region⟩ | ⟨owner, region⟩
      all_goals
        unfold writeScalar at written
        cases sized : storageBytes place.type with
        | none => simp [sized] at written
        | some bytes =>
            have width : bytes = 32 := by simpa only [WholeCell, sized, Option.getD_some] using whole
            subst bytes
            simp only [sized, region, Bind.bind, Except.bind] at written
            split at written
            · cases written
            · rename_i fits
              have aligned : place.reference.byte.val = 0 := by omega
              cases loaded : Slot.read heap place.reference.region place.reference.address with
              | error failure => simp [region, Slot.read] at loaded
              | ok word =>
                  simp only [region, Slot.read] at loaded
                  simp only [Slot.read, loaded, encoded] at written
                  have observed : Slot.read heap place.reference.region place.reference.address = .ok word :=
                    by simpa only [region, Slot.read] using loaded
                  have stored : Slot.write heap place.reference.region place.reference.address 0 = .ok after := by
                    simpa [region, aligned, Packed.insert, Packed.mask] using written
                  exact (ZeroTrace.load observed).trans (.store stored)

theorem empty_plan_zero (planned : StorageBytes.planWrite heap budget reference [] = .ok plan) :
    ∀ change ∈ plan.writes, change.2 = 0 := by
  unfold StorageBytes.planWrite at planned
  simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte] at planned
  cases loaded : StorageBytes.loadHeader heap reference with
  | error failure => simp [loaded] at planned
  | ok result =>
      rcases result with ⟨header, count⟩
      simp only [loaded, Bind.bind, Except.bind] at planned
      have emptySlots : StorageBytes.slotCount 0 = 0 := rfl
      have emptyHeader : StorageBytes.encodeHeader [] = 0 := rfl
      simp only [emptySlots, emptyHeader, Nat.zero_add, Nat.sub_zero, List.range_zero,
        List.map_nil, List.append_nil] at planned
      cases reserved : reserve budget (StorageBytes.slotCount count+1) with
      | error failure => simp [reserved] at planned
      | ok remaining =>
          simp only [reserved] at planned
          cases planned
          intro change member
          simp only [List.mem_append, List.mem_map, List.mem_singleton] at member
          rcases member with ⟨index, _, same⟩ | same
          · cases same; rfl
          · cases same; rfl

theorem applyWrites_zero (zero : ∀ change ∈ writes, change.2 = 0)
    (written : StorageBytes.applyWrites heap region writes = .ok after) : ZeroTrace heap after := by
  refine ⟨_, StorageBytes.applyWrites_trace written, ?_⟩
  intro selected address value member
  rcases List.mem_map.mp member with ⟨change, member, same⟩
  rcases change with ⟨slot, word⟩
  have valueZero := zero (slot, word) member
  cases same
  exact valueZero

theorem empty_bytes_zero
    (written : StorageBytes.writeChecked heap budget reference [] = .ok (after, remaining)) : ZeroTrace heap after := by
  unfold StorageBytes.writeChecked at written
  cases loaded : StorageBytes.loadHeader heap reference with
  | error failure => simp [loaded] at written
  | ok result =>
      rcases result with ⟨header, count⟩
      simp only [loaded, Bind.bind, Except.bind] at written
      unfold StorageBytes.write at written
      cases planned : StorageBytes.planWrite heap budget reference [] with
      | error failure => simp [planned] at written
      | ok plan =>
          simp only [planned, Bind.bind, Except.bind] at written
          cases stored : StorageBytes.applyWrites heap reference.region plan.writes with
          | error failure => simp [stored] at written
          | ok final =>
              have trace := applyWrites_zero (empty_plan_zero planned) stored
              simp only [stored] at written
              cases written
              exact trace.trans (.journal final _ _ count 0 true)

def ZeroClear (clear : Nat → Heap → Place → Result (Heap × Nat)) : Prop :=
  ∀ budget heap place after remaining, WholeCell place.type →
    clear budget heap place = .ok (after, remaining) → ZeroTrace heap after

def ZeroTail (clear : Nat → Heap → Place → SType → Nat → Nat → Result (Heap × Nat)) : Prop :=
  ∀ budget heap place element count after remaining,
    clear budget heap place element count 0 = .ok (after, remaining) → ZeroTrace heap after

theorem eraseMember_zero (safe : ZeroClear clear)
    (written : eraseMember clear reference (heap, budget, cleared) member =
      .ok (after, remaining, newCleared)) : ZeroTrace heap after := by
  unfold eraseMember at written
  dsimp only at written
  split at written
  · cases written; exact .refl _
  · split at written
    · split at written
      · cases written; exact .refl _
      · cases stored : Slot.write heap reference.region
            (reference.address+BitVec.ofNat 256 member.position.slot) 0 with
        | error failure => rw [stored] at written; cases written
        | ok final =>
            rw [stored] at written
            cases written
            exact .store stored
    · rename_i wide
      cases erased : clear budget heap (captured ⟨atLocation member.type .storage false,
          rebase reference (reference.address+BitVec.ofNat 256 member.position.slot) member.position.byte⟩) with
      | error failure => simp [erased] at written
      | ok result =>
          rcases result with ⟨final, rest⟩
          have whole : WholeCell (atLocation member.type .storage false) := by
            simp only [WholeCell, storageBytes_atLocation]
            have bound := storageBytes_getD_bound member.type
            omega
          have trace := safe budget heap _ final rest whole erased
          simp only [erased] at written
          cases written
          exact trace

theorem eraseRangeElement_zero (safe : ZeroClear clear)
    (written : eraseRangeElement clear reference data element ((storageBytes element).getD 32)
      newSlots step (heap, budget) index = .ok (after, remaining)) : ZeroTrace heap after := by
  unfold eraseRangeElement at written
  dsimp only at written
  split at written
  · cases stored : Slot.write heap reference.region (data+BitVec.ofNat 256 (newSlots+index*step)) 0 with
    | error failure => rw [stored] at written; cases written
    | ok final => rw [stored] at written; cases written; exact .store stored
  · rename_i wide
    apply safe budget heap _ after remaining _ written
    simp only [WholeCell, storageBytes_atLocation]
    have bound := storageBytes_getD_bound element
    omega

theorem clearTail_zero_step (safe : ZeroClear (erase registry fuel))
    (written : clearTail registry (fuel+1) budget heap place element count 0 = .ok (after, remaining)) :
    ZeroTrace heap after := by
  unfold clearTail at written
  dsimp only at written
  split at written
  · cases written; exact .refl _
  · split at written
    · cases written; exact .refl _
    · cases sized : storageSize registry fuel element with
      | error failure => simp [sized] at written
      | ok slots =>
          simp only [sized, Bind.bind, Except.bind] at written
          cases old : slotCount ((storageBytes element).getD 32) slots count with
          | error failure => simp [old] at written
          | ok oldSlots =>
              simp only [old] at written
              cases retained : slotCount ((storageBytes element).getD 32) slots 0 with
              | error failure => simp [retained] at written
              | ok newSlots =>
                  simp only [retained] at written
                  generalize countEq : ((BitVec.ofNat 256 oldSlots-BitVec.ofNat 256 newSlots).toNat+
                    (if (storageBytes element).getD 32 < 32 then 1 else slots)-1) /
                    (if (storageBytes element).getD 32 < 32 then 1 else slots) = iterations at written
                  cases reserved : reserve budget (iterations+1) with
                  | error failure => simp [reserved] at written
                  | ok allowance =>
                      simp only [reserved] at written
                      have partialClear : clearPartial heap place.reference.region (cleanupData place).address
                          0 ((storageBytes element).getD 32) newSlots = .ok heap := by
                        simp [clearPartial]
                      rw [partialClear] at written
                      exact fold_zero_trace (fun state : Heap × Nat => state.1)
                        (eraseRangeElement (erase registry fuel) place.reference (cleanupData place).address
                          element ((storageBytes element).getD 32) newSlots
                          (if (storageBytes element).getD 32 < 32 then 1 else slots))
                        (fun before index after done => by
                          rcases before with ⟨heap, budget⟩
                          rcases after with ⟨after, remaining⟩
                          exact eraseRangeElement_zero safe done) (List.range iterations) written

theorem eraseContents_zero (safe : ZeroClear clear) (tailSafe : ZeroTail clearArray)
    (whole : WholeCell place.type) (storage : StorageRegion place.reference.region)
    (written : eraseContents registry fuel clear clearArray budget heap place = .ok (after, remaining)) :
    ZeroTrace heap after := by
  cases type : place.type <;>
    simp only [eraseContents, type, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
  all_goals try
    (cases stored : scalarZero heap place with
    | error failure => simp [stored] at written
    | ok final =>
        have trace := scalarZero_zero whole storage stored
        simp only [stored] at written
        cases written
        exact trace)
  case mapping key value => cases written; exact .refl _
  case bytes location pointer => exact empty_bytes_zero written
  case string location pointer => exact empty_bytes_zero written
  case array element size location pointer =>
    cases sized : Access.length heap place with
    | error failure => simp [sized] at written
    | ok count =>
        simp only [sized] at written
        cases size with
        | some length =>
            simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at written
            exact tailSafe budget heap place element count after remaining written
        | none =>
            simp only [Option.isNone_none, ↓reduceIte] at written
            split at written
            · cases written
            · rename_i middle stored
              exact (ZeroTrace.store stored).trans
                ((ZeroTrace.journal middle _ _ count 0 false).trans
                  (tailSafe budget _ place element count after remaining written))
  case structType identity location pointer =>
    cases fields : registry.structFields identity with
    | none => simp [fields] at written
    | some members =>
        simp only [fields] at written
        cases layout : fieldLayout registry fuel members {} with
        | error failure => simp [layout] at written
        | ok laidOut =>
            simp only [layout] at written
            cases reserved : reserve budget laidOut.fields.length with
            | error failure => simp [reserved] at written
            | ok allowance =>
                simp only [reserved] at written
                cases filled : laidOut.fields.foldlM (eraseMember clear place.reference)
                    (heap, allowance, ([] : List Word)) with
                | error failure => simp [filled] at written
                | ok result =>
                    rcases result with ⟨final, rest, cleared⟩
                    have trace := fold_zero_trace (fun state : Heap × Nat × List Word => state.1)
                      (eraseMember clear place.reference)
                      (fun before member after done => by
                        rcases before with ⟨heap, budget, cleared⟩
                        rcases after with ⟨after, remaining, newCleared⟩
                        exact eraseMember_zero safe done) laidOut.fields filled
                    simp only [filled] at written
                    cases written
                    exact trace

theorem erase_zero_step (safe : ZeroClear (erase registry fuel)) (tailSafe : ZeroTail (clearTail registry fuel))
    (whole : WholeCell place.type)
    (written : erase registry (fuel+1) budget heap place = .ok (after, remaining)) : ZeroTrace heap after := by
  unfold erase at written
  cases checked : Access.validate heap place with
  | error failure => simp [checked] at written
  | ok _ =>
      simp only [checked] at written
      cases reserved : reserve budget 1 with
      | error failure => simp [reserved] at written
      | ok allowance =>
          simp only [reserved] at written
          cases region : place.reference.region with
          | memory invocation => simp [region] at written
          | calldata invocation => simp [region] at written
          | storage owner =>
              simp only [region, Pure.pure, Except.pure] at written
              exact eraseContents_zero safe tailSafe whole (Or.inl ⟨owner, region⟩) written
          | transient owner =>
              simp only [region, Pure.pure, Except.pure] at written
              exact eraseContents_zero safe tailSafe whole (Or.inr ⟨owner, region⟩) written

theorem cleanup_zero (registry : Registry) (fuel : Nat) :
    ZeroClear (erase registry fuel) ∧ ZeroTail (clearTail registry fuel) := by
  induction fuel with
  | zero =>
      constructor
      · intro budget heap place after remaining whole done; cases done
      · intro budget heap place element count after remaining done; cases done
  | succ fuel ih => exact ⟨fun _ _ _ _ _ whole done => erase_zero_step ih.1 ih.2 whole done,
      fun _ _ _ _ _ _ _ done => clearTail_zero_step ih.1 done⟩

theorem erase_zeroStores (whole : WholeCell place.type)
    (written : erase registry fuel budget heap place = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after ∧ ZeroStores events :=
  (cleanup_zero registry fuel).1 _ _ _ _ _ whole written

theorem delete_zeroStores (whole : WholeCell place.type)
    (written : delete registry fuel budget heap place = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after ∧ ZeroStores events := by
  unfold delete at written
  split at written
  · cases written
  · exact erase_zeroStores whole written

theorem zero_preserved (zero : ZeroStores events) (account slot : Word) :
    events.foldl (StorageEvent.persistent account slot) 0 = 0 := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      have tailZero : ZeroStores rest := fun region address value member =>
        zero region address value (List.mem_cons_of_mem event member)
      have headZero : StorageEvent.persistent account slot 0 event = 0 := by
        cases event with
        | load region address value | resize region address oldLength newLength bytes => rfl
        | store region address value =>
            have same := zero region address value (List.mem_cons_self)
            subst value
            cases region <;> simp [StorageEvent.persistent]
      rw [List.foldl_cons, headZero]
      exact ih tailZero

/-- Every physical persistent word that the eraser touches is zero afterward,
including when another later erase path reaches that same word. -/
theorem zero_touched (trace : StorageTrace before events after) (zero : ZeroStores events)
    {owner : BitVec 160}
    (touched : .store (.storage owner) slot value ∈ events) :
    after.execution.world.storage (owner.setWidth 256) slot = 0 := by
  have valueZero := zero (.storage owner) slot value touched
  subst value
  rcases List.mem_iff_append.mp touched with ⟨initial, suffix, decomposition⟩
  have tailZero : ZeroStores suffix := by
    intro region address value member
    apply zero region address value
    rw [decomposition]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
  rw [trace.persistent, decomposition, List.foldl_append, List.foldl_cons]
  simp only [StorageEvent.persistent, Bool.and_self]
  exact zero_preserved tailZero _ _

/-- A mapping payload is retained unless an actual physical erase store
aliases it. Distinct keys or logical paths are not a separation proof. -/
theorem zero_frame (trace : StorageTrace before events after)
    (separate : PersistentSeparate events account slot) :
    after.execution.world.storage account slot = before.execution.world.storage account slot :=
  trace.persistent_frame separate

theorem erase_representation (whole : WholeCell place.type)
    (written : erase registry fuel budget heap place = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after ∧ ZeroStores events ∧
      (∀ owner slot value, .store (.storage owner) slot value ∈ events →
        after.execution.world.storage (owner.setWidth 256) slot = 0) ∧
      (∀ account slot, PersistentSeparate events account slot →
        after.execution.world.storage account slot = heap.execution.world.storage account slot) := by
  rcases erase_zeroStores whole written with ⟨events, trace, zero⟩
  exact ⟨events, trace, zero, fun _ _ _ touched => zero_touched trace zero touched,
    fun _ _ separate => zero_frame trace separate⟩

end Solidity.Aggregates.Deletion
