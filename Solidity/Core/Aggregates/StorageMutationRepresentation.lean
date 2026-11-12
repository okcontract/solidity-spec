/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.StorageArrays
import Solidity.Core.Aggregates.StorageTrace

/-! Ordered physical cleanup effects. These derivations retain actual loaded
words, stores and lifetime journal updates; a hashed start address need not be
disjoint from any other address. Generic trace frames are therefore conditional
on the physical slots written, never on logical path inequality. -/
namespace Solidity.Aggregates
open Core Static
open Contract.Interaction (Word)

private theorem mutation_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem mutation_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] mutation_map_error mutation_map_ok Bind.bind Except.bind Pure.pure Except.pure

def StorageRegion (region : Region) : Prop :=
  (∃ owner, region = .storage owner) ∨ (∃ owner, region = .transient owner)

theorem writeScalar_storage_trace (place : Place) (value : place.type.Value)
    (storage : StorageRegion place.reference.region)
    (written : writeScalar heap place value = .ok after) :
    ∃ events, StorageTrace heap events after := by
  rcases storage with ⟨owner, region⟩ | ⟨owner, region⟩
  all_goals
    unfold writeScalar at written
    cases sized : storageBytes place.type with
    | none => simp [sized] at written
    | some bytes =>
        simp only [sized, region, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
        split at written
        · cases written
        · cases loaded : Slot.read heap place.reference.region place.reference.address with
          | error failure => simp [region, Slot.read] at loaded
          | ok word =>
              simp only [region, Slot.read] at loaded
              simp only [Slot.read, loaded] at written
              cases encoded : encodeStorage place.type value with
              | error failure => simp [encoded] at written
              | ok packet =>
                  simp only [encoded] at written
                  have observed : Slot.read heap place.reference.region place.reference.address = .ok word :=
                    by simpa only [region, Slot.read] using loaded
                  exact ⟨_, (StorageTrace.read observed).append (.write written)⟩

theorem scalarZero_trace (storage : StorageRegion place.reference.region)
    (written : StorageArrays.scalarZero heap place = .ok after) :
    ∃ events, StorageTrace heap events after := by
  unfold StorageArrays.scalarZero at written
  cases zero : defaultScalar place.type with
  | none => simp [zero] at written
  | some value =>
      simp only [zero] at written
      exact writeScalar_storage_trace place value storage written

theorem fold_storage_trace (heapOf : State → Heap) (step : State → α → Result State)
    (safe : ∀ before item after, step before item = .ok after →
      ∃ events, StorageTrace (heapOf before) events (heapOf after))
    (items : List α) (finished : items.foldlM step before = .ok after) :
    ∃ events, StorageTrace (heapOf before) events (heapOf after) := by
  induction items generalizing before with
  | nil => cases finished; exact ⟨[], .nil _⟩
  | cons item rest ih =>
      rw [List.foldlM_cons] at finished
      cases first : step before item with
      | error failure => simp [first] at finished
      | ok middle =>
          simp only [first, Bind.bind, Except.bind] at finished
          rcases safe before item middle first with ⟨initial, firstTrace⟩
          rcases ih finished with ⟨final, lastTrace⟩
          exact ⟨initial ++ final, firstTrace.append lastTrace⟩

theorem StorageBytes.applyWrites_trace
    (written : StorageBytes.applyWrites heap region writes = .ok after) :
    StorageTrace heap (writes.map fun (slot, value) => .store region slot value) after := by
  induction writes generalizing heap with
  | nil => cases written; exact .nil _
  | cons change rest ih =>
      rcases change with ⟨slot, value⟩
      unfold StorageBytes.applyWrites at written
      cases first : Slot.write heap region slot value with
      | error failure => simp [first] at written
      | ok middle =>
          simp only [first, Bind.bind, Except.bind] at written
          exact .store first (ih written)

theorem StorageBytes.write_trace
    (written : StorageBytes.write heap budget reference bytes = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := by
  unfold StorageBytes.write at written
  cases planned : StorageBytes.planWrite heap budget reference bytes with
  | error failure => simp [planned] at written
  | ok plan =>
      simp only [planned, Bind.bind, Except.bind] at written
      cases stored : StorageBytes.applyWrites heap reference.region plan.writes with
      | error failure => simp [stored] at written
      | ok final =>
          simp only [stored] at written
          cases written
          exact ⟨_, StorageBytes.applyWrites_trace stored⟩

theorem StorageBytes.writeChecked_trace
    (written : StorageBytes.writeChecked heap budget reference bytes = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := by
  unfold StorageBytes.writeChecked at written
  cases loaded : StorageBytes.loadHeader heap reference with
  | error failure => simp [loaded] at written
  | ok header =>
      rcases header with ⟨word, count⟩
      simp only [loaded, Bind.bind, Except.bind] at written
      cases stored : StorageBytes.write heap budget reference bytes with
      | error failure => simp [stored] at written
      | ok result =>
          rcases result with ⟨final, rest⟩
          rcases StorageBytes.write_trace stored with ⟨events, trace⟩
          simp only [stored] at written
          cases written
          exact ⟨events ++ [.resize reference.region reference.address count bytes.length true],
            trace.append (.journal final _ _ _ _ _)⟩

namespace StorageArrays

def ClearHasTrace (clear : Nat → Heap → Place → Result (Heap × Nat)) : Prop :=
  ∀ budget heap place after remaining, clear budget heap place = .ok (after, remaining) →
    ∃ events, StorageTrace heap events after

theorem clearPartial_trace
    (written : clearPartial heap region data start bytes newSlots = .ok after) :
    ∃ events, StorageTrace heap events after := by
  unfold clearPartial at written
  dsimp only at written
  split at written
  · split at written
    · cases written; exact ⟨[], .nil _⟩
    · cases loaded : Slot.read heap region (data + BitVec.ofNat 256 newSlots - 1) with
      | error failure => rw [loaded] at written; cases written
      | ok word =>
          rw [loaded] at written
          dsimp only [Bind.bind, Except.bind] at written
          exact ⟨_, (StorageTrace.read loaded).append (.write written)⟩
  · cases written; exact ⟨[], .nil _⟩

theorem eraseMember_trace (safe : ClearHasTrace clear)
    (written : eraseMember clear reference (heap, budget, cleared) member =
      .ok (after, remaining, newCleared)) :
    ∃ events, StorageTrace heap events after := by
  unfold eraseMember at written
  dsimp only at written
  split at written
  · cases written; exact ⟨[], .nil _⟩
  · split at written
    · split at written
      · cases written; exact ⟨[], .nil _⟩
      · cases stored : Slot.write heap reference.region
            (reference.address + BitVec.ofNat 256 member.position.slot) 0 with
        | error failure => rw [stored] at written; cases written
        | ok final =>
            rw [stored] at written
            cases written
            exact ⟨_, .write stored⟩
    · cases erased : clear budget heap (captured ⟨atLocation member.type .storage false,
          rebase reference (reference.address + BitVec.ofNat 256 member.position.slot) member.position.byte⟩) with
      | error failure => simp [erased] at written
      | ok result =>
          rcases result with ⟨final, rest⟩
          have trace := safe budget heap _ final rest erased
          simp only [erased] at written
          cases written
          exact trace

theorem eraseRangeElement_trace (safe : ClearHasTrace clear)
    (written : eraseRangeElement clear reference data element bytes newSlots step (heap, budget) index =
      .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := by
  unfold eraseRangeElement at written
  dsimp only at written
  split at written
  · cases stored : Slot.write heap reference.region
        (data + BitVec.ofNat 256 (newSlots + index*step)) 0 with
    | error failure => rw [stored] at written; cases written
    | ok final =>
        rw [stored] at written
        cases written
        exact ⟨_, .write stored⟩
  · exact safe budget heap _ after remaining written

theorem clearTail_step_trace (safe : ClearHasTrace (erase registry fuel))
    (written : clearTail registry (fuel+1) budget heap place element oldLength start = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := by
  unfold clearTail at written
  dsimp only at written
  split at written
  · cases written; exact ⟨[], .nil _⟩
  · split at written
    · cases written; exact ⟨[], .nil _⟩
    · cases sized : storageSize registry fuel element with
      | error failure => simp [sized] at written
      | ok slots =>
          simp only [sized, Bind.bind, Except.bind] at written
          cases old : slotCount ((storageBytes element).getD 32) slots oldLength with
          | error failure => simp [old] at written
          | ok oldSlots =>
              simp only [old] at written
              cases retained : slotCount ((storageBytes element).getD 32) slots start with
              | error failure => simp [retained] at written
              | ok newSlots =>
                  simp only [retained] at written
                  generalize countEq : ((BitVec.ofNat 256 oldSlots - BitVec.ofNat 256 newSlots).toNat +
                    (if (storageBytes element).getD 32 < 32 then 1 else slots) - 1) /
                    (if (storageBytes element).getD 32 < 32 then 1 else slots) = count at written
                  cases reserved : reserve budget (count+1) with
                  | error failure => simp [reserved] at written
                  | ok available =>
                      simp only [reserved] at written
                      simp only [Pure.pure, Except.pure] at written
                      split at written
                      · cases written
                      · rename_i middle completed
                        have tailTrace := fold_storage_trace (fun state : Heap × Nat => state.1)
                          (eraseRangeElement (erase registry fuel) place.reference (cleanupData place).address element
                            ((storageBytes element).getD 32) newSlots
                            (if (storageBytes element).getD 32 < 32 then 1 else slots))
                          (fun state index final done => by
                            rcases state with ⟨before, allowance⟩
                            rcases final with ⟨after, unused⟩
                            exact eraseRangeElement_trace safe done) (List.range count) written
                        rcases clearPartial_trace completed with ⟨prefixEvents, firstTrace⟩
                        rcases tailTrace with ⟨suffixEvents, lastTrace⟩
                        exact ⟨prefixEvents ++ suffixEvents, firstTrace.append lastTrace⟩

def TailHasTrace (clear : Nat → Heap → Place → SType → Nat → Nat → Result (Heap × Nat)) : Prop :=
  ∀ budget heap place element count start after remaining,
    clear budget heap place element count start = .ok (after, remaining) →
    ∃ events, StorageTrace heap events after

private theorem scalarErase_trace (storage : StorageRegion place.reference.region)
    (written : (do let after ← scalarZero heap place; pure (after, budget)) =
      .ok (after, remaining)) : ∃ events, StorageTrace heap events after := by
  cases stored : scalarZero heap place with
  | error failure => simp [stored] at written
  | ok final =>
      simp only [stored, Bind.bind, Except.bind] at written
      cases written
      exact scalarZero_trace storage stored

theorem eraseContents_trace (safe : ClearHasTrace clear) (arraySafe : TailHasTrace clearArray)
    (storage : StorageRegion place.reference.region)
    (written : eraseContents registry fuel clear clearArray budget heap place = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := by
  cases type : place.type <;>
    simp only [eraseContents, type, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
  all_goals try exact scalarErase_trace storage written
  case mapping key value => cases written; exact ⟨[], .nil _⟩
  case bytes location pointer => exact StorageBytes.writeChecked_trace written
  case string location pointer => exact StorageBytes.writeChecked_trace written
  case array element size location pointer =>
    cases sized : Access.length heap place with
    | error failure => simp [sized] at written
    | ok count =>
        simp only [sized] at written
        cases size with
        | some length =>
            simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at written
            exact arraySafe budget heap place element count 0 after remaining written
        | none =>
            simp only [Option.isNone_none, ↓reduceIte] at written
            split at written
            · cases written
            · rename_i middle stored
              rcases arraySafe budget _ place element count 0 after remaining written with ⟨events, trace⟩
              exact ⟨_, (StorageTrace.write stored).append
                ((StorageTrace.journal middle _ _ count 0 false).append trace)⟩
  case structType identity location pointer =>
    cases fields : registry.structFields identity with
    | none => simp [fields] at written
    | some members =>
        simp only [fields] at written
        cases laidOut : fieldLayout registry fuel members {} with
        | error failure => simp [laidOut] at written
        | ok layout =>
            simp only [laidOut] at written
            cases reserved : reserve budget layout.fields.length with
            | error failure => simp [reserved] at written
            | ok allowance =>
                simp only [reserved] at written
                cases filled : layout.fields.foldlM (eraseMember clear place.reference)
                    (heap, allowance, ([] : List Word)) with
                | error failure => simp [filled] at written
                | ok result =>
                    rcases result with ⟨final, rest, cleared⟩
                    have bodyTrace := fold_storage_trace (fun state : Heap × Nat × List Word => state.1)
                      (eraseMember clear place.reference)
                      (fun state member after done => by
                        rcases state with ⟨heap, budget, cleared⟩
                        rcases after with ⟨after, remaining, newCleared⟩
                        exact eraseMember_trace safe done) layout.fields filled
                    simp only [filled] at written
                    cases written
                    exact bodyTrace

theorem erase_step_trace (safe : ClearHasTrace (erase registry fuel))
    (arraySafe : TailHasTrace (clearTail registry fuel))
    (written : erase registry (fuel+1) budget heap place = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := by
  unfold erase at written
  cases checked : Access.validate heap place with
  | error failure => simp [checked] at written
  | ok _ =>
      simp only [checked, Bind.bind, Except.bind] at written
      cases reserved : reserve budget 1 with
      | error failure => simp [reserved] at written
      | ok allowance =>
          simp only [reserved] at written
          cases region : place.reference.region with
          | memory invocation => simp [region] at written
          | calldata invocation => simp [region] at written
          | storage owner =>
              simp only [region, Pure.pure, Except.pure] at written
              exact eraseContents_trace safe arraySafe (Or.inl ⟨owner, region⟩) written
          | transient owner =>
              simp only [region, Pure.pure, Except.pure] at written
              exact eraseContents_trace safe arraySafe (Or.inr ⟨owner, region⟩) written

theorem cleanup_trace (registry : Registry) (fuel : Nat) :
    ClearHasTrace (erase registry fuel) ∧ TailHasTrace (clearTail registry fuel) := by
  induction fuel with
  | zero =>
      constructor
      · intro budget heap place after remaining done; cases done
      · intro budget heap place element count start after remaining done; cases done
  | succ fuel ih =>
      exact ⟨fun _ _ _ _ _ done => erase_step_trace ih.1 ih.2 done,
        fun _ _ _ _ _ _ _ _ done => clearTail_step_trace ih.1 done⟩

theorem erase_trace
    (written : erase registry fuel budget heap place = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := (cleanup_trace registry fuel).1 _ _ _ _ _ written

theorem clearTail_trace
    (written : clearTail registry fuel budget heap place element count start = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := (cleanup_trace registry fuel).2 _ _ _ _ _ _ _ _ written

theorem delete_trace
    (written : delete registry fuel budget heap place = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := by
  unfold delete at written
  split at written
  · cases written
  · exact erase_trace written

theorem resize_trace
    (written : resize registry fuel budget heap place newLength = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := by
  unfold resize at written
  cases checked : Access.validate heap place with
  | error failure => simp [checked] at written
  | ok _ =>
      simp [checked] at written
      split at written
      · rename_i element size pointer typeEq
        split at written
        · split at written
          · cases written
          · cases sized : Access.length heap place with
            | error failure => simp [sized] at written
            | ok count =>
                simp [sized] at written
                split at written
                · cases written
                · cases size with
                  | some length =>
                      exact clearTail_trace written
                  | none =>
                      simp only [↓reduceIte] at written
                      split at written
                      · cases written
                      · rename_i middle stored
                        rcases clearTail_trace written with ⟨events, trace⟩
                        exact ⟨_, (StorageTrace.write stored).append
                          ((StorageTrace.journal middle _ _ count newLength false).append trace)⟩
        · cases written
      · cases written

theorem pushZero_trace
    (written : pushZero registry fuel budget heap place = .ok (element, after, remaining)) :
    ∃ events, StorageTrace heap events after := by
  unfold pushZero at written
  cases checked : Access.validate heap place with
  | error failure => simp [checked] at written
  | ok _ =>
      simp [checked] at written
      split at written
      · split at written
        · cases sized : Access.length heap place with
          | error failure => simp [sized] at written
          | ok count =>
              simp [sized] at written
              split at written
              · cases written
              · cases reserved : reserve budget 1 with
                | error failure => simp [reserved] at written
                | ok allowance =>
                    simp [reserved] at written
                    split at written
                    · cases written
                    · rename_i middle stored
                      cases located : Access.index registry fuel middle place count with
                      | error failure => simp [located] at written
                      | ok target =>
                          simp [located] at written
                          rcases written with ⟨rfl, rfl, rfl⟩
                          exact ⟨_, .write stored⟩
        · cases written
      · cases written

theorem pop_trace
    (written : pop registry fuel budget heap place = .ok (after, remaining)) :
    ∃ events, StorageTrace heap events after := by
  unfold pop at written
  cases checked : Access.validate heap place with
  | error failure => simp [checked] at written
  | ok _ =>
      simp [checked] at written
      split at written
      · split at written
        · cases sized : Access.length heap place with
          | error failure => simp [sized] at written
          | ok count =>
              simp [sized] at written
              split at written
              · cases written
              · cases located : Access.index registry fuel heap place (count-1) with
                | error failure => simp [located] at written
                | ok element =>
                    simp [located] at written
                    cases erased : erase registry fuel budget heap (captured element) with
                    | error failure => simp [erased] at written
                    | ok result =>
                        rcases result with ⟨middle, allowance⟩
                        rcases erase_trace erased with ⟨events, first⟩
                        simp [erased] at written
                        split at written
                        · cases written
                        · rename_i final stored
                          cases written
                          exact ⟨_, first.append ((StorageTrace.write stored).append
                            (StorageTrace.journal final _ _ count (count-1) false))⟩
        · cases written
      · cases written

theorem resize_frame
    (written : resize registry fuel budget heap place count = .ok (after, remaining)) :
    StorageFrame heap after := by
  rcases resize_trace written with ⟨events, trace⟩
  exact trace.frame

theorem erase_frame
    (written : erase registry fuel budget heap place = .ok (after, remaining)) :
    StorageFrame heap after := by
  rcases erase_trace written with ⟨events, trace⟩
  exact trace.frame

end StorageArrays

end Solidity.Aggregates
