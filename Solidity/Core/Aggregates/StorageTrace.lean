/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Types

/-! Ordered physical storage observations. Loads record the word read at that
point, so a later store cannot retroactively change a cached source word.
Lifetime journal events affect source references but never EVM storage bytes. -/
namespace Solidity.Aggregates
open Static
open Contract.Interaction (Word World)

inductive StorageEvent where
  | load (region : Region) (slot word : Word)
  | store (region : Region) (slot word : Word)
  | resize (region : Region) (slot : Word) (oldLength newLength : Nat) (bytes : Bool)
  deriving DecidableEq, Repr

inductive StorageTrace : Heap → List StorageEvent → Heap → Prop where
  | nil (heap : Heap) : StorageTrace heap [] heap
  | load (read : Slot.read before region slot = .ok word)
      (tail : StorageTrace before events after) :
      StorageTrace before (.load region slot word :: events) after
  | store (written : Slot.write before region slot word = .ok middle)
      (tail : StorageTrace middle events after) :
      StorageTrace before (.store region slot word :: events) after
  | resize (tail : StorageTrace (before.journalResize region slot oldLength newLength bytes) events after) :
      StorageTrace before (.resize region slot oldLength newLength bytes :: events) after

theorem StorageTrace.append (first : StorageTrace before initial middle)
    (last : StorageTrace middle final after) : StorageTrace before (initial ++ final) after := by
  induction first with
  | nil => exact last
  | load read _ ih => exact .load read (ih last)
  | store written _ ih => exact .store written (ih last)
  | resize _ ih => exact .resize (ih last)

theorem StorageTrace.read (read : Slot.read heap region slot = .ok word) :
    StorageTrace heap [.load region slot word] heap := .load read (.nil heap)

theorem StorageTrace.write (written : Slot.write before region slot word = .ok after) :
    StorageTrace before [.store region slot word] after := .store written (.nil after)

theorem StorageTrace.journal (heap : Heap) (region : Region) (slot : Word)
    (oldLength newLength : Nat) (bytes : Bool) :
    StorageTrace heap [.resize region slot oldLength newLength bytes]
      (heap.journalResize region slot oldLength newLength bytes) := .resize (.nil _)

/-- Components untouched by every physical persistent/transient store and
every lifetime-journal event. No separation premise is needed for these. -/
def StorageFrame (before after : Heap) : Prop :=
  after.execution.memory = before.execution.memory ∧
  after.execution.context = before.execution.context ∧
  after.invocation = before.invocation ∧ after.nextMemory = before.nextMemory ∧
  after.allocations = before.allocations ∧
  after.execution.world.logs = before.execution.world.logs ∧
  after.execution.world.accounts = before.execution.world.accounts ∧
  after.execution.world.other = before.execution.world.other

theorem StorageFrame.refl (heap : Heap) : StorageFrame heap heap :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem StorageFrame.trans (first : StorageFrame before middle) (last : StorageFrame middle after) :
    StorageFrame before after := by
  rcases first with ⟨m₁, c₁, i₁, f₁, a₁, l₁, ac₁, o₁⟩
  rcases last with ⟨m₂, c₂, i₂, f₂, a₂, l₂, ac₂, o₂⟩
  exact ⟨m₂.trans m₁, c₂.trans c₁, i₂.trans i₁, f₂.trans f₁,
    a₂.trans a₁, l₂.trans l₁, ac₂.trans ac₁, o₂.trans o₁⟩

theorem Slot.write_frame (written : Slot.write before region slot word = .ok after) :
    StorageFrame before after := by
  unfold Slot.write at written
  split at written
  · cases written
  · cases region <;> cases written
    all_goals exact StorageFrame.refl _

theorem StorageFrame.journal (heap : Heap) (region : Region) (slot : Word)
    (oldLength newLength : Nat) (bytes : Bool) :
    StorageFrame heap (heap.journalResize region slot oldLength newLength bytes) := by
  unfold StorageFrame Heap.journalResize
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem StorageTrace.frame (trace : StorageTrace before events after) : StorageFrame before after := by
  induction trace with
  | nil => exact .refl _
  | load _ _ ih => exact ih
  | store written _ ih => exact (Slot.write_frame written).trans ih
  | resize _ ih => exact (StorageFrame.journal _ _ _ _ _ _).trans ih

def StorageEvent.persistent (account slot previous : Word) : StorageEvent → Word
  | .store (.storage owner) written value =>
      if account = owner.setWidth 256 && slot = written then value else previous
  | _ => previous

def StorageEvent.transient (account : BitVec 160) (slot previous : Word) : StorageEvent → Word
  | .store (.transient owner) written value =>
      if account = owner && slot = written then value else previous
  | _ => previous

theorem Slot.write_persistent (written : Slot.write before region slot word = .ok after)
    (account observed : Word) :
    after.execution.world.storage account observed =
      StorageEvent.persistent account observed (before.execution.world.storage account observed)
        (.store region slot word) := by
  unfold Slot.write at written
  split at written
  · cases written
  · cases region <;> cases written <;> rfl

theorem Slot.write_transient (written : Slot.write before region slot word = .ok after)
    (account : BitVec 160) (observed : Word) :
    after.execution.world.transient account observed =
      StorageEvent.transient account observed (before.execution.world.transient account observed)
        (.store region slot word) := by
  unfold Slot.write at written
  split at written
  · cases written
  · cases region <;> cases written
    case storage.refl owner => rfl
    case transient.refl owner =>
      simp [StorageEvent.transient, World.tstore,
        BitVec.setWidth_setWidth_of_le owner (by decide : 160 ≤ 256)]

/-- Last matching physical persistent store wins, including aliases between a
header, payload, cleanup word, or any other logical source path. -/
theorem StorageTrace.persistent (trace : StorageTrace before events after) (account slot : Word) :
    after.execution.world.storage account slot =
      events.foldl (StorageEvent.persistent account slot) (before.execution.world.storage account slot) := by
  induction trace with
  | nil => rfl
  | load read tail ih => exact ih
  | @store before region written value middle events after stored tail ih =>
      simp only [List.foldl_cons]
      rw [← Slot.write_persistent stored account slot]
      exact ih
  | resize tail ih =>
      simpa only [List.foldl_cons, StorageEvent.persistent, Heap.journalResize_execution] using ih

theorem StorageTrace.transient (trace : StorageTrace before events after)
    (account : BitVec 160) (slot : Word) :
    after.execution.world.transient account slot =
      events.foldl (StorageEvent.transient account slot) (before.execution.world.transient account slot) := by
  induction trace with
  | nil => rfl
  | load read tail ih => exact ih
  | @store before region written value middle events after stored tail ih =>
      simp only [List.foldl_cons]
      rw [← Slot.write_transient stored account slot]
      exact ih
  | resize tail ih =>
      simpa only [List.foldl_cons, StorageEvent.transient, Heap.journalResize_execution] using ih

def PersistentSeparate (events : List StorageEvent) (account slot : Word) : Prop :=
  ∀ event ∈ events, ∀ owner written value, event = .store (.storage owner) written value →
    account ≠ owner.setWidth 256 ∨ slot ≠ written

theorem persistent_untouched (separate : PersistentSeparate events account slot) (previous : Word) :
    events.foldl (StorageEvent.persistent account slot) previous = previous := by
  induction events generalizing previous with
  | nil => rfl
  | cons event rest ih =>
      have remaining : PersistentSeparate rest account slot :=
        fun entry member owner written value same => separate entry (by simp [member]) owner written value same
      rw [List.foldl_cons, ih remaining]
      cases event with
      | load region address value => rfl
      | resize region address oldLength newLength bytes => rfl
      | store region address value =>
          cases region with
          | storage owner =>
              have apart := separate (.store (.storage owner) address value) (by simp) owner address value rfl
              rcases apart with otherAccount | otherSlot <;> simp [StorageEvent.persistent, *]
          | transient owner | memory invocation | calldata invocation => rfl

theorem StorageTrace.persistent_frame (trace : StorageTrace before events after)
    (separate : PersistentSeparate events account slot) :
    after.execution.world.storage account slot = before.execution.world.storage account slot := by
  rw [trace.persistent, persistent_untouched separate]

end Solidity.Aggregates
