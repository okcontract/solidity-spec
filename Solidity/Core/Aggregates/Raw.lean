/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Access

/-! Explicit raw-state interfaces invalidate source-reference history.
Unknown histories produce invalidContext, rather than inventing a dangling
reference witness or silently accepting an old reference after remove/regrow.
World replacement consumes a separately admitted transition; source permissions,
external-call rollback and gas are responsibilities of its enclosing boundary. -/
namespace Solidity.Aggregates.Raw
open Static
open Contract.Interaction (Word World)

def invalidateRegion (heap : Heap) (region : Region) : Heap :=
  {heap with historyEpoch := fun selected =>
    if selected = region then heap.historyEpoch selected+1 else heap.historyEpoch selected}

def invalidateStorageHistories (heap : Heap) : Heap :=
  {heap with historyEpoch := fun region => match region with
    | .storage _ | .transient _ => heap.historyEpoch region+1
    | .memory _ | .calldata _ => heap.historyEpoch region}

def write (heap : Heap) (region : Region) (slot value : Word) : Result Heap := do
  let after ← Slot.write heap region slot value
  return invalidateRegion after region

def replaceWorld (heap : Heap) (world : World) : Heap :=
  invalidateStorageHistories {heap with execution := {heap.execution with world}}

theorem invalidateRegion_same (heap : Heap) (region : Region) :
    (invalidateRegion heap region).historyEpoch region = heap.historyEpoch region+1 := by
  simp [invalidateRegion]

theorem invalidateRegion_other (heap : Heap) (region selected : Region) (different : selected ≠ region) :
    (invalidateRegion heap region).historyEpoch selected = heap.historyEpoch selected := by
  simp [invalidateRegion, different]

theorem invalidateRegion_execution (heap : Heap) (region : Region) :
    (invalidateRegion heap region).execution = heap.execution := rfl

theorem replaceWorld_memory_epoch (heap : Heap) (world : World) (invocation : Nat) :
    (replaceWorld heap world).historyEpoch (.memory invocation) = heap.historyEpoch (.memory invocation) := rfl

theorem replaceWorld_calldata_epoch (heap : Heap) (world : World) (invocation : Nat) :
    (replaceWorld heap world).historyEpoch (.calldata invocation) = heap.historyEpoch (.calldata invocation) := rfl

theorem replaceWorld_storage_epoch (heap : Heap) (world : World) (owner : BitVec 160) :
    (replaceWorld heap world).historyEpoch (.storage owner) = heap.historyEpoch (.storage owner)+1 := rfl

theorem replaceWorld_transient_epoch (heap : Heap) (world : World) (owner : BitVec 160) :
    (replaceWorld heap world).historyEpoch (.transient owner) = heap.historyEpoch (.transient owner)+1 := rfl

theorem replaceWorld_world (heap : Heap) (world : World) :
    (replaceWorld heap world).execution.world = world := rfl

theorem replaceWorld_memory (heap : Heap) (world : World) :
    (replaceWorld heap world).execution.memory = heap.execution.memory := rfl

theorem typed_write_history (written : Slot.write heap region slot value = .ok after) :
    after.historyEpoch = heap.historyEpoch := by
  unfold Slot.write at written
  split at written
  · cases written
  · cases region <;> cases written <;> rfl

theorem write_history (written : write heap region slot value = .ok after) :
    after.historyEpoch region = heap.historyEpoch region+1 := by
  unfold write at written
  cases stored : Slot.write heap region slot value with
  | error failure => simp [stored] at written <;> cases written
  | ok physical =>
      have history := typed_write_history stored
      simp only [stored, Bind.bind, Except.bind] at written
      cases written
      simp [invalidateRegion, history]

theorem invalidated_capture_rejected (heap : Heap) (reference : Reference) (index : Nat) (bytes : Bool) :
    Access.checkGuard (invalidateRegion heap reference.region) reference.region
      (Access.captureGuard heap reference index bytes) =
        .error (.invalidContext "storage reference lifetime history invalidated by raw transition") := by
  apply Access.checkGuard_history_rejected
  simp [invalidateRegion, Access.captureGuard]

theorem replaced_capture_rejected (heap : Heap) (world : World) (reference : Reference)
    {owner : BitVec 160}
    (storage : reference.region = .storage owner ∨ reference.region = .transient owner)
    (index : Nat) (bytes : Bool) :
    Access.checkGuard (replaceWorld heap world) reference.region
      (Access.captureGuard heap reference index bytes) =
        .error (.invalidContext "storage reference lifetime history invalidated by raw transition") := by
  apply Access.checkGuard_history_rejected
  rcases storage with storage | transient
  · simp [replaceWorld, invalidateStorageHistories, Access.captureGuard, storage]
  · simp [replaceWorld, invalidateStorageHistories, Access.captureGuard, transient]

end Solidity.Aggregates.Raw
