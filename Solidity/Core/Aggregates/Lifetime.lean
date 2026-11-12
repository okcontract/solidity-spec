/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Access

namespace Solidity.Aggregates.Access
open Static
open Contract.Interaction (Word)

theorem stale_head_rejected (reference : Reference) (guard : ReferenceGuard)
    (rest : List ReferenceGuard)
    (history : heap.historyEpoch reference.region = guard.historyEpoch)
    (stale : heap.generations reference.region guard.slot guard.index ≠ guard.generation) :
    checkGuards heap {reference with guards := guard :: rest} =
      .error (.undefinedBehavior "dangling storage reference after element removal") := by
  apply checkGuards_head_error
  simp [checkGuard, history, stale, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem removed_capture_rejected (heap : Heap) (reference : Reference)
    (index first stop : Nat) (bytes : Bool) (removed : first ≤ index ∧ index < stop) :
    checkGuards (heap.retire reference.region reference.address first stop)
      {reference with guards := [captureGuard heap reference index bytes]} =
      .error (.undefinedBehavior "dangling storage reference after element removal") := by
  apply stale_head_rejected
  · rfl
  · simp only [captureGuard]
    rw [Heap.retire_removed heap reference.region reference.address first stop index removed]
    omega

theorem layout_head_rejected (reference : Reference) (guard : ReferenceGuard)
    (rest : List ReferenceGuard)
    (history : heap.historyEpoch reference.region = guard.historyEpoch)
    (same : heap.generations reference.region guard.slot guard.index = guard.generation)
    (captured : guard.layoutGeneration = some generation)
    (stale : heap.layouts reference.region guard.slot ≠ generation) :
    checkGuards heap {reference with guards := guard :: rest} =
      .error (.undefinedBehavior "dangling bytes reference after layout transition") := by
  apply checkGuards_head_error
  simp [checkGuard, history, same, captured, stale, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem relocated_capture_rejected (heap : Heap) (reference : Reference) (index : Nat) :
    checkGuards (heap.moveLayout reference.region reference.address)
      {reference with guards := [captureGuard heap reference index true]} =
      .error (.undefinedBehavior "dangling bytes reference after layout transition") := by
  apply layout_head_rejected
  · rfl
  · rfl
  · rfl
  · simp [Heap.moveLayout, captureGuard]

end Solidity.Aggregates.Access
