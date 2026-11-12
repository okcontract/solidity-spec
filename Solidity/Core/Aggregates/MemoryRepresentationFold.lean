/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.MemoryConstructionFrame

namespace Solidity.Aggregates.Copy

/-- A mutable construction fold preserves a prefix invariant. The step premise
gets the actual indexed source item, so it can establish its new physical cell
and frame every earlier cell. No successful fold is assumed to represent its
input merely because it returned successfully. -/
theorem foldlM_zipIdx_invariant (step : State → α × Nat → Result State)
    (items : List α) (start : Nat) (property : Nat → State → Prop)
    (initial : property start before)
    (safe : ∀ item state next, item ∈ items.zipIdx start →
      property item.2 state → step state item = .ok next → property (item.2+1) next)
    (finished : (items.zipIdx start).foldlM step before = .ok after) :
    property (start+items.length) after := by
  induction items generalizing start before with
  | nil =>
      cases finished
      simpa using initial
  | cons first rest ih =>
      simp only [List.zipIdx_cons, List.foldlM_cons] at finished
      cases advanced : step before (first, start) with
      | error failure => simp [advanced, Bind.bind, Except.bind] at finished
      | ok next =>
          simp only [advanced, Bind.bind, Except.bind] at finished
          have firstMember : (first, start) ∈ (first :: rest).zipIdx start := by
            simp only [List.zipIdx_cons]; exact List.mem_cons_self
          have nextInvariant := safe (first, start) before next firstMember initial advanced
          have restInvariant := ih (before := next) (start+1) nextInvariant
            (fun item state after member prior done => safe item state after
              (by simp only [List.zipIdx_cons]; exact List.mem_cons_of_mem _ member) prior done)
            finished
          simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using restInvariant

end Solidity.Aggregates.Copy
