/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.ImmutableStorageCopy
import Solidity.Core.Aggregates.StorageEffects

/-! Every recursive storage-target copy has a finite action refinement. Scalar
member writes retain their precise byte footprints; bulk packed words, byte
payloads and cleanup reuse the physical trace. The generic produced-leaf laws
therefore apply through arbitrary later array/struct children. -/
namespace Solidity.Aggregates.Copy
open Core Static

private theorem access_write_scalar {target : Place}
    (written : Access.write before target value = .ok after) :
    ∃ scalar : target.type.Value, value = ⟨target.type, scalar⟩ ∧ writeScalar before target scalar = .ok after := by
  unfold Access.write at written
  cases checked : Access.validate before target with
  | error failure => simp [checked, Bind.bind, Except.bind] at written
  | ok _ =>
      simp only [checked, Bind.bind, Except.bind] at written
      split at written
      · rename_i same
        refine ⟨same ▸ value.value, ?_, written⟩
        rcases value with ⟨type, scalar⟩
        cases same
        rfl
      · cases written

theorem ScalarCopyRule.actions {owner : BitVec 160}
    (region : target.reference.region = .storage owner)
    (copied : ScalarCopyRule budget source target before events after) :
    ∃ value : target.type.Value,
      StorageActions before [.scalar owner target value] after.1 ∧
      ∃ sourceValue, Access.read before source = .ok sourceValue ∧
        convertScalar target.type sourceValue = .ok ⟨target.type, value⟩ := by
  cases copied with
  | step _ _ _ _ read conversion written _ =>
      obtain ⟨value, rfl, stored⟩ := access_write_scalar written
      exact ⟨value, .scalar region stored (.nil _), _, read, conversion⟩

theorem CopyFold.actions (project : σ → Heap)
    (law : ∀ before item events after, relation before item events after →
      ∃ actions, StorageActions (project before) actions (project after))
    (copied : CopyFold relation before items events after) :
    ∃ actions, StorageActions (project before) actions (project after) := by
  induction copied with
  | nil => exact ⟨[], .nil _⟩
  | cons step _ ih =>
      obtain ⟨initial, first⟩ := law _ _ _ _ step
      obtain ⟨final, last⟩ := ih
      exact ⟨initial ++ final, first.append last⟩

theorem StorageArrayRule.actions
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      ∃ actions, StorageActions heap actions after.1)
    (copied : StorageArrayRule child registry fuel budget source target a b before events after) :
    ∃ actions, StorageActions before actions after.1 := by
  cases copied with
  | scalars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ resizeTrace _ _ _ _ copied =>
      exact ⟨_, (StorageActions.ofTrace resizeTrace).append (.ofTrace copied.trace)⟩
  | references _ _ _ _ _ _ _ _ _ _ _ resizeTrace _ _ copied =>
      obtain ⟨actions, tail⟩ := copied.actions Prod.fst (by
        intro _ _ _ _ step
        cases step with | step _ _ _ _ _ _ copied => exact law _ _ _ _ _ _ copied)
      exact ⟨_, (StorageActions.ofTrace resizeTrace).append tail⟩

theorem StorageStructRule.actions
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      ∃ actions, StorageActions heap actions after.1)
    (copied : StorageStructRule child registry fuel budget source target a b before events after) :
    ∃ actions, StorageActions before actions after.1 := by
  cases copied with
  | step _ _ _ _ _ _ _ copied =>
      exact copied.actions Prod.fst (by
        intro _ _ _ _ step
        cases step with | step _ _ _ _ _ _ copied => exact law _ _ _ _ _ _ copied)

theorem StorageBodyRule.actions {owner : BitVec 160}
    (region : target.reference.region = .storage owner)
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      ∃ actions, StorageActions heap actions after.1)
    (copied : StorageBodyRule child registry fuel budget source target before events after) :
    ∃ actions, StorageActions before actions after.1 := by
  cases copied with
  | array _ copied => exact copied.actions law
  | «structure» _ copied => exact copied.actions law
  | bytes _ copied => exact ⟨_, .ofTrace copied.trace⟩
  | scalar _ copied =>
      obtain ⟨_, actions, _⟩ := copied.actions region
      exact ⟨_, actions⟩

theorem StorageCopyRule.actions (registry : Registry) (fuel : Nat) :
    ∀ budget before source target events after,
      StorageCopyRule registry fuel budget before source target events after →
      ∃ actions, StorageActions before actions after.1 := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ impossible; exact False.elim impossible
  | succ fuel ih =>
      intro budget before source target events after copied
      rcases copied with ⟨_, _, _, _, _, region, self | ⟨_, copied⟩⟩
      · rcases self with ⟨_, _, _, rfl, rfl⟩; exact ⟨[], .nil _⟩
      · exact copied.actions region ih

theorem ImmutableArrayRule.actions
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      ∃ actions, StorageActions heap actions after.1)
    (copied : ImmutableArrayRule child registry fuel budget source target element before events after) :
    ∃ actions, StorageActions before actions after.1 := by
  cases copied with
  | scalars _ _ _ _ _ _ _ _ _ _ _ _ resizeTrace _ copied =>
      exact ⟨_, (StorageActions.ofTrace resizeTrace).append (.ofTrace copied.trace)⟩
  | references _ _ _ _ _ _ _ _ _ _ _ resizeTrace _ copied =>
      obtain ⟨actions, tail⟩ := copied.actions Prod.fst (by
        intro _ _ _ _ step
        cases step with | step _ _ _ _ _ _ copied => exact law _ _ _ _ _ _ copied)
      exact ⟨_, (StorageActions.ofTrace resizeTrace).append tail⟩

theorem ImmutableStructRule.actions
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      ∃ actions, StorageActions heap actions after.1)
    (copied : ImmutableStructRule child registry fuel budget source target a b before events after) :
    ∃ actions, StorageActions before actions after.1 := by
  cases copied with
  | step _ _ _ _ _ _ _ copied =>
      exact copied.actions Prod.fst (by
        intro _ _ _ _ step
        cases step with | step _ _ _ _ _ _ copied => exact law _ _ _ _ _ _ copied)

theorem ImmutableBodyRule.actions {owner : BitVec 160}
    (region : target.reference.region = .storage owner)
    (law : ∀ budget heap source target events after, child budget heap source target events after →
      ∃ actions, StorageActions heap actions after.1)
    (copied : ImmutableBodyRule child registry fuel budget source target before events after) :
    ∃ actions, StorageActions before actions after.1 := by
  cases copied with
  | array _ copied => exact copied.actions law
  | «structure» _ copied => exact copied.actions law
  | bytes _ copied => exact ⟨_, .ofTrace copied.trace⟩
  | scalar _ copied =>
      obtain ⟨_, actions, _⟩ := copied.actions region
      exact ⟨_, actions⟩

theorem CopyToStorageRule.actions (registry : Registry) (fuel : Nat) :
    ∀ budget before source target events after,
      CopyToStorageRule registry fuel budget before source target events after →
      ∃ actions, StorageActions before actions after.1 := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ impossible; exact False.elim impossible
  | succ fuel ih =>
      intro budget before source target events after copied
      rcases copied with ⟨_, _, _, region, ⟨_, _, copied⟩ | ⟨_, copied⟩⟩
      · exact StorageCopyRule.actions registry (fuel+1) _ _ _ _ _ _ copied
      · exact copied.actions region ih

/-- Successful recursive copies yield a checked ordered traversal and a
physical action refinement to which scalar/packet read-back laws apply. -/
theorem copyStorage_actions
    (copied : copyStorage registry fuel budget before source target = .ok after) :
    ∃ events actions, StorageCopyRule registry fuel budget before source target events after ∧
      StorageActions before actions after.1 := by
  obtain ⟨events, rule⟩ := (copyStorage_iff registry fuel _ _ _ _ _).mp copied
  obtain ⟨actions, trace⟩ := StorageCopyRule.actions registry fuel _ _ _ _ _ _ rule
  exact ⟨events, actions, rule, trace⟩

theorem copyToStorage_actions
    (copied : copyToStorage registry fuel budget before source target = .ok after) :
    ∃ events actions, CopyToStorageRule registry fuel budget before source target events after ∧
      StorageActions before actions after.1 := by
  obtain ⟨events, rule⟩ := (copyToStorage_iff registry fuel _ _ _ _ _).mp copied
  obtain ⟨actions, trace⟩ := CopyToStorageRule.actions registry fuel _ _ _ _ _ _ rule
  exact ⟨events, actions, rule, trace⟩

/-- Unconditional raw-store representation of the complete recursive copy.
The derivation supplies the exact helper traversal and produced packets; every
physical collision is retained by the ordered last-store fold. Disjointness is
needed only for the separate noninterference/read-back corollaries. -/
theorem copyStorage_store_representation
    (copied : copyStorage registry fuel budget before source target = .ok after) :
    ∃ events, StorageCopyRule registry fuel budget before source target events after ∧
      StorageFrame before after.1 ∧
      (∀ account slot, after.1.execution.world.storage account slot =
        events.foldl (StorageEvent.persistent account slot) (before.execution.world.storage account slot)) ∧
      (∀ account slot, after.1.execution.world.transient account slot =
        events.foldl (StorageEvent.transient account slot) (before.execution.world.transient account slot)) := by
  obtain ⟨events, rule, trace⟩ := copyStorage_trace copied
  exact ⟨events, rule, trace.frame, trace.persistent, trace.transient⟩

theorem copyToStorage_store_representation
    (copied : copyToStorage registry fuel budget before source target = .ok after) :
    ∃ events, CopyToStorageRule registry fuel budget before source target events after ∧
      StorageFrame before after.1 ∧
      (∀ account slot, after.1.execution.world.storage account slot =
        events.foldl (StorageEvent.persistent account slot) (before.execution.world.storage account slot)) ∧
      (∀ account slot, after.1.execution.world.transient account slot =
        events.foldl (StorageEvent.transient account slot) (before.execution.world.transient account slot)) := by
  obtain ⟨events, rule, trace⟩ := copyToStorage_trace copied
  exact ⟨events, rule, trace.frame, trace.persistent, trace.transient⟩

end Solidity.Aggregates.Copy
