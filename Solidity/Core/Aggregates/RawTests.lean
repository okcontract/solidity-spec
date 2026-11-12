/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Raw
import Solidity.Core.Aggregates.StorageArrays

namespace Solidity.Aggregates.Raw.Tests
open Static

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun a b =>
  match a, b with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ | .error _, .ok _ => isFalse (by intro h; cases h)

private def registry : Registry := {
  enumerations := fun _ => none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun _ => false }

private def root : Place :=
  ⟨.array (.uint 0) none .storage false, {region := .storage 0, address := 0}⟩

private def populated : Heap :=
  {execution := {world := ({} : Contract.Interaction.World).store 0 0 1}}

private def oldAfterRawRegrow : Result Unit := do
  let old ← Access.index registry 8 populated root 0
  let heap ← write populated (.storage 0) 0 0
  let heap ← write heap (.storage 0) 0 1
  Access.validate heap old

example : oldAfterRawRegrow = .error
    (.invalidContext "storage reference lifetime history invalidated by raw transition") := by decide +kernel

private def recapturedAfterRawRegrow : Result Unit := do
  let heap ← write populated (.storage 0) 0 0
  let heap ← write heap (.storage 0) 0 1
  let fresh ← Access.index registry 8 heap root 0
  Access.validate heap fresh

example : recapturedAfterRawRegrow = .ok () := by decide +kernel

private def typedRemovalStillDangling : Result Unit := do
  let old ← Access.index registry 8 populated root 0
  let (heap, _) ← StorageArrays.pop registry 8 100 populated root
  let (_, heap, _) ← StorageArrays.pushZero registry 8 100 heap root
  Access.validate heap old

example : typedRemovalStillDangling = .error
    (.undefinedBehavior "dangling storage reference after element removal") := by decide +kernel

private def identicalWorldReplacement : Result Unit := do
  let old ← Access.index registry 8 populated root 0
  Access.validate (replaceWorld populated populated.execution.world) old

example : identicalWorldReplacement = .error
    (.invalidContext "storage reference lifetime history invalidated by raw transition") := by decide +kernel

example : (replaceWorld populated populated.execution.world).historyEpoch (.memory 7) = 0 := rfl
example : (replaceWorld populated populated.execution.world).historyEpoch (.calldata 7) = 0 := rfl
example : (replaceWorld populated populated.execution.world).historyEpoch (.storage 1) = 1 := rfl
example : (replaceWorld populated populated.execution.world).historyEpoch (.transient 1) = 1 := rfl

example : (do let heap ← write populated (.transient 0) 0 1
              pure (heap.historyEpoch (.storage 0), heap.historyEpoch (.transient 0))) = .ok (0, 1) := by decide +kernel

example : (do let heap ← Slot.write populated (.storage 0) 0 9
              pure (heap.historyEpoch (.storage 0))) = .ok 0 := by decide +kernel

example : (write {populated with execution := {populated.execution with context := {readOnly := true}}}
    (.storage 0) 0 0).isOk = false := by decide +kernel

end Solidity.Aggregates.Raw.Tests
