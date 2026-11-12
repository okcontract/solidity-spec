/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.DefaultAliasing

namespace Solidity.Aggregates.Defaults.Representation.Tests
open Static
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

private def registry : Registry := {
  enumerations := fun _ => none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun _ => false }

private def answer : Result α → Option α
  | .ok value => some value
  | .error _ => none

private def emptyArrayRoots : Result (Nat × Nat) := do
  let (first, middle, _) ← newArray registry 8 10000 MemoryOps.initialHeap (.uint 0) 0
  let (second, _, _) ← newArray registry 8 10000 middle (.uint 0) 0
  return ((← asPlace first).reference.address.toNat, (← asPlace second).reference.address.toNat)

/-- Empty `new` arrays still own separate length headers. -/
example : answer emptyArrayRoots = some (128, 160) := by decide +kernel

private def defaultArrayRoots : Result (Nat × Nat) := do
  let type := SType.array (.uint 0) none .memory true
  let (first, middle, _) ← defaultValue registry 8 10000 MemoryOps.initialHeap type
  let (second, _, _) ← defaultValue registry 8 10000 middle type
  return ((← asPlace first).reference.address.toNat, (← asPlace second).reference.address.toNat)

/-- This is the negative boundary for an unconditional distinct-root claim. -/
example : answer defaultArrayRoots = some (96, 96) := by decide +kernel

private def copiedArrayRootsAndMutation : Result (Nat × Nat × Nat) := do
  let type := SType.array (.uint 0) (some 1) .memory true
  let contents := Contents.array (.uint 0) [.scalar ⟨.uint 0, 3⟩]
  let (first, middle, _) ← Copy.materializeMemory registry 8 10000 MemoryOps.initialHeap type contents
  let (second, after, _) ← Copy.materializeMemory registry 8 10000 middle type contents
  let left ← asPlace first
  let right ← asPlace second
  let after ← Access.write after (← Access.index registry 8 after left 0) ⟨.uint 0, 7⟩
  let value ← Access.read after (← Access.index registry 8 after right 0)
  match value with
  | ⟨.uint _, word⟩ => return (left.reference.address.toNat, right.reference.address.toNat, word.toNat)
  | _ => throw .rejected

example : answer copiedArrayRootsAndMutation = some (128, 160, 3) := by decide +kernel

example (old : Object registry middle lower oldType oldAddress oldContents)
    (valid : MemoryOps.validFrontier middle = true)
    (next : Object registry after middle.nextMemory type address contents)
    (nonshared : address ≠ 96) (nonempty : 0 < rootSpan oldType oldContents) :
    oldAddress ≠ address := old.staged_nonshared_distinct next valid nonshared nonempty

end Solidity.Aggregates.Defaults.Representation.Tests
