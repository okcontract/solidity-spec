/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Mutation

namespace Solidity.Aggregates.Mutation.Tests
open Core Static
open Contract.Interaction (Word)

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun a b =>
  match a, b with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ | .error _, .ok _ => isFalse (by intro h; cases h)

private def registry : Registry := {
  enumerations := fun _ => none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun id => id == 1 || id == 2
  structFields := fun id => if id == 1 then
    some [("small", .uint 0), ("alsoSmall", .uint 0)] else if id == 2 then
    some [("retained", .mapping (.uint 31) (.uint 31)), ("small", .uint 0)] else none }

private def root (type : SType) (slot : Word := 0) : Place :=
  ⟨type, {region := .storage 0, address := slot}⟩

private def rawHeap (word : Word) : Heap :=
  {execution := {world := ({} : Contract.Interaction.World).store 0 0 word}}

private def wordAt (heap : Heap) (slot : Word := 0) : Word :=
  heap.execution.world.storage 0 slot

example : (do let (after, _) ← delete registry 20 100 (rawHeap (BitVec.allOnes 256))
                (root (.structType 1 .storage false))
              pure (wordAt after)) = .ok 0 := by decide +kernel

example : (do let (after, _) ← delete registry 20 100 (rawHeap (BitVec.allOnes 256))
                (root (.array (.uint 0) (some 1) .storage false))
              pure (wordAt after)) = .ok 0 := by decide +kernel

-- A scalar deletion preserves adjacent dirty bytes.
example : (do let (after, _) ← delete registry 20 100 (rawHeap 0x0702) (root (.uint 0))
              pure (wordAt after)) = .ok 0x0700 := by decide +kernel

-- The mapping's hash-derived payload survives deletion of its enclosing struct.
private def mappingDelete : Result (Word × Word) := do
  let aggregate := root (.structType 2 .storage false)
  let field ← Access.field registry 20 (rawHeap 0) aggregate 0
  let target ← Access.mapping (rawHeap 0) field (.scalar ⟨.uint 31, 7⟩)
  let world := ((({} : Contract.Interaction.World).store 0 0 99).store 0 1 0xffff).store
    0 target.reference.address 42
  let heap : Heap := {execution := {world}}
  let (after, _) ← delete registry 20 1000 heap aggregate
  return (wordAt after 1, wordAt after target.reference.address)

example : mappingDelete = .ok (0, 42) := by decide +kernel

example : (delete registry 20 100 (rawHeap 1)
    (root (.array (.uint 0) none .storage true))).isOk = false := by decide +kernel
example : (delete registry 20 100 (rawHeap 1)
    (root (.valueType 1 (.scalar (.uint 0))))).isOk = false := by decide +kernel
example : (delete registry 20 100 (rawHeap 1)
    (root (.mapping (.uint 31) (.uint 31)))).isOk = false := by decide +kernel

private def array : Place := root (.array (.uint 0) none .storage false)

private def removeRegrow : Result Unit := do
  let (element, heap, _) ← pushZero registry 20 100 (rawHeap 0) array
  let (heap, _) ← pop registry 20 100 heap array
  let (_, heap, _) ← pushZero registry 20 100 heap array
  Access.validate heap element

example : removeRegrow = .error (.undefinedBehavior
    "dangling storage reference after element removal") := by decide +kernel

example : (pop registry 20 100 (rawHeap 0) array).isOk = false := by decide +kernel
example : (do let (heap, _) ← push registry 20 100 (rawHeap 0) array ⟨.uint 0, 9⟩
              let target ← Access.index registry 20 heap array 0
              let value ← Access.read heap target
              match value.type, value.value with
              | .uint _, value => pure value.toNat
              | _, _ => (throw Failure.rejected : Result Nat)) = .ok 9 := by decide +kernel

example : (push registry 20 100 (rawHeap 0) (root (.string .storage false))
    ⟨.fixedBytes 0, 9⟩).isOk = false := by decide +kernel
example : (push registry 20 100 (rawHeap 0) (root (.bytes .storage false))
    ⟨.uint 0, 9⟩).isOk = false := by decide +kernel

private def deleteMemoryMember : Result (Nat × Nat) := do
  let heap := MemoryOps.initialHeap
  let innerType := .array (.uint 0) none .memory false
  let (outer, heap, _) ← Defaults.newArray registry 20 10000 heap innerType 1 false
  let outer ← Defaults.asPlace outer
  let target ← Access.index registry 20 heap outer 0
  let (inner, heap, _) ← Defaults.newArray registry 20 10000 heap (.uint 0) 2 true
  let (heap, _) ← Copy.assign registry 20 10000 heap target inner
  let target ← Access.index registry 20 heap outer 0
  let (heap, _) ← delete registry 20 10000 heap target
  let current ← Access.index registry 20 heap outer 0
  let old ← Defaults.asPlace inner
  return (← Access.length heap current, ← Access.length heap old)

example : deleteMemoryMember = .ok (0, 2) := by decide +kernel

example : (do let (value, _, _) ← deleteValue registry 20 100
                MemoryOps.initialHeap (.bytes .memory true)
              let place ← Defaults.asPlace value
              pure place.reference.address.toNat) = .ok 96 := by decide +kernel

end Solidity.Aggregates.Mutation.Tests
