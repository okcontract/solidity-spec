/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.ReferenceCastProofs

namespace Solidity.Aggregates.ReferenceCasts.Tests
open Core Static
open Contract.Interaction (Word bytesWord)

set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false, structFields := fun _ => none }

private def number (value : Value) : Result Nat :=
  match value with | ⟨.fixedBytes _, word⟩ => .ok word.toNat | _ => .error .rejected

private def memoryPrefix (length : Nat) (payload : List UInt8) (width : Width := 3) : Result (Nat × Nat) := do
  let (source, heap, _) ← Defaults.newBytes 10000 MemoryOps.initialHeap length false
  let place ← Defaults.asPlace source
  let heap := {heap with execution := {heap.execution with
    memory := heap.execution.memory.write (place.reference.address.toNat+32) payload}}
  let (value, remaining) ← cast registry 16 100 heap (.fixedBytes width) source
  return (← number value, remaining)

-- The unused dirty bytes cannot enter this typed conversion.
example : memoryPrefix 1 [0x11, 0xff, 0xee, 0xdd] = .ok (0x11000000, 98) := by decide +kernel
example : memoryPrefix 0 [0xff, 0xff, 0xff, 0xff] = .ok (0, 99) := by decide +kernel
example : memoryPrefix 33 [1, 2, 3, 4, 0xff] = .ok (0x01020304, 95) := by decide +kernel

private def storagePrefix : Result Nat := do
  let raw : Word := (0x11 <<< 248) ||| (0xff <<< 240) ||| 2
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 7 raw
  let (value, _) ← cast registry 16 100 heap (.fixedBytes 3)
    ⟨.bytes .storage false, {region := .storage 0, address := 7}⟩
  number value

example : storagePrefix = .ok 0x11000000 := by decide +kernel

private def calldataPrefix : Result Nat := do
  let heap := MemoryOps.initialHeap {context := {calldata := [0x11, 0xff, 0xee, 0xdd]}}
  let (value, _) ← cast registry 16 100 heap (.fixedBytes 3)
    ⟨.bytes .calldata true, {region := .calldata 0, address := 0, viewLength := some 1}⟩
  number value

example : calldataPrefix = .ok 0x11000000 := by decide +kernel

private def memoryAlias : Result Nat := do
  let (source, heap, _) ← Defaults.newBytes 1000 MemoryOps.initialHeap 1 false
  let original ← Defaults.asPlace source
  let (text, _) ← cast registry 16 0 heap (.string .memory false) source
  let (bytes, _) ← cast registry 16 0 heap (.bytes .memory false) text
  let alias ← Defaults.asPlace bytes
  let cell ← Access.index registry 16 heap alias 0
  let heap ← Access.write heap cell ⟨.fixedBytes 0, 0x7a⟩
  number (← Access.read heap (← Access.index registry 16 heap original 0))

example : memoryAlias = .ok 0x7a := by decide +kernel

private def sliceAlias : Result (Nat × Nat × Nat × Nat) := do
  let heap := MemoryOps.initialHeap {context := {calldata := [1, 2, 3, 4]}}
  let source : Place := ⟨.bytes .calldata true,
    {region := .calldata 0, address := 0, viewLength := some 4}⟩
  let source ← Access.slice registry 16 heap source 1 3
  let (text, remaining) ← cast registry 16 0 heap (.string .calldata false) (← source.asValue)
  let (bytes, _) ← cast registry 16 remaining heap (.bytes .calldata false) text
  let alias ← Defaults.asPlace bytes
  return (alias.reference.address.toNat, alias.reference.viewLength.getD 0,
    (alias.reference.relativeBase.getD 7).toNat,
    ← number (← Access.read heap (← Access.index registry 16 heap alias 0)))

example : sliceAlias = .ok (1, 2, 0, 2) := by decide +kernel

example : select (.bytes .memory false) (.string .calldata false) = none := rfl
example : select (.array (.uint 0) none .memory false) (.string .memory false) = none := rfl
example : select (.string .memory false) (.fixedBytes 3) = none := rfl
example : select (.array (.uint 0) none .memory false)
    (.array (.uint 1) none .memory false) = none := rfl
example : select (.array (.uint 31) none .calldata true)
    (.array (.uint 31) none .calldata false) = some .alias := rfl
example : resolveTarget (.string .calldata false) (.bytes .memory true) =
    .ok (.string .memory true) := rfl

private def failureOf (result : Result α) : Option Failure :=
  match result with | .ok _ => none | .error error => some error

example : failureOf (cast registry 16 0 MemoryOps.initialHeap (.string .storage false)
    ⟨.bytes .storage false, {region := .transient 0, address := 0}⟩) = some .rejected := by decide +kernel

example : failureOf (toFixedBytes registry 16 0
    (MemoryOps.initialHeap {context := {calldata := []}})
    ⟨.bytes .calldata true, {region := .calldata 0, address := 0, viewLength := some 0}⟩ 3) =
      some .exhausted := by decide +kernel

end Solidity.Aggregates.ReferenceCasts.Tests
