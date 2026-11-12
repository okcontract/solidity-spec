/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy

namespace Solidity.Aggregates.CopySource.Tests
open Static
open Contract.Interaction (Word wordBytes)

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ | .error _, .ok _ => isFalse (by intro h; cases h)

private def registry : Registry := {
  enumerations := fun id => if id == 17 then some 1 else none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun id => id == 1
  structFields := fun id => if id == 1 then
    some [("tag", .enumType 17 1), ("value", .uint 31)] else none }

private def atFrontier (heap : Heap) (frontier : Nat) : Heap :=
  {heap with nextMemory := frontier, execution := {heap.execution with
    memory := heap.execution.memory.write 64 (wordBytes (BitVec.ofNat 256 frontier))}}

private def calldataHeap (words : List Word) : Heap :=
  MemoryOps.initialHeap {context := {calldata := words.flatMap wordBytes}}

private def source (type : SType) (region : Region) : Value :=
  match type with
  | .array element size location pointer => ⟨.array element size location pointer, {region, address := 0}⟩
  | .structType identity location pointer => ⟨.structType identity location pointer, {region, address := 0}⟩
  | .bytes location pointer => ⟨.bytes location pointer, {region, address := 0}⟩
  | _ => ⟨.uint 31, 0⟩

private def copyFailure (heap : Heap) (type : SType) (region : Region) : Result Unit :=
  (Copy.bind registry 24 10000 heap (atLocation type .memory true) (source type region)).map (fun _ => ())

private def smallArray : SType := .array (.uint 0) none .calldata true

-- Production calldata available-length decoding allocates before inspecting
-- the complete array extent or validating the first scalar word.
example : copyFailure (atFrontier (calldataHeap [1, 256]) (2^64-32)) smallArray (.calldata 0) =
    .error (.panic 0x41) := by decide +kernel
example : copyFailure (atFrontier (calldataHeap [1]) (2^64-32)) smallArray (.calldata 0) =
    .error (.panic 0x41) := by decide +kernel
example : copyFailure (calldataHeap [1]) smallArray (.calldata 0) =
    .error (.revert []) := by decide +kernel
example : copyFailure (calldataHeap [1, 256]) smallArray (.calldata 0) =
    .error (.revert []) := by decide +kernel

private def tagged : SType := .structType 1 .calldata true

-- Struct decoding checks its full head before allocating, then allocates
-- before validating members. These two failures must not exchange priority.
example : copyFailure (atFrontier (calldataHeap [2]) (2^64-32)) tagged (.calldata 0) =
    .error (.revert []) := by decide +kernel
example : copyFailure (atFrontier (calldataHeap [2, 0]) (2^64-32)) tagged (.calldata 0) =
    .error (.panic 0x41) := by decide +kernel

private def storageHeap (element : Word) : Heap :=
  let world := (({} : Contract.Interaction.World).store 0 0 1).store
    0 (Access.hash (wordBytes 0)) element
  MemoryOps.initialHeap {world}

private def storageStructHeap : Heap :=
  MemoryOps.initialHeap {world := ({} : Contract.Interaction.World).store 0 0 2}

-- Storage scalar arrays read through the unbounded ABI encoder before its
-- final allocation check; storage reference arrays allocate their root first.
example : copyFailure (atFrontier (storageHeap 2) (2^64-32))
    (.array (.enumType 17 1) none .storage false) (.storage 0) =
    .error (.invalidContext "out-of-range storage enum") := by decide +kernel
example : copyFailure (atFrontier (storageHeap 2) (2^64-32))
    (.array (.structType 1 .storage false) none .storage false) (.storage 0) =
    .error (.panic 0x41) := by decide +kernel
example : copyFailure (atFrontier storageStructHeap (2^64-32))
    (.structType 1 .storage false) (.storage 0) = .error (.panic 0x41) := by decide +kernel

-- Child allocation is interleaved with decoding. The first empty child's
-- allocation fails before the malformed offset of the second child is read.
example : copyFailure (atFrontier (calldataHeap [2, 64, BitVec.ofNat 256 (2^64), 0]) (2^64-128))
    (.array (.array (.uint 0) none .calldata false) none .calldata true) (.calldata 0) =
    .error (.panic 0x41) := by decide +kernel

private def copied : Result (Nat × Nat) := do
  let (value, heap, _) ← Copy.bind registry 24 10000 (calldataHeap [1, 7])
    (.array (.uint 0) none .memory true) (source smallArray (.calldata 0))
  let array ← Defaults.asPlace value
  let cell ← Access.index registry 24 heap array 0
  let value ← Access.read heap cell
  match value with
  | ⟨.uint _, value⟩ => return (← Access.length heap array, value.toNat)
  | _ => throw .rejected

example : copied = .ok (1, 7) := by decide +kernel

end Solidity.Aggregates.CopySource.Tests
