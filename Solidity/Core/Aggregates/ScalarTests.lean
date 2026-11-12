/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Scalars

namespace Solidity.Aggregates.Tests
open Static Core
open Contract.Interaction (Word bytesWord wordBytes)

set_option maxRecDepth 8192

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

-- A uint24 field leaves sixteen bits unused in each packed storage word.
example : Packed.extract 24 216 (Packed.insert 24 216 (BitVec.allOnes 256) 0x123456) = 0x123456 := by decide +kernel
example : (Packed.insert 24 216 (BitVec.allOnes 256) 0).getLsbD 255 = true := by decide +kernel
example : (Packed.insert 24 216 (BitVec.allOnes 256) 0).getLsbD 239 = false := by decide +kernel

example : decodeStorage .bool 2 = .error (.invalidContext "noncanonical storage boolean") := by decide +kernel
example : decodeMemory .bool 2 = .ok true := by decide +kernel
example : decodeCalldata .bool 2 = .error (.revert []) := by decide +kernel
example : decodeStorage (.enumType 1 1) 2 = .error (.invalidContext "out-of-range storage enum") := by decide +kernel
example : decodeMemory (.enumType 1 1) 2 = .error (.panic 0x21) := by decide +kernel
example : decodeCalldata (.enumType 1 1) 2 = .error (.revert []) := by decide +kernel
example : decodeCalldata (.uint 0) 256 = .error (.revert []) := by decide +kernel
example : decodeMemory (.uint 0) 256 = .ok 0 := by decide +kernel
example : decodeCalldata (.sint 0) 255 = .error (.revert []) := by decide +kernel
example : decodeCalldata (.sint 0) (BitVec.ofInt 256 (-1)) = .ok (BitVec.ofInt 8 (-1)) := by decide +kernel
example : decodeCalldata (.fixedBytes 0) 1 = .error (.revert []) := by decide +kernel
example : decodeCalldata (.fixedBytes 0) (1 <<< 248) = .ok 1 := by decide +kernel
example : encodeInternal 64 (some (2^64-1)) = .error (.invalidContext "internal function handle does not fit representation") := by decide +kernel
example : encodeInternal 64 none = .ok 0 := by decide +kernel
example : (encodeInternal 64 (some (2^64-2))).map decodeInternal = .ok (some (2^64-2)) := by decide +kernel

private def packedHeap : Heap := { execution := { world := { storage := fun _ _ => BitVec.allOnes 256 } } }
private abbrev packedPlace : Place := ⟨.uint 2, {region := .storage 0, address := 7, byte := 27}⟩
private def changedWord : Result Word := do
  let heap ← writeScalar packedHeap packedPlace (0x123456 : BitVec 24)
  Slot.read heap (.storage 0) 7
example : changedWord.map (fun (word : Word) => (word >>> 216).setWidth 24) = .ok (0x123456 : BitVec 24) := by decide +kernel
example : changedWord.map (fun word => word.getLsbD 255) = .ok true := by decide +kernel
example : (readScalar packedHeap packedPlace).map BitVec.toNat = .ok 0xffffff := by decide +kernel

private def byteHeap : Heap := {
  execution := { memory := fun i => if i == 128 then 0xab else 0x77 }
  allocations := [⟨128, 1⟩] }
private abbrev bytePlace : Place := ⟨.fixedBytes 0, {region := .memory 0, address := 128, byteCell := true}⟩
example : readScalar byteHeap bytePlace = .ok 0xab := by decide +kernel
example : (do let heap ← writeScalar byteHeap bytePlace 0x12
              pure (heap.execution.memory 128, heap.execution.memory 129)) = .ok (0x12, 0x77) := by decide +kernel
example : readScalar byteHeap ⟨.uint 31, {region := .memory 0, address := 128}⟩ =
    .error (.invalidContext "unallocated memory extent") := by decide +kernel
example : readScalar byteHeap ⟨.uint 0, {region := .memory 0, address := 128, byteCell := true}⟩ =
    .error .rejected := by decide +kernel
example : readScalar byteHeap ⟨.fixedBytes 0, {region := .memory 1, address := 128, byteCell := true}⟩ =
    .error (.invalidContext "foreign memory reference") := by decide +kernel

private def calldataHeap : Heap := { execution := { context := { calldata := wordBytes 257 } } }
example : readScalar calldataHeap ⟨.uint 0, {region := .calldata 0, address := 0}⟩ =
    .error (.revert []) := by decide +kernel
example : readScalar calldataHeap ⟨.uint 31, {region := .calldata 0, address := 1}⟩ =
    .error (.revert []) := by decide +kernel

-- Recognized fixed-point types remain an execution boundary, not a source error.
example : decodeStorage (.fixedPoint false 15 18) 0 =
    .error (.unsupported "fixed-point storage decoding") := by decide +kernel
example : decodeMemory (.fixedPoint true 31 18) 0 =
    .error (.unsupported "fixed-point memory decoding") := by decide +kernel
example : decodeCalldata (.fixedPoint false 15 18) 0 =
    .error (.unsupported "fixed-point memory decoding") := by decide +kernel
example (value : (SType.fixedPoint false 15 18).Value) :
    encodeStorage (.fixedPoint false 15 18) value =
      .error (.unsupported "fixed-point storage encoding") := rfl
example (value : (SType.fixedPoint true 31 18).Value) :
    encodeMemory (.fixedPoint true 31 18) value =
      .error (.unsupported "fixed-point memory encoding") := rfl
example : readScalar ({} : Heap) ⟨.fixedPoint false 15 18, {region := .storage 0, address := 0}⟩ =
    .error (.unsupported "fixed-point storage decoding") := by decide +kernel

end Solidity.Aggregates.Tests
