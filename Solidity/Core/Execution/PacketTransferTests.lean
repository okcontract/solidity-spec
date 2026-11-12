/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.PacketTransferLaws

namespace Solidity.Execution.PacketTransfers.Tests
open Static Core Aggregates
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }
private def failed : Aggregates.Result α → Option Failure
  | .error failure => some failure | .ok _ => none
private def answer : Aggregates.Result α → Option α
  | .ok value => some value | .error _ => none
private def numbers : Nat → Datum → List Nat
  | 0, _ => []
  | _ + 1, .atom ⟨.uint _, value⟩ | _ + 1, .atom ⟨.sint _, value⟩ |
      _ + 1, .atom ⟨.fixedBytes _, value⟩ => [value.toNat]
  | _ + 1, .atom _ => []
  | fuel + 1, .tuple values => values.flatMap (numbers fuel)
private def convertedNumbers (target : SType) (source : Datum) : Aggregates.Result (List Nat) := do
  let (value, _, _) ← transfer registry 16 100 MemoryOps.initialHeap .implicit target source
  return numbers 16 value

private def nestedTarget : SType := .tuple (.cons (.uint 1)
  (.cons (.tuple (.cons (.sint 1) (.cons (.fixedBytes 3) .nil))) .nil))
private def nestedSource : Datum := .tuple [
  .atom ⟨.uint 0, 255⟩, .tuple [.atom ⟨.sint 0, 255⟩, .atom ⟨.fixedBytes 0, 0xab⟩]]

example : answer (convertedNumbers nestedTarget nestedSource) = some [255,65535,0xab000000] := by decide +kernel
example : failed (convertedNumbers (.tuple .nil) nestedSource) = some .rejected := by decide +kernel
example : failed (convertedNumbers (.uint 1) (.tuple [.atom ⟨.uint 0, 1⟩])) = some .rejected := by decide +kernel
example : failed (transfer registry 16 100 MemoryOps.initialHeap (.explicit .ordinary)
    nestedTarget nestedSource) = some .rejected := by decide +kernel
example : failed (transfer registry 0 100 MemoryOps.initialHeap .implicit nestedTarget nestedSource) =
    some .exhausted := by decide +kernel
example : failed (transfer registry 1 100 MemoryOps.initialHeap .implicit nestedTarget nestedSource) =
    some .exhausted := by decide +kernel
example : answer (do
    let (value, _, _) ← transfer registry 1 100 MemoryOps.initialHeap .implicit (.tuple .nil) (.tuple [])
    return value.type == SType.tuple .nil) = some true := by decide +kernel
example : failed (transfer registry 16 100 MemoryOps.initialHeap .implicit (.tuple (.cons (.uint 0) .nil))
    (.tuple [.atom ⟨.uint 31, 1⟩])) = some .rejected := by decide +kernel

private def copiedReference : Aggregates.Result (Nat × Nat × Nat) := do
  let (heap, _) ← StorageBytes.writeChecked MemoryOps.initialHeap 1000 {region := .storage 0, address := 7} [1,2]
  let source : Datum := .tuple [.atom ⟨.bytes .storage false, {region := .storage 0, address := 7}⟩,
    .atom ⟨.uint 0, 4⟩]
  let target := SType.tuple (.cons (.bytes .memory true) (.cons (.uint 31) .nil))
  let (.tuple [.atom bytes, .atom ⟨.uint _, number⟩], after, _) ← transfer registry 16 1000 heap .implicit target source
    | throw .rejected
  let length ← Effects.length registry 16 after bytes
  let ⟨.uint _, length⟩ := length | throw .rejected
  return (length.toNat, number.toNat, (← Slot.read after (.storage 0) 7).toNat)

example : answer copiedReference = some (2,4,0x0102*2^240+4) := by decide +kernel

/-- Explicit physical boundary states distinguish component conversion order:
the invalid bytes header panics22; the reference-array allocation panics41. -/
private def orderedFailure (reverse : Bool) : Aggregates.Result (Datum × Heap × Nat) := do
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 7 1
  let heap ← Slot.write heap (.storage 0) 8 (BitVec.ofNat 256 (2^64))
  let bytes : Datum := .atom ⟨.bytes .storage false, {region := .storage 0, address := 7}⟩
  let array : Datum := .atom ⟨.array (.bytes .storage false) none .storage false, {region := .storage 0, address := 8}⟩
  let byteTarget := SType.bytes .memory true
  let arrayTarget := SType.array (.bytes .memory false) none .memory true
  let target := if reverse then .tuple (.cons arrayTarget (.cons byteTarget .nil))
    else .tuple (.cons byteTarget (.cons arrayTarget .nil))
  transfer registry 16 1000 heap .implicit target (if reverse then .tuple [array,bytes] else .tuple [bytes,array])

example : failed (orderedFailure false) = some (.panic 0x22) := by decide +kernel
example : failed (orderedFailure true) = some (.panic 0x41) := by decide +kernel

end Solidity.Execution.PacketTransfers.Tests
