/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Memory

namespace Solidity.Aggregates.MemoryOps.Tests
open Static
open Contract.Interaction (Memory bytesWord wordBytes)

set_option maxRecDepth 8192

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def allocationObservation (heap : Heap) (budget size : Nat) :
    Result (Nat × Nat × Nat × List UInt8 × Nat) := do
  let (reference, after, remaining) ← allocate heap budget size
  return (reference.address.toNat, after.nextMemory, remaining,
    after.execution.memory.read reference.address.toNat size,
    (bytesWord (after.execution.memory.read 64 32)).toNat)

example : roundedSize 0 = 0 := rfl
example : roundedSize 1 = 32 := by decide +kernel
example : roundedSize 32 = 32 := by decide +kernel
example : roundedSize 33 = 64 := by decide +kernel
example : allocationObservation initialHeap 64 1 = .ok (128, 160, 0, [0], 160) := by decide +kernel
example : allocationObservation initialHeap 32 0 = .ok (128, 128, 0, [], 128) := by decide +kernel
example : allocationObservation initialHeap 63 1 = .error .exhausted := by decide +kernel
example : allocationObservation { initialHeap with nextMemory := 129 } 100 1 =
    .error (.invalidContext "invalid memory allocation context") := by decide +kernel

private def matchedFrontier (frontier : Nat) : Heap :=
  let heap := initialHeap
  { heap with nextMemory := frontier, execution := { heap.execution with
      memory := heap.execution.memory.write 64 (wordBytes (BitVec.ofNat 256 frontier)) } }

example : allocationObservation (matchedFrontier (2^64 - 32)) 0 1 =
    .error (.panic 0x41) := by decide +kernel
example : allocationObservation { initialHeap with nextMemory := 160 } 100 1 =
    .error (.invalidContext "invalid memory allocation context") := by decide +kernel
example : allocationObservation (matchedFrontier (2^256+128)) 100 1 =
    .error (.invalidContext "invalid memory allocation context") := by decide +kernel

private def clobberedFreePointer : Heap :=
  let heap := initialHeap
  { heap with execution := { heap.execution with
      memory := heap.execution.memory.write 64 (wordBytes 512) } }

example : validFrontier clobberedFreePointer = true := by decide +kernel
example : validAllocationContext clobberedFreePointer = false := by decide +kernel
example : allocationObservation clobberedFreePointer 100 32 =
    .error (.invalidContext "invalid memory allocation context") := by decide +kernel
example : allocationObservation (matchedFrontier 512) 64 32 =
    .ok (512, 544, 0, List.replicate 32 0, 544) := by decide +kernel
example : arraySize (2^64) false true = .error (.panic 0x41) := by decide +kernel
example : arraySize 33 true true = .ok 96 := by decide +kernel
example : arraySize 3 false true = .ok 128 := by decide +kernel

private def dirtyHeap : Heap :=
  let heap := initialHeap
  let memory := heap.execution.memory.write 128 [1, 2, 3, 4, 5]
  { heap with execution := { heap.execution with memory }, nextMemory := 160, allocations := ⟨128, 32⟩ :: heap.allocations }

private def memoryReference (address : Nat) : Reference :=
  { region := .memory 0, address := BitVec.ofNat 256 address }

private def copyObservation (source destination size : Nat) : Result (List UInt8 × Nat) := do
  let (after, remaining) ← copyBytes dirtyHeap (size * 2)
    (memoryReference source) (memoryReference destination) size
  return (after.execution.memory.read 128 5, remaining)

example : copyObservation 128 129 4 = .ok ([1, 1, 2, 3, 4], 0) := by decide +kernel
example : copyObservation 129 128 4 = .ok ([2, 3, 4, 5, 5], 0) := by decide +kernel
example : copyObservation 128 128 5 = .ok ([1, 2, 3, 4, 5], 0) := by decide +kernel
example : copyObservation 128 159 2 = .error (.invalidContext "unallocated memory extent") := by decide +kernel

private def calldataHeap : Heap :=
  initialHeap { context := { calldata := [10, 20, 30, 40, 50] } }

private def calldataObservation (offset length : Nat) : Result (List UInt8 × Nat) := do
  let reference ← calldataView calldataHeap offset length
  readView calldataHeap length reference length

example : calldataObservation 2 3 = .ok ([30, 40, 50], 0) := by decide +kernel
example : calldataObservation 4 2 = .error (.revert []) := by decide +kernel
example : calldataObservation (2^256) 0 =
    .error (.invalidContext "calldata address exceeds word range") := by decide +kernel

private def sliceObservation (start stop size : Nat) : Result (List UInt8 × Nat) := do
  let reference ← calldataView calldataHeap 1 4
  let view ← slice calldataHeap reference start stop
  readView calldataHeap size view size

example : sliceObservation 1 3 2 = .ok ([30, 40], 0) := by decide +kernel
example : sliceObservation 1 3 3 = .error (.panic 0x32) := by decide +kernel
example : sliceObservation 3 1 0 = .error (.panic 0x32) := by decide +kernel
example : sliceObservation 0 5 0 = .error (.panic 0x32) := by decide +kernel

private def immutableDestination : Bool :=
  match copyBytes calldataHeap 0 (memoryReference 96)
      { region := .calldata 0, address := 0 } 0 with
  | .error .rejected => true
  | _ => false

example : immutableDestination = true := by decide +kernel

example : readView calldataHeap 0 { region := .storage 0, address := 0 } 1 =
    .error .rejected := by decide +kernel
example : readView calldataHeap 1 { region := .calldata 1, address := 0 } 1 =
    .error (.invalidContext "foreign calldata reference") := by decide +kernel

end Solidity.Aggregates.MemoryOps.Tests
