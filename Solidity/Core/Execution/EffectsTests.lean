/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Effects

namespace Solidity.Execution.Effects.Tests
open Core Static Aggregates
open Contract.Interaction (Word)

set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none, contracts := fun _ => none,
  structures := fun _ => false, structFields := fun _ => none }

private def number (value : Value) : Aggregates.Result Nat :=
  match value with
  | ⟨.uint _, value⟩ | ⟨.fixedBytes _, value⟩ => .ok value.toNat
  | ⟨.sint _, value⟩ => .ok value.toNat
  | ⟨.bool, value⟩ => .ok (if value then 1 else 0)
  | _ => .error .rejected

private def failureOf (result : Aggregates.Result α) : Option Failure :=
  match result with | .ok _ => none | .error failure => some failure

example : failureOf (binary .unchecked (.arithmetic .div) ⟨.uint 0, 9⟩ ⟨.uint 0, 0⟩) =
    some (.panic 0x12) := by decide +kernel
example : failureOf (unary .unchecked .neg ⟨.uint 0, 1⟩) = some .rejected := by decide +kernel
example : failureOf (scalarCast (.explicit .ordinary) (.address true) ⟨.uint 31, 0⟩) =
    some .rejected := by decide +kernel

private def localUpdate (mode : ArithmeticMode) (post : Bool) : Aggregates.Result (Nat × Nat) := do
  let locals ← Locals.empty.declare ⟨0, .uint 0, none⟩ (some ⟨.uint 0, 255⟩)
  let (some result, locals, heap, _) ← updateCaptured registry 16 100 mode locals
    MemoryOps.initialHeap (.local 0 (.uint 0)) (.inc post) | throw .rejected
  return (← number result, ← number (← readCaptured registry 16 locals heap (.local 0 (.uint 0))))

example : failureOf (localUpdate .checked false) = some (.panic 0x11) := by decide +kernel
example : localUpdate .unchecked true = .ok (255, 0) := by decide +kernel
example : localUpdate .unchecked false = .ok (0, 0) := by decide +kernel

private def capturedIndex : Aggregates.Result (Nat × Nat × Nat) := do
  let source : Value := ⟨.array (.uint 0) (some 2) .storage false, {region := .storage 0, address := 7}⟩
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 7 0x0201
  let locals ← Locals.empty.declare ⟨0, .uint 31, none⟩ (some ⟨.uint 31, 0⟩)
  let target ← captureIndex registry 16 heap source (← readCaptured registry 16 locals heap (.local 0 (.uint 31)))
  let (locals, heap, _) ← writeCaptured registry 16 100 locals heap (.local 0 (.uint 31)) ⟨.uint 31, 1⟩
  let (locals, heap, _) ← writeCaptured registry 16 100 locals heap target ⟨.uint 0, 9⟩
  return (← number (← readIndex registry 16 locals heap source ⟨.uint 31, 0⟩),
    ← number (← readIndex registry 16 locals heap source ⟨.uint 31, 1⟩),
    ← number (← readCaptured registry 16 locals heap (.local 0 (.uint 31))))

example : capturedIndex = .ok (9, 2, 1) := by decide +kernel

private def memoryBindingReadback : Aggregates.Result (Nat × Bool) := do
  let (outer, heap, remaining) ← Defaults.newArray registry 16 10000 MemoryOps.initialHeap (.bytes .memory false) 1
  let target ← captureIndex registry 16 heap outer ⟨.uint 31, 0⟩
  let (source, heap, remaining) ← Defaults.newBytes remaining heap 3 false
  let (locals, heap, _) ← writeCaptured registry 16 remaining Locals.empty heap target source
  let assigned ← assignmentResult registry 16 locals heap target source
  let source ← asPlace source
  let assignedPlace ← asPlace assigned
  return (← number (← length registry 16 heap assigned), assignedPlace.reference.address == source.reference.address)

example : memoryBindingReadback = .ok (3, true) := by decide +kernel

private def clearDirtyBool : Aggregates.Result (Nat × Nat) := do
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 7 0x0102
  let target := Captured.heap ⟨.bool, {region := .storage 0, address := 7}⟩
  let (locals, heap, _) ← deleteCaptured registry 16 100 Locals.empty heap target
  return ((← Slot.read heap (.storage 0) 7).toNat, ← number (← readCaptured registry 16 locals heap target))

example : clearDirtyBool = .ok (0x0100, 0) := by decide +kernel

private def staleCaptured : Aggregates.Result Value := do
  let source : Value := ⟨.array (.uint 0) none .storage false, {region := .storage 0, address := 7}⟩
  let heap ← Slot.write MemoryOps.initialHeap (.storage 0) 7 1
  let target ← captureIndex registry 16 heap source ⟨.uint 31, 0⟩
  let (heap, _) ← pop registry 16 100 heap source
  readCaptured registry 16 Locals.empty heap target

example : (match staleCaptured with | .error (.undefinedBehavior _) => true | _ => false) = true := by decide +kernel

private def unsetReference : Aggregates.Result Value := do
  let type := SType.array (.uint 0) none .storage true
  let (locals, heap, _) ← declareLocal registry 16 100 Locals.empty MemoryOps.initialHeap ⟨0, type, none⟩ none
  readCaptured registry 16 locals heap (.local 0 type)

example : failureOf unsetReference = some (.invalidContext "uninitialized local reference") := by decide +kernel

private def mappingReturn : Aggregates.Result Nat := do
  let type := SType.mapping (.uint 31) (.uint 31)
  let (locals, heap, remaining) ← declareReturn registry 16 100 Locals.empty
    MemoryOps.initialHeap ⟨0, type, none⟩
  let (locals, heap, remaining) ← writeCaptured registry 16 remaining locals heap
    (.local 0 type) ⟨type, {region := .storage 0, address := 7}⟩
  let (target, remaining) ← captureMapping registry 16 remaining heap
    (← readCaptured registry 16 locals heap (.local 0 type)) ⟨.uint 31, 4⟩
  let (locals, heap, _) ← writeCaptured registry 16 remaining locals heap target ⟨.uint 31, 9⟩
  number (← readCaptured registry 16 locals heap target)

example : mappingReturn = .ok 9 := by decide +kernel
example : failureOf (declareLocal registry 16 100 Locals.empty MemoryOps.initialHeap
    ⟨0, .mapping (.uint 31) (.uint 31), none⟩ none) = some .rejected := by decide +kernel
example : failureOf (do
    let type := SType.mapping (.uint 31) (.uint 31)
    let (locals, heap, _) ← declareReturn registry 16 100 Locals.empty MemoryOps.initialHeap ⟨0, type, none⟩
    readCaptured registry 16 locals heap (.local 0 type)) =
    some (.invalidContext "uninitialized local reference") := by decide +kernel

private def mappingAddress (keyType : SType) (key : Value) : Aggregates.Result Nat := do
  let source : Value := ⟨.mapping keyType (.uint 31), {region := .storage 0, address := 7}⟩
  let (place, _) ← mapping registry 16 100 MemoryOps.initialHeap source key
  return place.reference.address.toNat

example : mappingAddress (.uint 31) ⟨.uint 0, 4⟩ =
    .ok (Contract.Interaction.mappingKey 4 7).toNat := by decide +kernel
example : mappingAddress (.sint 31) ⟨.sint 0, 255⟩ =
    .ok (Contract.Interaction.mappingKey (BitVec.ofInt 256 (-1)) 7).toNat := by decide +kernel
example : mappingAddress (.fixedBytes 3) ⟨.fixedBytes 0, 0xab⟩ =
    .ok (Contract.Interaction.mappingKey (BitVec.ofNat 256 0xab <<< 248) 7).toNat := by decide +kernel
example : failureOf (mappingAddress (.uint 0) ⟨.uint 31, 4⟩) = some .rejected := by decide +kernel

private def rejectDeleteValueType : Aggregates.Result (Locals × Heap × Nat) := do
  let type := SType.valueType 0 (.scalar (.uint 0))
  let locals ← Locals.empty.declare ⟨0, type, none⟩ (some ⟨type, 0#8⟩)
  deleteCaptured registry 16 100 locals MemoryOps.initialHeap (.local 0 type)

example : failureOf rejectDeleteValueType = some .rejected := by decide +kernel

example : readIndex registry 16 Locals.empty MemoryOps.initialHeap
    ⟨.fixedBytes 3, 0x11223344⟩ ⟨.uint 31, 0⟩ >>= number = .ok 0x11 := by decide +kernel
example : failureOf (readIndex registry 16 Locals.empty MemoryOps.initialHeap
    ⟨.fixedBytes 3, 0x11223344⟩ ⟨.uint 31, 4⟩) = some (.panic 0x32) := by decide +kernel

example : (do
    let value ← length registry 16 MemoryOps.initialHeap ⟨.fixedBytes 0, 0xff⟩
    return (value.type == SType.uint 0, ← number value)) = .ok (true, 1) := by decide +kernel
example : (do
    let value ← length registry 16 MemoryOps.initialHeap ⟨.fixedBytes 31, 0⟩
    return (value.type == SType.uint 0, ← number value)) = .ok (true, 32) := by decide +kernel

private def logWords : Aggregates.Result (Nat × Nat × Nat) := do
  let heap ← emitWords MemoryOps.initialHeap [⟨.bool, true⟩] [⟨.sint 0, 255⟩, ⟨.fixedBytes 0, 0xab⟩]
  let some event := heap.execution.world.logs[0]? | throw .rejected
  return (event.data.length, (event.topics[0]?).getD 0 |>.toNat, (event.data[32]?).getD 0 |>.toNat)

example : logWords = .ok (64, 1, 0xab) := by decide +kernel
example : failureOf (emit (MemoryOps.initialHeap {context := {readOnly := true}}) [] []) =
    some .exceptional := by decide +kernel

end Solidity.Execution.Effects.Tests
