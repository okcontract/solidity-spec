/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.StorageBytes

namespace Solidity.Aggregates.StorageBytes.Tests
open Core Static
open Contract.Interaction (Word)

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def root : Reference := {region := .storage 0, address := 1}
private def heapWithHeader (word : Word) : Heap := {
  execution := {world := {storage := fun account slot => if account = 0 && slot = 1 then word else 0}} }

private def roundtrip (bytes : List UInt8) : Result (List UInt8) := do
  let (after, _) ← write {} 4096 root bytes
  return (← read after 4096 root).1

example : roundtrip [] = .ok [] := by decide +kernel
example : roundtrip [0, 1, 255] = .ok [0, 1, 255] := by decide +kernel
example : roundtrip (List.replicate 31 0xab) = .ok (List.replicate 31 0xab) := by decide +kernel
example : roundtrip (List.replicate 32 0xab) = .ok (List.replicate 32 0xab) := by decide +kernel
example : roundtrip (List.replicate 33 0xab) = .ok (List.replicate 33 0xab) := by decide +kernel
example : roundtrip (List.replicate 64 0xcd) = .ok (List.replicate 64 0xcd) := by decide +kernel
example : roundtrip (List.replicate 65 0xef) = .ok (List.replicate 65 0xef) := by decide +kernel

example : Access.byteLength 64 = .error (.panic 0x22) := by decide +kernel
example : Access.byteLength 1 = .error (.panic 0x22) := by decide +kernel
example : Access.byteLength 63 = .error (.panic 0x22) := by decide +kernel
example : read (heapWithHeader 64) 4096 root = .error (.panic 0x22) := by decide +kernel
example : read (heapWithHeader 1) 4096 root = .error (.panic 0x22) := by decide +kernel

example : (write {} 0 root []).map (fun _ => ()) = .error .exhausted := by decide +kernel
example : read {} 0 root = .error .exhausted := by decide +kernel
example : (pop {} 0 root).map (fun _ => ()) = .error (.panic 0x31) := by decide +kernel
example : (write {execution := {context := {readOnly := true}}} 8 root []).map (fun _ => ()) =
    .error .exceptional := by decide +kernel
example : (push {execution := {context := {readOnly := true}}} 8 root 7).map (fun _ => ()) =
    .error .exceptional := by decide +kernel

private def shrink (old new : List UInt8) : Result (List UInt8 × Word × Word × Word) := do
  let (before, _) ← write {} 4096 root old
  let (after, _) ← write before 4096 root new
  return ((← read after 4096 root).1, after.execution.world.storage 0 (dataSlot root 0),
    after.execution.world.storage 0 (dataSlot root 1), after.execution.world.storage 0 (dataSlot root 2))

example : shrink (List.replicate 64 0xff) [0x11] = .ok ([0x11], 0, 0, 0) := by decide +kernel
example : shrink (List.replicate 65 0xff) [] = .ok ([], 0, 0, 0) := by decide +kernel
example : (shrink (List.replicate 65 0xff) (List.replicate 33 0xab)).map
    (fun result => (result.1, result.2.2.1 &&& BitVec.ofNat 256 (2^248-1), result.2.2.2)) =
    .ok (List.replicate 33 0xab, 0, 0) := by decide +kernel

private def pushed (bytes : List UInt8) (value : UInt8) : Result (List UInt8 × Nat) := do
  let (before, _) ← write {} 4096 root bytes
  let (after, _) ← push before 8 root value
  return ((← read after 4096 root).1, (← loadHeader after root).2)

example : pushed [] 0x12 = .ok ([0x12], 1) := by decide +kernel
example : pushed (List.replicate 30 0x34) 0x56 = .ok (List.replicate 30 0x34 ++ [0x56], 31) := by decide +kernel
example : pushed (List.replicate 31 0x34) 0x56 = .ok (List.replicate 31 0x34 ++ [0x56], 32) := by decide +kernel
example : pushed (List.replicate 32 0x34) 0x56 = .ok (List.replicate 32 0x34 ++ [0x56], 33) := by decide +kernel

private def popped (bytes : List UInt8) : Result (List UInt8 × Word × Word) := do
  let (before, _) ← write {} 4096 root bytes
  let (after, _) ← pop before 8 root
  return ((← read after 4096 root).1, after.execution.world.storage 0 (dataSlot root 0),
    after.execution.world.storage 0 (dataSlot root 1))

example : popped [0xff] = .ok ([], 0, 0) := by decide +kernel
example : popped (List.replicate 32 0xff) = .ok (List.replicate 31 0xff, 0, 0) := by decide +kernel
example : (popped (List.replicate 33 0xff)).map (fun result => (result.1, result.2.2)) =
    .ok (List.replicate 32 0xff, 0) := by decide +kernel

-- Pop clears the removed byte, while preserving dirty unused bits. Bulk copy
-- cleanup clears whole obsolete slots; neither operation assumes raw zeroes.
private def dirtyLong : Heap := {
  execution := {world := {storage := fun account slot =>
    if account != 0 then 0 else if slot = 1 then longHeader 33
    else if slot = dataSlot root 1 then BitVec.allOnes 256 else 0}} }

example : (pop dirtyLong 8 root).map (fun result => result.1.execution.world.storage 0 (dataSlot root 1)) =
    .ok (BitVec.ofNat 256 (2^248-1)) := by decide +kernel
example : (write dirtyLong 4096 root (List.replicate 32 0xab)).map
    (fun result => result.1.execution.world.storage 0 (dataSlot root 1)) = .ok 0 := by decide +kernel

-- The native push limit differs from bulk-copy admission; no huge list is built.
private def pushAtLimit : Result Nat := do
  let (after, _) ← push (heapWithHeader (longHeader maximumCopyLength)) 8 root 0xab
  return (← loadHeader after root).2

example : pushAtLimit = .ok pushLimit := by decide +kernel
example : (push (heapWithHeader (longHeader pushLimit)) 8 root 0xab).map (fun _ => ()) =
    .error (.panic 0x41) := by decide +kernel
example : (write (heapWithHeader (longHeader (2^200))) 4096 root []).map (fun _ => ()) =
    .error .exhausted := by decide +kernel

-- A repeated concrete target is retained, and its final physical write wins.
example : (applyWrites {} (.storage 0) [(9, 11), (9, 12)]).map
    (fun heap => heap.execution.world.storage 0 9) = .ok 12 := by decide +kernel

private def noArg (before : Heap) : Result (Nat × Nat × Nat) := do
  let (place, after, remaining) ← pushZeroChecked before 8 root
  let value ← Access.read after place
  match value with
  | ⟨.fixedBytes _, byte⟩ => return (byte.toNat, (← loadHeader after root).2, remaining)
  | _ => throw .rejected

example : noArg {} = .ok (0, 1, 4) := by decide +kernel

-- Extension retains the newly exposed dirty short byte, while masking the
-- still-unused suffix. This distinguishes push() from push(bytes1(0)).
private def dirtyShort : Heap := heapWithHeader (BitVec.ofNat 256 (0xaabb * 2^240))
example : noArg dirtyShort = .ok (0xaa, 1, 4) := by decide +kernel
example : (extend dirtyShort 8 root).map
    (fun result => result.1.execution.world.storage 0 1) =
    .ok (BitVec.ofNat 256 (0xaa * 2^248 + 2)) := by decide +kernel

private def noArgFrom (values : List UInt8) : Result (List UInt8 × Nat × Nat) := do
  let (before, _) ← writeChecked {} 4096 root values
  let (place, after, _) ← pushZeroChecked before 8 root
  return ((← read after 4096 root).1, place.reference.byte.val,
    after.layouts root.region root.address)

example : noArgFrom (List.replicate 30 0xab) = .ok (List.replicate 30 0xab ++ [0], 1, 0) := by decide +kernel
example : noArgFrom (List.replicate 31 0xab) = .ok (List.replicate 31 0xab ++ [0], 0, 1) := by decide +kernel
example : noArgFrom (List.replicate 32 0xab) = .ok (List.replicate 32 0xab ++ [0], 31, 1) := by decide +kernel

private def dirtyNextLong : Heap := {
  execution := {world := {storage := fun account slot =>
    if account != 0 then 0 else if slot = 1 then longHeader 32
    else if slot = dataSlot root 1 then BitVec.allOnes 256 else 0}} }
example : noArg dirtyNextLong = .ok (0xff, 33, 4) := by decide +kernel
example : (extend dirtyNextLong 8 root).map
    (fun result => result.1.execution.world.storage 0 (dataSlot root 1)) =
    .ok (BitVec.allOnes 256) := by decide +kernel

example : extensionWrites root (shortHeader (BitVec.allOnes 248) 31) 31 =
    [(dataSlot root 0, BitVec.ofNat 256 ((2^248-1)*256)), (1, longHeader 32)] := by decide +kernel
example : (pushZeroChecked {} 0 root).map (fun _ => ()) = .error .exhausted := by decide +kernel
example : (pushZeroChecked (heapWithHeader 64) 8 root).map (fun _ => ()) =
    .error (.panic 0x22) := by decide +kernel
example : (pushZeroChecked (heapWithHeader (longHeader pushLimit)) 8 root).map (fun _ => ()) =
    .error (.panic 0x41) := by decide +kernel
example : (pushZeroChecked {execution := {context := {readOnly := true}}} 8 root).map (fun _ => ()) =
    .error .exceptional := by decide +kernel

private def noArgStale : Result Unit := do
  let (old, heap, _) ← pushZeroChecked {} 8 root
  let (heap, _) ← popChecked heap 8 root
  let (_, heap, _) ← pushZeroChecked heap 8 root
  Access.validate heap old
example : noArgStale = .error (.undefinedBehavior "dangling storage reference after element removal") := by decide +kernel

end Solidity.Aggregates.StorageBytes.Tests
