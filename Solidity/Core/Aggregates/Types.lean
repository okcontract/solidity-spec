/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Registry
import Contract.Interaction.MemoryProofs

namespace Solidity.Aggregates
open Static Core
open Contract.Interaction (Word World Memory)

/-- Static rejection, inconclusive execution and source/EVM failure are
different outcomes. Host budget exhaustion never becomes a Solidity panic. -/
inductive Failure where
  | rejected
  | revert (bytes : List UInt8)
  | panic (code : UInt8)
  | exceptional
  | invalidContext (reason : String)
  | unsupported (reason : String)
  | undefinedBehavior (reason : String)
  | exhausted
  deriving DecidableEq, Repr

abbrev Result := Except Failure

structure Allocation where
  start : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- Internal calls share this heap and allocation frontier. External invocation
ownership is explicit; distinct invocations have separate allocation ownership. -/
structure Heap where
  execution : Contract.Interaction.State := {}
  invocation : Nat := 0
  nextMemory : Nat := 128
  allocations : List Allocation := []
  /-- Source-reference lifetime metadata is journaled with the heap, separately
  from EVM storage bytes. Removing an element invalidates prior references even
  if a later push reuses its physical slot. -/
  generations : Region → Word → Nat → Nat := fun _ _ _ => 0
  layouts : Region → Word → Nat := fun _ _ => 0
  /-- Unknown raw transitions invalidate source-reference histories. Current
  slot contents alone cannot establish that an element was never removed. -/
  historyEpoch : Region → Nat := fun _ => 0

structure Place where
  type : SType
  reference : Reference
  deriving DecidableEq, Repr

structure Value where
  type : SType
  value : type.Value

def storageBytes : SType → Option Nat
  | .uint width | .sint width | .fixedBytes width | .fixedPoint _ width _ => some (width.val + 1)
  | .bool | .enumType _ _ => some 1
  | .address _ | .contract _ _ _ => some 20
  | .valueType _ base => match base with
      | .scalar (.uint w) | .scalar (.sint w) | .scalar (.fixedBytes w) => some (w.val + 1)
      | .scalar .bool => some 1
      | .scalar .address | .payableAddress => some 20
  | .function .internal _ _ _ => some 8
  | .function .external _ _ _ => some 24
  | _ => none

theorem storageBytes_bound (type : SType) (bytes : Nat)
    (sized : storageBytes type = some bytes) : 0 < bytes ∧ bytes ≤ 32 := by
  cases type <;> simp_all [storageBytes]
  all_goals try omega
  case valueType identity base =>
    cases base with
    | payableAddress => simp_all; omega
    | scalar type => cases type <;> simp_all <;> omega
  case function visibility mutability parameters returns =>
    cases visibility <;> simp_all <;> omega

def atLocation : SType → Location → Bool → SType
  | .array element size _ _, location, pointer =>
      .array (atLocation element location false) size location pointer
  | .bytes _ _, location, pointer => .bytes location pointer
  | .string _ _, location, pointer => .string location pointer
  | .structType identity _ _, location, pointer => .structType identity location pointer
  | type, _, _ => type

def regionLocation : Region → Location
  | .storage _ | .transient _ => .storage
  | .memory _ => .memory
  | .calldata _ => .calldata

def referenceLocation : SType → Option Location
  | .array _ _ location _ | .bytes location _ | .string location _ |
    .structType _ location _ => some location
  | .mapping _ _ => some .storage
  | _ => none

def isReference (type : SType) : Bool := (referenceLocation type).isSome

def referenceValue (type : SType) (reference : Reference) : Result type.Value :=
  match type with
  | .array _ _ _ _ | .bytes _ _ | .string _ _ | .structType _ _ _ |
    .mapping _ _ => .ok reference
  | _ => .error .rejected

def Value.reference : (value : Value) → Option Reference
  | ⟨.array _ _ _ _, reference⟩ | ⟨.bytes _ _, reference⟩ |
    ⟨.string _ _, reference⟩ | ⟨.structType _ _ _, reference⟩ |
    ⟨.mapping _ _, reference⟩ => some reference
  | _ => none

def Place.asValue (place : Place) : Result Value :=
  (referenceValue place.type {place.reference with bindingCell := none}).map
    (fun value => ⟨place.type, value⟩)

def Heap.retire (heap : Heap) (region : Region) (slot : Word) (first stop : Nat) : Heap :=
  {heap with generations := fun r s index =>
    if r = region && s = slot && first ≤ index && index < stop then
      heap.generations r s index + 1 else heap.generations r s index}

def Heap.moveLayout (heap : Heap) (region : Region) (slot : Word) : Heap :=
  {heap with layouts := fun r s =>
    if r = region && s = slot then heap.layouts r s + 1 else heap.layouts r s}

def Heap.journalResize (heap : Heap) (region : Region) (slot : Word)
    (oldLength newLength : Nat) (bytes : Bool := false) : Heap :=
  let retired := heap.retire region slot newLength oldLength
  if bytes && (decide (oldLength < 32) != decide (newLength < 32)) then retired.moveLayout region slot else retired

theorem Heap.journalResize_execution (heap : Heap) (region : Region) (slot : Word)
    (oldLength newLength : Nat) (bytes : Bool) :
    (heap.journalResize region slot oldLength newLength bytes).execution = heap.execution := by
  simp only [Heap.journalResize]
  split <;> rfl

theorem Heap.retire_removed (heap : Heap) (region : Region) (slot : Word)
    (first stop index : Nat) (removed : first ≤ index ∧ index < stop) :
    (heap.retire region slot first stop).generations region slot index =
      heap.generations region slot index + 1 := by simp [Heap.retire, removed.1, removed.2]

theorem Heap.retire_retained (heap : Heap) (region : Region) (slot : Word)
    (first stop index : Nat) (retained : index < first ∨ stop ≤ index) :
    (heap.retire region slot first stop).generations region slot index =
      heap.generations region slot index := by
  rcases retained with before | after
  · simp [Heap.retire, Nat.not_le.mpr before]
  · simp [Heap.retire, Nat.not_lt.mpr after]

theorem Heap.retire_preserves_execution (heap : Heap) (region : Region) (slot : Word)
    (first stop : Nat) : (heap.retire region slot first stop).execution = heap.execution := rfl

def owner (reference : Reference) : Option (BitVec 160) :=
  match reference.region with
  | .storage account | .transient account => some account
  | _ => none

def Heap.allocated (heap : Heap) (start size : Nat) : Bool :=
  heap.allocations.any fun allocation =>
    allocation.start ≤ start && start + size ≤ allocation.start + allocation.size

def checkExtent (heap : Heap) (reference : Reference) (size : Nat) : Result Unit :=
  match reference.region with
  | .storage _ | .transient _ => .ok ()
  | .memory invocation =>
      if invocation != heap.invocation then .error (.invalidContext "foreign memory reference")
      else if heap.allocated reference.address.toNat size then .ok ()
      else .error (.invalidContext "unallocated memory extent")
  | .calldata invocation =>
      if invocation != heap.invocation then .error (.invalidContext "foreign calldata reference")
      else if reference.address.toNat + size ≤ heap.execution.context.calldata.length then .ok ()
      else .error (.revert [])

/-- A host materialization allowance is consumed before constructing packets.
Its unit is bytes/elements, not gas and not a source-language limit. -/
def reserve (budget work : Nat) : Result Nat :=
  if work ≤ budget then .ok (budget - work) else .error .exhausted

theorem reserve_sufficient (budget work : Nat) (enough : work ≤ budget) :
    reserve budget work = .ok (budget - work) := by simp [reserve, enough]

theorem reserve_exhausted (budget work : Nat) (tooMuch : budget < work) :
    reserve budget work = .error .exhausted := by simp [reserve, Nat.not_le.mpr tooMuch]

def rebase (reference : Reference) (address : Word) (byte : Fin 32 := 0) : Reference :=
  { reference with address, byte, viewLength := none, relativeBase := none, bindingCell := none, byteCell := false }

def Slot.read (heap : Heap) (region : Region) (slot : Word) : Result Word :=
  match region with
  | .storage owner => .ok (heap.execution.world.storage (owner.setWidth 256) slot)
  | .transient owner => .ok (heap.execution.world.transient owner slot)
  | _ => .error .rejected

def Slot.write (heap : Heap) (region : Region) (slot value : Word) : Result Heap :=
  if heap.execution.context.readOnly then .error .exceptional else
  match region with
  | .storage owner => .ok { heap with execution := { heap.execution with
      world := heap.execution.world.store (owner.setWidth 256) slot value } }
  | .transient owner => .ok { heap with execution := { heap.execution with
      world := heap.execution.world.tstore (owner.setWidth 256) slot value } }
  | _ => .error .rejected

theorem Slot.persistent_transient_separate (heap : Heap) (owner : BitVec 160)
    (slot value : Word) (after : Heap)
    (written : Slot.write heap (.storage owner) slot value = .ok after) :
    after.execution.world.transient = heap.execution.world.transient := by
  unfold Slot.write at written
  split at written
  · cases written
  · cases written; rfl

theorem Slot.transient_persistent_separate (heap : Heap) (owner : BitVec 160)
    (slot value : Word) (after : Heap)
    (written : Slot.write heap (.transient owner) slot value = .ok after) :
    after.execution.world.storage = heap.execution.world.storage := by
  unfold Slot.write at written
  split at written
  · cases written
  · cases written; rfl

end Solidity.Aggregates
