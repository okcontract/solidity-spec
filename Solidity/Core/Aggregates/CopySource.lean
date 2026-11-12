/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Contents

/-! Fresh-memory copy reads storage/calldata, which allocation cannot change.
A dry frontier orders native allocation checks with source decoding before the
existing materializer writes memory. Storage scalar arrays use the production
unbounded ABI encoder and finalize after reading; reference arrays/structs
allocate before their children. Calldata uses the production ABI decoder,
whose child-offset checks differ from source indexing's checked tail access. -/
namespace Solidity.Aggregates.CopySource
open Static
open Contract.Interaction (Word)

def allocation (frontier size : Nat) : Result Nat :=
  if MemoryOps.maximumMemory < frontier + MemoryOps.roundedSize size then .error (.panic 0x41)
  else .ok (frontier + MemoryOps.roundedSize size)

theorem allocation_resource (large : MemoryOps.maximumMemory < frontier + MemoryOps.roundedSize size) :
    allocation frontier size = .error (.panic 0x41) := by simp [allocation, large]

theorem allocation_success (fits : frontier + MemoryOps.roundedSize size ≤ MemoryOps.maximumMemory) :
    allocation frontier size = .ok (frontier + MemoryOps.roundedSize size) := by
  simp [allocation, Nat.not_lt.mpr fits]

private def allocateArray (frontier count : Nat) (bytes dynamic : Bool) : Result Nat := do
  allocation frontier (← MemoryOps.arraySize count bytes dynamic)

private def calldata (place : Place) : Bool :=
  match place.reference.region with | .calldata _ => true | _ => false

/-- ABI child decoding limits relative offsets before invoking the child's
decoder. Its own minimum-head/allocation/extent sequence is handled below. -/
private def decoderChild (registry : Registry) (fuel : Nat) (heap : Heap) (type : SType)
    (cell : Reference) (base : Word) : Result Place := do
  let type := atLocation type .calldata false
  if isReference type && (← calldataDynamic registry fuel type) then
    let offset ← Access.readWord heap cell
    if MemoryOps.maximumMemory < offset.toNat then throw (.revert [])
    let reference ← Access.advance {cell with address := base} offset.toNat
    return ⟨type, reference⟩
  else return ⟨type, cell⟩

private def arrayChild (registry : Registry) (fuel : Nat) (heap : Heap)
    (place : Place) (element : SType) (index : Nat) : Result Place := do
  if calldata place then
    let data ← Access.arrayData place
    let stride ← calldataHeadSize registry fuel element
    decoderChild registry fuel heap element (← Access.advance data (index*stride))
      (data.relativeBase.getD data.address)
  else Access.index registry fuel heap place index

private def fieldChild (registry : Registry) (fuel : Nat) (heap : Heap)
    (place : Place) (fields : List (String × SType)) (index : Nat) : Result Place := do
  if calldata place then
    let some (_, type) := fields[index]? | throw .rejected
    let offset ← (fields.take index).foldlM (fun offset (_, member) => do
      return offset + (← calldataHeadSize registry fuel member)) 0
    decoderChild registry fuel heap type (← Access.advance place.reference offset) place.reference.address
  else Access.field registry fuel heap place index

private def arrayExtent (registry : Registry) (fuel : Nat) (heap : Heap)
    (place : Place) (element : SType) (count : Nat) : Result Unit := do
  let data ← Access.arrayData place
  let stride ← calldataHeadSize registry fuel element
  checkExtent heap data (count*stride)

private def structExtent (registry : Registry) (fuel : Nat) (heap : Heap)
    (place : Place) (fields : List (String × SType)) : Result Unit := do
  let head ← fields.foldlM (fun size (_, type) => do
    return size + (← calldataHeadSize registry fuel type)) 0
  checkExtent heap place.reference head

private def bytePacket (registry : Registry) (fuel : Nat) (heap : Heap)
    (place : Place) (count : Nat) : Result (List UInt8) := do
  let source : Place := ⟨.bytes (regionLocation place.reference.region) false, place.reference⟩
  (List.range count).mapM fun index => do
    let value ← Access.read heap (← Access.index registry fuel heap source index)
    match value with
    | ⟨.fixedBytes width, word⟩ =>
        if width = 0 then return word.toNat.toUInt8 else throw .rejected
    | _ => throw .rejected

/-- `nested` selects the ABI array decoder's minimum-head check. At the root,
array conversions already carry their length and use the available-length
decoder. Every host traversal is reserved before materializing its index list. -/
def freeze (registry : Registry) : Nat → Bool → Nat → Heap → Nat → Place →
    Result (Contents × Nat × Nat)
  | 0, _, _, _, _, _ => .error .exhausted
  | fuel+1, nested, budget, heap, frontier, place => do
      Access.validate heap place
      match place.type with
      | .array element size _ _ =>
          if calldata place && nested then checkExtent heap place.reference 32
          let count ← Access.length heap place
          let delayed := !calldata place && (storageBytes element).isSome
          let frontier ← if delayed then pure frontier else allocateArray frontier count false size.isNone
          if calldata place then arrayExtent registry fuel heap place element count
          let budget ← reserve budget (count+1)
          let (values, budget, frontier) ← (List.range count).foldlM
            (fun (values, budget, frontier) index => do
              let child ← arrayChild registry fuel heap place element index
              let (value, budget, frontier) ← freeze registry fuel true budget heap frontier child
              return (value :: values, budget, frontier)) ([], budget, frontier)
          let frontier ← if delayed then allocateArray frontier count false size.isNone else pure frontier
          return (.array element values.reverse, budget, frontier)
      | .structType identity _ _ =>
          let some fields := registry.structFields identity |
            throw (.invalidContext "missing struct definition during fresh copy")
          if calldata place then structExtent registry fuel heap place fields
          let frontier ← allocation frontier (fields.length*32)
          let budget ← reserve budget (fields.length+1)
          let (values, budget, frontier) ← (List.range fields.length).foldlM
            (fun (values, budget, frontier) index => do
              let child ← fieldChild registry fuel heap place fields index
              let (value, budget, frontier) ← freeze registry fuel true budget heap frontier child
              return (value :: values, budget, frontier)) ([], budget, frontier)
          return (.structure identity values.reverse, budget, frontier)
      | .bytes _ _ | .string _ _ =>
          let count ← Access.length heap place
          let frontier ← if calldata place then allocateArray frontier count true true else pure frontier
          if calldata place then
            let data ← if place.reference.viewLength.isSome then pure place.reference
              else Access.advance place.reference 32
            checkExtent heap data count
          let budget ← reserve budget (count+1)
          let values ← bytePacket registry fuel heap place count
          let frontier ← if calldata place then pure frontier else allocateArray frontier count true true
          return (.bytes (match place.type with | .string _ _ => true | _ => false) values, budget, frontier)
      | .mapping _ _ => throw .rejected
      | _ =>
          let budget ← reserve budget 1
          return (.scalar (← Access.read heap place), budget, frontier)

def snapshotForMemory (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (place : Place) : Result (Contents × Nat) := do
  eligibleAt registry fuel place.reference.region place.type
  match place.reference.region with
  | .storage _ | .calldata _ => pure ()
  | _ => throw .rejected
  if !MemoryOps.validAllocationContext heap then
    throw (.invalidContext "invalid memory allocation context")
  let (contents, remaining, _) ← freeze registry fuel false budget heap heap.nextMemory place
  return (contents, remaining)

theorem freeze_exhausted (registry : Registry) (nested : Bool) (budget frontier : Nat)
    (heap : Heap) (place : Place) :
    freeze registry 0 nested budget heap frontier place = .error .exhausted := rfl

end Solidity.Aggregates.CopySource
