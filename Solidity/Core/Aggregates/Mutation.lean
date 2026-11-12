/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy.Operations

/-! Source permissions for aggregate mutations. The storage implementation
helpers accept captured internal positions; these endpoints retain source
guards and validate the resolved type before changing a physical cell.
Deleting a local binding returns its new value to the enclosing environment.
Deleting a memory aggregate member rebinds its captured pointer cell. -/
namespace Solidity.Aggregates.Mutation
open Core Static

def deletable : SType → Bool
  | .array _ _ .memory _ | .bytes .memory _ | .string .memory _ |
    .structType _ .memory _ => true
  | .array _ _ .storage false | .bytes .storage false | .string .storage false |
    .structType _ .storage false => true
  | .uint _ | .sint _ | .fixedBytes _ | .bool | .address _ | .enumType _ _ |
    .contract _ _ _ | .function _ _ _ _ | .fixedPoint _ _ _ => true
  | _ => false

/-- Local storage/calldata references cannot be reset by `delete`. Fixed point
deletion is source-valid but execution remains explicitly unsupported. -/
def deleteValue (registry : Registry) (fuel budget : Nat) (heap : Heap) (type : SType) :
    Result (Value × Heap × Nat) := do
  eligibleType registry fuel type
  if !deletable type then throw .rejected
  match defaultScalar type with
  | some zero => return (⟨type, zero⟩, heap, budget)
  | none =>
      if referenceLocation type = some .memory then
        Defaults.defaultValue registry fuel budget heap type
      else throw (.unsupported "no executable default value for this local type")

def delete (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place) :
    Result (Heap × Nat) := do
  eligibleAt registry fuel place.reference.region place.type
  Access.validate heap place
  if !deletable place.type then throw .rejected
  match place.reference.region with
  | .calldata _ => throw .rejected
  | .storage _ | .transient _ => StorageArrays.delete registry fuel budget heap place
  | .memory _ =>
      if isReference place.type then
        let some address := place.reference.bindingCell |
          throw (.invalidContext "memory aggregate deletion requires its captured binding cell")
        let (zero, after, remaining) ← deleteValue registry fuel budget heap place.type
        let cell := rebase place.reference address
        return (← Defaults.writeMemoryValue after cell zero, remaining)
      else return (← StorageArrays.scalarZero heap place, budget)

def pushZero (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place) :
    Result (Place × Heap × Nat) := do
  eligibleAt registry fuel place.reference.region place.type
  Access.validate heap place
  match place.type, place.reference.region with
  | .array _ none .storage _, .storage _ =>
      StorageArrays.pushZero registry fuel budget heap place
  | .bytes .storage _, .storage _ => StorageBytes.pushZeroChecked heap budget place.reference
  | _, _ => throw .rejected

def push (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place)
    (value : Value) : Result (Heap × Nat) := do
  eligibleAt registry fuel place.reference.region place.type
  Access.validate heap place
  match place.type, place.reference.region with
  | .array element none .storage _, .storage _ =>
      let _ ← planTransfer registry fuel false value.type (atLocation element .storage false)
      let (target, after, remaining) ← StorageArrays.pushZero registry fuel budget heap place
      Copy.assign registry fuel remaining after target value
  | .bytes .storage _, .storage _ =>
      match value.type, value.value with
      | .fixedBytes width, byte =>
          if width = 0 then StorageBytes.pushChecked heap budget place.reference byte.toNat.toUInt8
          else throw .rejected
      | _, _ => throw .rejected
  | _, _ => throw .rejected

def pop (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place) :
    Result (Heap × Nat) := do
  eligibleAt registry fuel place.reference.region place.type
  Access.validate heap place
  match place.type, place.reference.region with
  | .array _ none .storage _, .storage _ => StorageArrays.pop registry fuel budget heap place
  | .bytes .storage _, .storage _ => StorageBytes.popChecked heap budget place.reference
  | _, _ => throw .rejected

theorem storage_pointer_delete_rejected (element : SType) (size : Option Nat) :
    deletable (.array element size .storage true) = false := rfl

theorem mapping_delete_rejected (key value : SType) :
    deletable (.mapping key value) = false := rfl

theorem value_type_delete_rejected (identity : Nat) (base : Elementary) :
    deletable (.valueType identity base) = false := rfl

theorem local_scalar_delete (type : SType) (zero : type.Value)
    (eligible : eligibleType registry fuel type = .ok ())
    (allowed : deletable type = true) (default : defaultScalar type = some zero) :
    deleteValue registry fuel budget heap type = .ok (⟨type, zero⟩, heap, budget) := by
  simp [deleteValue, eligible, allowed, default]
  rfl

end Solidity.Aggregates.Mutation
