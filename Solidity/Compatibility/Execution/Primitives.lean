/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Scalars
import Solidity.Core.Control
import Solidity.Core.Execution.State

/-! Concrete scalar-store codecs for compatibility with the existing finite
specifications. These definitions perform reads and writes only; statements,
control and calls must execute the shared effectful machine. The external state
is unchanged in representation, so no cardinality assumption about its logical
locations is needed. -/
namespace Solidity.Execution.Compatibility
open Core Static
open Aggregates (Failure)

def scalarValue (type : Core.Ty) : type.Value → (SType.ofCore type).Value := by
  cases type <;> exact id

def coreValue (type : Core.Ty) : (SType.ofCore type).Value → type.Value := by
  cases type <;> exact id

@[simp] theorem coreValue_scalarValue (type : Core.Ty) (value : type.Value) :
    coreValue type (scalarValue type value) = value := by
  cases type <;> rfl

@[simp] theorem scalarValue_coreValue (type : Core.Ty) (value : (SType.ofCore type).Value) :
    scalarValue type (coreValue type value) = value := by
  cases type <;> rfl

theorem scalarValue_memory (type : Core.Ty) (value : type.Value) :
    Aggregates.encodeMemory (SType.ofCore type) (scalarValue type value) =
      .ok (type.abiWord value) := by
  cases type <;> rfl

/-- Keys are closed typed operands, never interpreter callbacks. Read references
and write places remain distinct because the old Store interface does not
promise that every write place can also be read. -/
inductive Key (Ref Place : Core.Ty → Type) : SType → Type where
  | read {type : Core.Ty} : Ref type → Key Ref Place (SType.ofCore type)
  | place {type : Core.Ty} : Place type → Key Ref Place (SType.ofCore type)

def read (store : Core.Store Ref Place State) (state : State) :
    {type : SType} → Key Ref Place type → Aggregates.Result type.Value
  | _, .read reference => .ok (scalarValue _ (store.read state reference))
  | _, .place _ => .error (.invalidContext "legacy write place has no read codec")

def write (store : Core.Store Ref Place State) (state : State) :
    {type : SType} → Key Ref Place type → type.Value → Aggregates.Result State
  | _, .read _, _ => .error (.invalidContext "legacy read reference has no write codec")
  | _, .place place, value =>
      match store.write state place (coreValue _ value) with
      | some after => .ok after
      | none => .error .exceptional

/-- The shared evaluator uses these codecs with the original external state.
No statement or expression evaluator is hidden in this backend. -/
def backend (store : Core.Store Ref Place State) : Backend State (Key Ref Place) where
  read := read store
  write := write store

@[simp] theorem read_reference (store : Core.Store Ref Place State) (state : State)
    (reference : Ref type) :
    read store state (.read reference) = .ok (scalarValue type (store.read state reference)) := rfl

@[simp] theorem read_place (store : Core.Store Ref Place State) (state : State)
    (place : Place type) :
    read store state (.place place) =
      .error (.invalidContext "legacy write place has no read codec") := rfl

@[simp] theorem write_reference (store : Core.Store Ref Place State) (state : State)
    (reference : Ref type) (value : (SType.ofCore type).Value) :
    write store state (.read reference) value =
      .error (.invalidContext "legacy read reference has no write codec") := rfl

theorem write_place_success_iff (store : Core.Store Ref Place State) (state after : State)
    (place : Place type) (value : type.Value) :
    write store state (.place place) (scalarValue type value) = .ok after ↔
      store.write state place value = some after := by
  simp only [write, coreValue_scalarValue]
  cases stored : store.write state place value <;> simp

theorem write_place_failure_iff (store : Core.Store Ref Place State) (state : State)
    (place : Place type) (value : type.Value) :
    write store state (.place place) (scalarValue type value) = .error .exceptional ↔
      store.write state place value = none := by
  simp only [write, coreValue_scalarValue]
  cases stored : store.write state place value <;> simp

theorem read_scalar_type (key : Key Ref Place type) : type.scalarSupported = true := by
  cases key with
  | @read type _ => cases type <;> rfl
  | @place type _ => cases type <;> rfl

theorem read_not_reference (key : Key Ref Place type) : Aggregates.isReference type = false := by
  cases key with
  | @read type _ => cases type <;> rfl
  | @place type _ => cases type <;> rfl

end Solidity.Execution.Compatibility
