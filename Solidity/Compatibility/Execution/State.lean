/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Expressions
import Solidity.Compatibility.Execution.Frames
import Solidity.Compatibility.Execution.Observations

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem write_external (store : Core.Store Ref Place State) (registry : Registry)
    (state : MachineState State) (place : Place type) (value : type.Value) :
    Machine.writeTarget (backend store) registry legacyLimits state (.external (Key.place place)) (scalar type value) =
      match store.write state.external place value with
      | some after => .ok {state with external := after}
      | none => .error .exceptional := by
  simp only [Machine.writeTarget, legacyLimits]
  rw [convert_scalar_self registry 0 state.materializationRemaining state.heap type value]
  simp [backend, write, scalar]
  cases store.write state.external place value <;> rfl

theorem typeOf_of_read (locals : Locals) (id : LocalId) (type : SType)
    (read : locals.read id type = .ok value) : locals.typeOf id = .ok type := by
  cases found : locals.find id with
  | none => simp [Locals.read, found] at read
  | some cell =>
      by_cases same : cell.type = type
      · simp [Locals.typeOf, found, same]
      · simp [Locals.read, found, same] at read

theorem write_local (backend : Backend σ Keys) (registry : Registry) (state : MachineState σ)
    (id : LocalId) (type : Core.Ty) (value : type.Value)
    (declared : state.locals.typeOf id = .ok (SType.ofCore type))
    (written : state.locals.write id (SType.ofCore type) (scalar type value) = .ok after) :
    Machine.writeTarget backend registry legacyLimits state (.captured (.local id (SType.ofCore type)))
      (scalar type value) = .ok {state with locals := after} := by
  simp [Machine.writeTarget, Effects.writeCaptured, legacyLimits, declared, scalar_bind, written]

theorem prepareArguments_packet (registry : Registry) (state : MachineState σ) (environment : Core.Env types) :
    Machine.prepareArguments registry legacyLimits state (types.map SType.ofCore) (environmentPacket environment) =
      .ok (environmentPacket environment, state) := by
  induction environment generalizing state with
  | nil => rfl
  | @cons types type head rest ih =>
      simp only [Machine.prepareArguments, environmentPacket, List.map_cons, Datum.asAtom, legacyLimits,
        Bind.bind, Except.bind]
      have converted := convert_scalar_self registry 0 state.materializationRemaining state.heap type head
      simp only [scalar] at converted
      rw [converted]
      dsimp only
      simp only [legacyLimits] at ih
      rw [ih]
      rfl

end Solidity.Execution.Compatibility
