/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Translations
import Solidity.Core.Execution.Machine

namespace Solidity.Execution.Compatibility
open Core Static
open Contract.Interaction (Word wordBytes)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def environmentPacket : Core.Env types → Packet
  | .nil => []
  | .cons (type := type) value rest =>
      .atom ⟨SType.ofCore type, scalarValue type value⟩ :: environmentPacket rest

def decodePacket : (types : List Core.Ty) → Packet → Option (Core.Env types)
  | [], [] => some .nil
  | type :: types, .atom value :: rest => do
      if same : value.type = SType.ofCore type then
        return .cons (coreValue type (same ▸ value.value)) (← decodePacket types rest)
      else none
  | _, _ => none

@[simp] theorem decode_environmentPacket (environment : Core.Env types) :
    decodePacket types (environmentPacket environment) = some environment := by
  induction environment with
  | nil => rfl
  | cons head rest ih => simp [environmentPacket, decodePacket, ih]

theorem encode_environmentPacket (environment : Core.Env types) :
    Machine.encodePacket (environmentPacket environment) = .ok environment.abiWords := by
  induction environment with
  | nil => rfl
  | @cons types type head rest ih =>
      simp only [Machine.encodePacket, Datum.asAtom, Bind.bind, Except.bind] at ih
      simp only [environmentPacket, Machine.encodePacket, List.mapM_cons,
        Datum.asAtom, Bind.bind, Except.bind, scalarValue_memory, Env.abiWords]
      rw [ih]
      rfl

/-- Only real source failures in the old observation domain are projected.
Invalid context, static rejection, unsupported execution and host exhaustion
cannot silently become an old fault/revert certificate. -/
def failureOutcome : Aggregates.Failure → Option (Core.Outcome State)
  | .revert bytes => some (.reverted bytes)
  | .panic code => some (.reverted (Contract.panic code))
  | .exceptional => some .fault
  | _ => none

def procedureObservation (returns : List Core.Ty) : Observation State → Option (Core.ProcedureOutcome State returns)
  | .returned values state => do
      return .returned state.external (← decodePacket returns values) state.heap.execution.world.logs
  | .failed (.revert bytes) _ => some (.reverted bytes)
  | .failed (.panic code) _ => some (.reverted (Contract.panic code))
  | .failed .exceptional _ => some .fault
  | _ => none

def fallthrough : Execution.Expr Keys := .literal ⟨.bool, true⟩

/-- Word/empty are the only explicit return packets in the old block fragment.
The Boolean packet is an internal fallthrough marker, never a source value
invented by its observation projection. -/
def BlockPacket (packet : Packet) : Prop :=
  packet = [] ∨ ∃ value : Word, packet = [.atom ⟨.uint 31, value⟩]

theorem BlockPacket.excludes_fallthrough (represented : BlockPacket packet) :
    packet ≠ [.atom ⟨.bool, true⟩] := by
  rcases represented with rfl | ⟨value, rfl⟩ <;> intro impossible <;> cases impossible

def blockObservation : Observation State → Option (Core.Flow State)
  | .returned [] state => some (.halt (.returned [] state.external))
  | .returned [.atom ⟨.bool, value⟩] state => if value then some (.next state.external) else none
  | .returned [.atom ⟨.uint width, value⟩] state =>
      if width = 31 then some (.halt (.returned (wordBytes (value.setWidth 256)) state.external)) else none
  | .failed failure _ => (failureOutcome failure).map Core.Flow.halt
  | _ => none

theorem blockObservation_next (state : MachineState State) :
    blockObservation (.returned [.atom ⟨.bool, true⟩] state) = some (.next state.external) := rfl

theorem blockObservation_word (state : MachineState State) (value : Word) :
    blockObservation (.returned [.atom ⟨.uint 31, value⟩] state) =
      some (.halt (.returned (wordBytes value) state.external)) := by
  simp only [blockObservation, ↓reduceIte, Option.some.injEq, Core.Flow.halt.injEq,
    Core.Outcome.returned.injEq, and_true]
  congr 1

theorem blockObservation_stop (state : MachineState State) :
    blockObservation (.returned [] state) = some (.halt (.returned [] state.external)) := rfl

def blockBody (body : Core.Block Ref Place) : Execution.Stmt (Key Ref Place) :=
  .seq (block body) (.return_ (some fallthrough))

def controlBody (body : Core.Control.Command Ref Place) : Execution.Stmt (Key Ref Place) :=
  .seq (control body) (.return_ (some fallthrough))

def initial (external : State) (environment : Core.Env types) (emitter : BitVec 160 := 0) : MachineState State :=
  {external, locals := localEnv environment,
    heap := {execution := {context := {self := emitter.setWidth 256}}}}

end Solidity.Execution.Compatibility
