/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.CallTransfers

/-! Universal scalar result transfers through the actual local-store and
continuation-machine paths. Return cells are typed inputs initialized by
`initializeReturn_packet`; successful readback and frame laws are derived. -/
namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def OutsideReturn (base : Nat) (types : List Core.Ty) (id : Nat) : Prop :=
  ∀ index, base ≤ index → index < base + types.length → 2 * index + 1 ≠ id

theorem ReturnTypes.frame {locals after : Locals} {types : List Core.Ty} {base : Nat}
    (typed : ReturnTypes locals base types)
    (same : ∀ index, base ≤ index → index < base + types.length →
      after.find (2 * index + 1) = locals.find (2 * index + 1)) :
    ReturnTypes after base types := by
  induction types generalizing base with
  | nil => trivial
  | cons type types ih =>
      refine ⟨?_, ih typed.2 ?_⟩
      · unfold Locals.typeOf
        rw [same base (Nat.le_refl _) (by simp)]
        exact typed.1
      · intro index lower upper
        exact same index (by omega) (by simp; omega)

theorem write_scalar_exists (locals : Locals) (id : Nat) (type : Core.Ty) (value : type.Value)
    (typed : locals.typeOf id = .ok (SType.ofCore type)) :
    ∃ after, locals.write id (SType.ofCore type) (scalar type value) = .ok after := by
  cases found : locals.find id with
  | none => simp [Locals.typeOf, found] at typed
  | some cell =>
      rcases cell with ⟨actual, data⟩
      have same : actual = SType.ofCore type := by simpa [Locals.typeOf, found] using typed
      subst actual
      exact ⟨locals.replace id ⟨SType.ofCore type, some (scalarValue type value)⟩,
        by simp [Locals.write, found, scalar]⟩

def returnAssignments (Keys : SType → Type) (base : Nat) : Core.Env types → List (Target Keys × Value)
  | .nil => []
  | .cons (type := type) value rest =>
      (.captured (.local (2 * base + 1) (SType.ofCore type)), scalar type value) ::
        returnAssignments Keys (base + 1) rest

theorem resultWrites_packet (Keys : SType → Type) (environment : Core.Env types) (base : Nat) :
    Machine.resultWrites (Key := Keys) (returnBinders base types) (environmentPacket environment) =
      .ok (returnAssignments Keys base environment) := by
  induction environment generalizing base with
  | nil => rfl
  | cons value rest ih =>
      simp [Machine.resultWrites, returnBinders, environmentPacket, returnAssignments, Datum.asAtom, ih, scalar]

theorem return_packet_fold (backend : Backend σ Keys) (registry : Registry)
    (environment : Core.Env types) (base : Nat) (state : MachineState σ)
    (typed : ReturnTypes state.locals base types) :
    ∃ after,
      (returnAssignments Keys base environment).foldlM
        (fun state item => Machine.writeTarget backend registry legacyLimits state item.1 item.2) state = .ok after ∧
      ReturnValues after.locals base environment ∧
      (∀ id, OutsideReturn base types id → after.locals.find id = state.locals.find id) ∧
      after.external = state.external ∧ after.heap = state.heap ∧ after.mode = state.mode ∧
      after.materializationRemaining = state.materializationRemaining := by
  induction environment generalizing base state with
  | nil => exact ⟨state, rfl, trivial, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | @cons types type value rest ih =>
      obtain ⟨locals, stored⟩ := write_scalar_exists state.locals (2 * base + 1) type value typed.1
      let first : MachineState σ := {state with locals}
      have headWrite := write_local backend registry state (2 * base + 1) type value typed.1 stored
      have tailTypes : ReturnTypes first.locals (base + 1) types :=
        ReturnTypes.frame typed.2 (by
          intro index lower upper
          have different : 2 * base + 1 ≠ 2 * index + 1 := by omega
          exact Locals.write_frames_other different stored)
      obtain ⟨after, tailWrite, tailValues, tailFrame, external, heap, mode, budget⟩ := ih (base + 1) first tailTypes
      refine ⟨after, ?_, ⟨?_, tailValues⟩, ?_, external, heap, mode, budget⟩
      · simp only [returnAssignments, List.foldlM_cons]
        rw [headWrite]
        exact tailWrite
      · have same := tailFrame (2 * base + 1) (by
          intro index lower upper
          omega)
        exact (Locals.read_eq_of_find_eq same).trans (Locals.read_after_write stored)
      · intro id outside
        have suffix : OutsideReturn (base + 1) types id := by
          intro index lower upper
          exact outside index (by omega) (by simp; omega)
        have different : 2 * base + 1 ≠ id := outside base (Nat.le_refl _) (by simp)
        exact (tailFrame id suffix).trans (Locals.write_frames_other different stored)

theorem FrameEnv.of_even_find {locals after : Locals} {environment : Core.Env types}
    (frame : FrameEnv locals environment)
    (same : ∀ index, after.find (2 * index) = locals.find (2 * index))
    (nonempty : after ≠ []) : FrameEnv after environment where
  represented := fun var =>
    (Locals.read_eq_of_find_eq (same (localIndex var))).trans (frame.represented var)
  fresh := fun index bound => (same index).trans (frame.fresh index bound)
  nonempty := nonempty

theorem writes_prefix (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (assignments : List (Target Keys × Value)) (state after entry : MachineState σ)
    (stack : List (Frame Keys))
    (written : assignments.foldlM
      (fun state item => Machine.writeTarget backend registry legacyLimits state item.1 item.2) state = .ok after) :
    Reaches (Machine.step backend registry legacyLimits program)
      ⟨.writes assignments, stack, state, entry⟩ ⟨.value (.tuple []), stack, after, entry⟩ := by
  induction assignments generalizing state with
  | nil =>
      simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at written
      cases written
      exact Reaches.single (choice := 0) (by rfl)
  | cons item assignments ih =>
      cases first : Machine.writeTarget backend registry legacyLimits state item.1 item.2 with
      | error failure => simp [List.foldlM_cons, first] at written
      | ok middle =>
          have tail : assignments.foldlM
              (fun state item => Machine.writeTarget backend registry legacyLimits state item.1 item.2) middle = .ok after := by
            simpa only [List.foldlM_cons, first, Bind.bind, Except.bind] using written
          have moved : Machine.step backend registry legacyLimits program 0
              ⟨.writes (item :: assignments), stack, state, entry⟩ =
              .next ⟨.writes assignments, stack, middle, entry⟩ := by
            simp only [legacyLimits] at first
            simp [Machine.step, Machine.transition, Machine.next, legacyLimits, first]
          exact .next moved (ih middle tail)

theorem finishCall_packet (config : Config σ Keys) (caller : Locals) (mode : ArithmeticMode)
    (stack : List (Frame Keys)) (environment : Core.Env types) (base : Nat)
    (values : ReturnValues config.state.locals base environment) :
    Machine.finishCall config caller mode (returnBinders base types) stack =
      .ok (.next ⟨.value (Datum.ofPacket (environmentPacket environment)), stack,
        {config.state with locals := caller, mode}, config.entry⟩) := by
  simp [Machine.finishCall, ReturnValues.collect values, Machine.next]

/-- Explicit scalar returns write their real odd slots in source component
order, read them back, and unwind the actual saved call continuation. All
legacy scalar families, result arities and caller frames are quantified. -/
theorem explicitReturn_prefix (backend : Backend σ Keys) (registry : Registry)
    (program : Program Keys) (state entry : MachineState σ) (caller : Locals)
    (mode : ArithmeticMode) (stack : List (Frame Keys))
    (environment : Core.Env types) (base : Nat)
    (typed : ReturnTypes state.locals base types) :
    Reaches (Machine.step backend registry legacyLimits program)
      ⟨.resume (.return_ (some (.tuple (environmentPacket environment)))),
        .call caller mode (returnBinders base types) :: stack, state, entry⟩
      ⟨.value (Datum.ofPacket (environmentPacket environment)), stack,
        {state with locals := caller, mode}, entry⟩ := by
  obtain ⟨after, written, values, framed, external, heap, arithmetic, budget⟩ :=
    return_packet_fold backend registry environment base state typed
  have entered : Machine.step backend registry legacyLimits program 0
      ⟨.resume (.return_ (some (.tuple (environmentPacket environment)))),
        .call caller mode (returnBinders base types) :: stack, state, entry⟩ =
      .next ⟨.writes (returnAssignments Keys base environment),
        .resultTransfer caller mode (returnBinders base types) :: stack, state, entry⟩ := by
    simp [Machine.step, Machine.transition, Machine.next, legacyLimits,
      resultWrites_packet, Datum.asPacket]
  have stores := writes_prefix backend registry program (returnAssignments Keys base environment)
    state after entry (.resultTransfer caller mode (returnBinders base types) :: stack) written
  have left : Machine.step backend registry legacyLimits program 0
      ⟨.value (.tuple []), .resultTransfer caller mode (returnBinders base types) :: stack, after, entry⟩ =
      .next ⟨.value (Datum.ofPacket (environmentPacket environment)), stack,
        {after with locals := caller, mode}, entry⟩ := by
    simp [Machine.step, Machine.transition, Machine.finishCall, Machine.next, legacyLimits,
      ReturnValues.collect values]
  have restored : {after with locals := caller, mode} = {state with locals := caller, mode} := by
    cases state
    cases after
    simp_all
  rw [restored] at left
  exact (Reaches.single entered).trans (stores.trans (Reaches.single left))

end Solidity.Execution.Compatibility
