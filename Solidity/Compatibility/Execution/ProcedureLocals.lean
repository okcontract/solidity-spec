/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.ResultBindings
import Solidity.Compatibility.Execution.ProcedureContexts

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure
variable {σ : Type} {Keys : SType → Type}
variable {backend : Backend σ Keys} {registry : Registry} {program : Program Keys}

theorem FrameEnv.write {locals after : Locals} {environment : Core.Env types}
    (frame : FrameEnv locals environment) (var : Core.Var types type) (value : type.Value)
    (written : locals.write (localId var) (SType.ofCore type) (scalar type value) = .ok after) :
    FrameEnv after (environment.set var value) where
  represented := Represents.write frame.represented var value written
  fresh := by
    intro index bound
    have different : localId var ≠ 2 * index :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le (localId_lt var) (Nat.mul_le_mul_left 2 bound))
    exact (Locals.write_frames_other different written).trans (frame.fresh index bound)
  nonempty := write_nonempty locals after frame.nonempty written

theorem assignmentResult_scalar (registry : Registry) (state : MachineState σ) (id : Nat)
    (type : Core.Ty) (value : type.Value) :
    Machine.assignmentResult (Key := Keys) registry legacyLimits state
      (.captured (.local id (SType.ofCore type))) (scalar type value) = .ok (scalar type value) := by
  unfold Machine.assignmentResult Effects.assignmentResult
  have ordinary : Aggregates.isReference (SType.ofCore type) = false := by cases type <;> rfl
  simp only [Captured.type, ordinary, Bool.false_eq_true, ↓reduceIte]
  exact scalarCast_implicit_self type value

/-- Capturing an existing scalar local and committing an assignment uses the
same real lvalue/write machinery as source code. The RHS is evaluated first,
which is one licensed sibling evaluation order. -/
theorem local_assignment_prefix (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (state : MachineState σ) (id : Nat) (type : Core.Ty) (expression : Execution.Expr Keys)
    (value : type.Value) (after : Locals)
    (evaluated : PureResult backend registry program state expression (.ok (.atom (scalar type value))))
    (typed : state.locals.typeOf id = .ok (SType.ofCore type))
    (written : state.locals.write id (SType.ofCore type) (scalar type value) = .ok after)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.exec (.expr (.assign (.local id (SType.ofCore type)) expression)), stack, state, entry⟩
      ⟨.resume .next, stack, {state with locals := after}, entry⟩ := by
  have start : Reaches (transition backend registry program)
      ⟨.exec (.expr (.assign (.local id (SType.ofCore type)) expression)), stack, state, entry⟩
      ⟨.eval expression, .assignRight (.local id (SType.ofCore type)) none :: .discard :: stack, state, entry⟩ :=
    (next_reaches (choice := 0) rfl).trans (next_reaches (choice := 0) rfl)
  apply start.trans ((evaluated _ entry).trans ?_)
  refine (next_reaches (choice := 0) rfl).trans ?_
  have captured : Reaches (transition backend registry program)
      ⟨.capture (.local id (SType.ofCore type)),
        .commitValue (.atom (scalar type value)) none :: .discard :: stack, state, entry⟩
      ⟨.target (.captured (.local id (SType.ofCore type))),
        .commitValue (.atom (scalar type value)) none :: .discard :: stack, state, entry⟩ :=
    next_reaches (choice := 0) (by simp [Machine.transition, typed, Machine.next])
  refine captured.trans ?_
  have committed : Reaches (transition backend registry program)
      ⟨.target (.captured (.local id (SType.ofCore type))),
        .commitValue (.atom (scalar type value)) none :: .discard :: stack, state, entry⟩
      ⟨.value (.atom (scalar type value)), .discard :: stack, {state with locals := after}, entry⟩ := by
    apply next_reaches (choice := 0)
    simp only [Machine.transition, Machine.commit, Datum.asAtom, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [write_local backend registry state id type value typed written]
    simp [assignmentResult_scalar, Machine.next]
  exact committed.trans (next_reaches (choice := 0) rfl)

theorem local_assignment_failure (state : MachineState σ) (id : Nat) (type : SType)
    (expression : Execution.Expr Keys) (failure : Aggregates.Failure)
    (evaluated : PureResult backend registry program state expression (.error failure))
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Executes (transition backend registry program)
      ⟨.exec (.expr (.assign (.local id type) expression)), stack, state, entry⟩ (fail entry failure) := by
  exact ((next_reaches (choice := 0) (by rfl)).trans (next_reaches (choice := 0) (by rfl))).executes
    (evaluated (.assignRight (.local id type) none :: .discard :: stack) entry)

theorem declareValue_single (backend : Backend σ Keys) (registry : Registry) (state : MachineState σ)
    (environment : Core.Env types) (frame : FrameEnv state.locals environment) (value : type.Value) :
    ∃ after,
      Machine.declareValues backend registry legacyLimits state [some (binder type types.length)]
        [.atom (scalar type value)] = .ok after ∧
      FrameEnv after.locals (.cons value environment) ∧ OddFrame state.locals after.locals ∧
      after.external = state.external ∧ after.heap = state.heap ∧ after.mode = state.mode ∧
      after.materializationRemaining = state.materializationRemaining := by
  have result := declareValues_results backend registry state (Core.Env.cons value .nil) environment frame
  simpa only [resultBinders, environmentPacket, Core.Env.append, List.length_nil, Nat.add_zero] using result

end Solidity.Execution.Compatibility
