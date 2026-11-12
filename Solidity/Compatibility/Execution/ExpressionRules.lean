/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.ExpressionContexts

namespace Solidity.Execution.Compatibility
open Core Static
open Aggregates (Failure)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

variable {σ : Type} {Keys : SType → Type}
variable {backend : Backend σ Keys} {registry : Registry} {program : Program Keys}

theorem pure_literal (state : MachineState σ) (value : Value) :
    PureResult backend registry program state (.literal value) (.ok (.atom value)) := by
  intro stack entry
  exact literal_reaches backend registry program ⟨.eval (.literal value), stack, state, entry⟩ value

theorem pure_external (state : MachineState σ) (key : Keys type) (value : type.Value)
    (read : backend.read state.external key = .ok value) :
    PureResult backend registry program state (.externalRead key) (.ok (.atom ⟨type, value⟩)) := by
  intro stack entry
  exact external_reaches backend registry program ⟨.eval (.externalRead key), stack, state, entry⟩ key value read

theorem pure_local (state : MachineState σ) (id : LocalId) (type : SType) (value : Value)
    (read : Effects.readCaptured registry 1 state.locals state.heap (.local id type) = .ok value) :
    PureResult backend registry program state (.local id type) (.ok (.atom value)) := by
  intro stack entry
  apply next_reaches (choice := 0)
  simp [Machine.transition, legacyLimits, read, Machine.next]

theorem pure_mode (state : MachineState σ) (mode : ArithmeticMode) (value : Execution.Expr Keys)
    (evaluated : PureResult backend registry program {state with mode} value result) :
    PureResult backend registry program state (.arithmetic mode value) result := by
  cases result with
  | ok answer =>
      intro stack entry
      let config : Config σ Keys := ⟨.eval value, stack, state, entry⟩
      exact (mode_enter backend registry program config mode value).trans
        ((evaluated (.mode state.mode :: stack) entry).trans
          (mode_leave backend registry program {config with state := {state with mode}} state.mode answer))
  | error failure =>
      intro stack entry
      let config : Config σ Keys := ⟨.eval value, stack, state, entry⟩
      exact (mode_enter backend registry program config mode value).executes
        (evaluated (.mode state.mode :: stack) entry)

theorem unary_started (state : MachineState σ) (code : UnaryCode) (value : Execution.Expr Keys)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Machine.transition backend registry legacyLimits program 0
      ⟨.eval (.unary code value), stack, state, entry⟩ =
        .ok (.next ⟨.collect [(0, value)] [] (.unary code), stack, state, entry⟩) := rfl

theorem cast_started (state : MachineState σ) (mode : ConversionMode) (type : SType) (value : Execution.Expr Keys)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Machine.transition backend registry legacyLimits program 0
      ⟨.eval (.cast mode type value), stack, state, entry⟩ =
        .ok (.next ⟨.collect [(0, value)] [] (.cast mode type), stack, state, entry⟩) := rfl

theorem binary_started (state : MachineState σ) (code : BinaryCode) (type : SType)
    (left right : Execution.Expr Keys) (notAnd : code ≠ .and) (notOr : code ≠ .or)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Machine.transition backend registry legacyLimits program 0
      ⟨.eval (.binary code type left right), stack, state, entry⟩ =
        .ok (.next ⟨.collect [(0, left), (1, right)] [] (.binary code type), stack, state, entry⟩) := by
  cases code <;> first | exact False.elim (notAnd rfl) | exact False.elim (notOr rfl) | rfl

theorem pure_unary_ok (state : MachineState σ) (code : UnaryCode) (child : Execution.Expr Keys)
    (value answer : Value) (evaluated : PureResult backend registry program state child (.ok (.atom value)))
    (applied : Effects.unary state.mode code value = .ok answer) :
    PureResult backend registry program state (.unary code child) (.ok (.atom answer)) := by
  intro stack entry
  have children := one_prefix state (.unary code child) child (.atom value) evaluated (.unary code)
    (unary_started state code child) stack entry
  apply children.trans
  apply next_reaches (choice := 0)
  simp [Machine.transition, Machine.apply, Datum.asAtom, applied, Machine.next]

theorem pure_unary_error (state : MachineState σ) (code : UnaryCode) (child : Execution.Expr Keys)
    (value : Value) (failure : Failure) (evaluated : PureResult backend registry program state child (.ok (.atom value)))
    (applied : Effects.unary state.mode code value = .error failure) (sourceFailure : isSourceFailure failure = true) :
    PureResult backend registry program state (.unary code child) (.error failure) := by
  intro stack entry
  have children := one_prefix state (.unary code child) child (.atom value) evaluated (.unary code)
    (unary_started state code child) stack entry
  apply children.executes
  apply failed_executes (choice := 0) (sourceFailure := sourceFailure)
  simp [Machine.transition, Machine.apply, Datum.asAtom, applied]

theorem pure_binary_ok (state : MachineState σ) (code : BinaryCode) (type : SType)
    (left right : Execution.Expr Keys) (a b answer : Value) (notAnd : code ≠ .and) (notOr : code ≠ .or)
    (first : PureResult backend registry program state left (.ok (.atom a)))
    (second : PureResult backend registry program state right (.ok (.atom b)))
    (applied : Effects.binary state.mode code a b = .ok answer) (typed : answer.type = type) :
    PureResult backend registry program state (.binary code type left right) (.ok (.atom answer)) := by
  intro stack entry
  have children := two_prefix state (.binary code type left right) left right (.atom a) (.atom b)
    first second (.binary code type) (binary_started state code type left right notAnd notOr) stack entry
  apply children.trans
  apply next_reaches (choice := 0)
  simp [Machine.transition, Machine.apply, Datum.asAtom, applied, Machine.typed, Datum.type, typed, Machine.next]

theorem pure_binary_error (state : MachineState σ) (code : BinaryCode) (type : SType)
    (left right : Execution.Expr Keys) (a b : Value) (failure : Failure) (notAnd : code ≠ .and) (notOr : code ≠ .or)
    (first : PureResult backend registry program state left (.ok (.atom a)))
    (second : PureResult backend registry program state right (.ok (.atom b)))
    (applied : Effects.binary state.mode code a b = .error failure) (sourceFailure : isSourceFailure failure = true) :
    PureResult backend registry program state (.binary code type left right) (.error failure) := by
  intro stack entry
  have children := two_prefix state (.binary code type left right) left right (.atom a) (.atom b)
    first second (.binary code type) (binary_started state code type left right notAnd notOr) stack entry
  apply children.executes
  apply failed_executes (choice := 0) (sourceFailure := sourceFailure)
  simp [Machine.transition, Machine.apply, Datum.asAtom, applied]

theorem pure_cast_ok (state : MachineState σ) (mode : ConversionMode) (type : SType)
    (child : Execution.Expr Keys) (value answer : Value)
    (evaluated : PureResult backend registry program state child (.ok (.atom value)))
    (applied : Effects.convert registry 1 state.materializationRemaining state.heap mode type value =
      .ok (answer, state.heap, state.materializationRemaining)) :
    PureResult backend registry program state (.cast mode type child) (.ok (.atom answer)) := by
  intro stack entry
  have children := one_prefix state (.cast mode type child) child (.atom value) evaluated (.cast mode type)
    (cast_started state mode type child) stack entry
  apply children.trans
  apply next_reaches (choice := 0)
  simp [Machine.transition, Machine.apply, legacyLimits, applied, Machine.next]

theorem pure_cast_error (state : MachineState σ) (mode : ConversionMode) (type : SType)
    (child : Execution.Expr Keys) (value : Value) (failure : Failure)
    (evaluated : PureResult backend registry program state child (.ok (.atom value)))
    (applied : Effects.convert registry 1 state.materializationRemaining state.heap mode type value = .error failure)
    (sourceFailure : isSourceFailure failure = true) :
    PureResult backend registry program state (.cast mode type child) (.error failure) := by
  intro stack entry
  have children := one_prefix state (.cast mode type child) child (.atom value) evaluated (.cast mode type)
    (cast_started state mode type child) stack entry
  apply children.executes
  apply failed_executes (choice := 0) (sourceFailure := sourceFailure)
  simp [Machine.transition, Machine.apply, legacyLimits, applied]

theorem conditional_prefix (state : MachineState σ) (test yes no : Execution.Expr Keys) (choice : Bool)
    (evaluated : PureResult backend registry program state test (.ok (.atom (scalar .bool choice))))
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.eval (.conditional test yes no), stack, state, entry⟩
      ⟨.eval (if choice then yes else no), stack, state, entry⟩ := by
  have start : Reaches (transition backend registry program)
      ⟨.eval (.conditional test yes no), stack, state, entry⟩
      ⟨.eval test, .select yes no :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  apply start.trans ((evaluated (.select yes no :: stack) entry).trans ?_)
  apply next_reaches (choice := 0)
  rfl

theorem pure_conditional (state : MachineState σ) (test yes no : Execution.Expr Keys) (choice : Bool)
    (evaluated : PureResult backend registry program state test (.ok (.atom (scalar .bool choice))))
    (branch : PureResult backend registry program state (if choice then yes else no) result) :
    PureResult backend registry program state (.conditional test yes no) result := by
  cases result with
  | ok answer =>
      intro stack entry
      exact (conditional_prefix state test yes no choice evaluated stack entry).trans (branch stack entry)
  | error failure =>
      intro stack entry
      exact (conditional_prefix state test yes no choice evaluated stack entry).executes (branch stack entry)

theorem pure_conditional_error (state : MachineState σ) (test yes no : Execution.Expr Keys) (failure : Failure)
    (evaluated : PureResult backend registry program state test (.error failure)) :
    PureResult backend registry program state (.conditional test yes no) (.error failure) := by
  intro stack entry
  have start : Reaches (transition backend registry program)
      ⟨.eval (.conditional test yes no), stack, state, entry⟩
      ⟨.eval test, .select yes no :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  exact start.executes (evaluated (.select yes no :: stack) entry)

def lazyExpression (terminal : Bool) (left right : Execution.Expr Keys) : Execution.Expr Keys :=
  .binary (if terminal then .or else .and) .bool left right

theorem lazy_start (state : MachineState σ) (terminal : Bool) (left right : Execution.Expr Keys)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.eval (lazyExpression terminal left right), stack, state, entry⟩
      ⟨.eval left, .lazy terminal right :: stack, state, entry⟩ := by
  apply next_reaches (choice := 0)
  cases terminal <;> rfl

theorem pure_lazy_stop (state : MachineState σ) (terminal : Bool) (left right : Execution.Expr Keys)
    (evaluated : PureResult backend registry program state left (.ok (.atom (scalar .bool terminal)))) :
    PureResult backend registry program state (lazyExpression terminal left right) (.ok (.atom (scalar .bool terminal))) := by
  intro stack entry
  apply (lazy_start state terminal left right stack entry).trans
  apply (evaluated (.lazy terminal right :: stack) entry).trans
  apply next_reaches (choice := 0)
  cases terminal <;> rfl

theorem pure_lazy_next (state : MachineState σ) (terminal : Bool) (left right : Execution.Expr Keys)
    (evaluated : PureResult backend registry program state left (.ok (.atom (scalar .bool (!terminal)))))
    (branch : PureResult backend registry program state right result) :
    PureResult backend registry program state (lazyExpression terminal left right) result := by
  have path (stack : List (Frame Keys)) (entry : MachineState σ) :
      Reaches (transition backend registry program)
        ⟨.eval (lazyExpression terminal left right), stack, state, entry⟩
        ⟨.eval right, stack, state, entry⟩ := by
    apply (lazy_start state terminal left right stack entry).trans
    apply (evaluated (.lazy terminal right :: stack) entry).trans
    apply next_reaches (choice := 0)
    cases terminal <;> rfl
  cases result with
  | ok answer => intro stack entry; exact (path stack entry).trans (branch stack entry)
  | error failure => intro stack entry; exact (path stack entry).executes (branch stack entry)

theorem pure_lazy_error (state : MachineState σ) (terminal : Bool) (left right : Execution.Expr Keys)
    (failure : Failure) (evaluated : PureResult backend registry program state left (.error failure)) :
    PureResult backend registry program state (lazyExpression terminal left right) (.error failure) := by
  intro stack entry
  exact (lazy_start state terminal left right stack entry).executes (evaluated (.lazy terminal right :: stack) entry)

end Solidity.Execution.Compatibility
