/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.ExpressionRules

/-! Old scalar expressions execute the shared machine using actual transition
prefixes. The selected left-first schedule is the one used by existing source
certificates; the machine's independent additional choices remain available. -/
namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

variable {σ : Type} {Keys : SType → Type}
variable {Ref : Core.Ty → Type}
variable {backend : Backend σ Keys} {registry : Registry} {program : Program Keys}

def coreResult (type : Core.Ty) (result : Core.Result type.Value) : Aggregates.Result Datum :=
  (Effects.liftCore result).map (fun value => .atom (scalar type value))

@[simp] theorem coreResult_ok (type : Core.Ty) (value : type.Value) :
    coreResult type (.ok value) = .ok (.atom (scalar type value)) := rfl

@[simp] theorem coreResult_error (type : Core.Ty) (bytes : List UInt8) :
    coreResult type (.error bytes) = .error (Effects.failureOfBytes bytes) := rfl

theorem failureOfBytes_source (bytes : List UInt8) : isSourceFailure (Effects.failureOfBytes bytes) = true := by
  cases same : bytes == Contract.panic ((bytes[35]?).getD 0) <;>
    simp [Effects.failureOfBytes, same, isSourceFailure]

theorem core_binary (state : MachineState σ) (operation : Core.Binary a b result)
    (left right : Execution.Expr Keys) (leftResult : Core.Result a.Value) (rightResult : Core.Result b.Value)
    (first : ∀ mode, PureResult backend registry program {state with mode} left (coreResult a leftResult))
    (second : ∀ mode, PureResult backend registry program {state with mode} right (coreResult b rightResult)) :
    PureResult backend registry program state (binary operation left right)
      (coreResult result (do
        let a ← leftResult
        let b ← rightResult
        operation.eval a b)) := by
  let mode := binaryMode operation state.mode
  have notAnd : binaryCode operation ≠ .and := by cases operation <;> simp [binaryCode]
  have notOr : binaryCode operation ≠ .or := by cases operation <;> simp [binaryCode]
  have inner : PureResult backend registry program {state with mode}
      (.binary (binaryCode operation) (SType.ofCore result) left right)
      (coreResult result (do
        let a ← leftResult
        let b ← rightResult
        operation.eval a b)) := by
    have firstMode := first mode
    have secondMode := second mode
    cases leftResult with
    | error bytes =>
        simpa using two_first_failure {state with mode}
          (.binary (binaryCode operation) (SType.ofCore result) left right) left right
          (Effects.failureOfBytes bytes) firstMode (.binary (binaryCode operation) (SType.ofCore result))
          (binary_started _ _ _ _ _ notAnd notOr)
    | ok a =>
        cases rightResult with
        | error bytes =>
            simpa using two_second_failure {state with mode}
              (.binary (binaryCode operation) (SType.ofCore result) left right) left right
              (.atom (scalar _ a)) (Effects.failureOfBytes bytes) firstMode secondMode
              (.binary (binaryCode operation) (SType.ofCore result))
              (binary_started _ _ _ _ _ notAnd notOr)
        | ok b =>
            have applied := binary_effect operation a b state.mode
            change Effects.binary mode (binaryCode operation) (scalar _ a) (scalar _ b) = _ at applied
            cases calculated : operation.eval a b with
            | ok answer =>
                simp only [calculated, Effects.liftCore, Except.map] at applied
                simpa [calculated] using pure_binary_ok {state with mode}
                  (binaryCode operation) (SType.ofCore result) left right (scalar _ a) (scalar _ b)
                  (scalar result answer) notAnd notOr firstMode secondMode applied rfl
            | error bytes =>
                simp only [calculated, Effects.liftCore, Except.map] at applied
                simpa [calculated] using pure_binary_error {state with mode}
                  (binaryCode operation) (SType.ofCore result) left right (scalar _ a) (scalar _ b)
                  (Effects.failureOfBytes bytes) notAnd notOr firstMode secondMode applied (failureOfBytes_source bytes)
  cases operation <;> first
    | exact pure_mode state _ _ inner
    | exact inner

theorem core_unary_node (state : MachineState σ) (code : UnaryCode) (child : Execution.Expr Keys)
    (argument : Core.Result a.Value) (calculate : a.Value → Core.Result b.Value)
    (evaluated : PureResult backend registry program state child (coreResult a argument))
    (law : ∀ value, Effects.unary state.mode code (scalar a value) =
      (Effects.liftCore (calculate value)).map (scalar b)) :
    PureResult backend registry program state (.unary code child)
      (coreResult b (argument >>= calculate)) := by
  cases argument with
  | error bytes =>
      simpa using one_failure state (.unary code child) child (Effects.failureOfBytes bytes)
        evaluated (.unary code) (unary_started state code child)
  | ok value =>
      have applied := law value
      cases calculated : calculate value with
      | ok answer =>
          simp only [calculated, Effects.liftCore, Except.map] at applied
          simpa [calculated] using pure_unary_ok state code child (scalar a value) (scalar b answer) evaluated applied
      | error bytes =>
          simp only [calculated, Effects.liftCore, Except.map] at applied
          simpa [calculated] using pure_unary_error state code child (scalar a value) (Effects.failureOfBytes bytes)
            evaluated applied (failureOfBytes_source bytes)

theorem core_cast_node (state : MachineState σ) (child : Execution.Expr Keys)
    (argument : Core.Result a.Value) (calculate : a.Value → b.Value)
    (evaluated : PureResult backend registry program state child (coreResult a argument))
    (law : ∀ value, Effects.convert registry 1 state.materializationRemaining state.heap
      (.explicit .ordinary) (SType.ofCore b) (scalar a value) =
        .ok (scalar b (calculate value), state.heap, state.materializationRemaining)) :
    PureResult backend registry program state (.cast (.explicit .ordinary) (SType.ofCore b) child)
      (coreResult b (do return calculate (← argument))) := by
  cases argument with
  | error bytes =>
      simpa using one_failure state (.cast (.explicit .ordinary) (SType.ofCore b) child) child
        (Effects.failureOfBytes bytes) evaluated (.cast (.explicit .ordinary) (SType.ofCore b))
        (cast_started state (.explicit .ordinary) (SType.ofCore b) child)
  | ok value =>
      exact pure_cast_ok state (.explicit .ordinary) (SType.ofCore b) child
        (scalar a value) (scalar b (calculate value)) evaluated (law value)

theorem core_unary (state : MachineState σ) (operation : Core.Unary a b) (child : Execution.Expr Keys)
    (argument : Core.Result a.Value)
    (evaluated : ∀ mode, PureResult backend registry program {state with mode} child (coreResult a argument)) :
    PureResult backend registry program state (unary operation child)
      (coreResult b (argument >>= operation.eval)) := by
  have ordinary := evaluated state.mode
  change PureResult backend registry program state child (coreResult a argument) at ordinary
  cases operation with
  | not =>
      exact core_unary_node state .not child argument (Core.Unary.not.eval) ordinary (by
        intro value; exact not_effect value state.mode)
  | uintNot width =>
      exact core_unary_node state .bitnot child argument (Core.Unary.uintNot width).eval ordinary (by
        intro value; exact uintNot_effect width value state.mode)
  | sintNot width =>
      exact core_unary_node state .bitnot child argument (Core.Unary.sintNot width).eval ordinary (by
        intro value; exact sintNot_effect width value state.mode)
  | bytesNot width =>
      exact core_unary_node state .bitnot child argument (Core.Unary.bytesNot width).eval ordinary (by
        intro value; exact bytesNot_effect width value state.mode)
  | negate width mode =>
      apply pure_mode state mode (.unary .neg child)
      exact core_unary_node {state with mode} .neg child argument (Core.Unary.negate width mode).eval
        (evaluated mode) (fun value => negate_effect width value mode)
  | uintCast src dst =>
      exact core_cast_node (a := .uint src) (b := .uint dst) state child argument (fun value => BitVec.ofNat dst.bits value.toNat)
        ordinary (fun value => uintCast_effect registry 1 _ state.heap src dst value)
  | sintCast src dst =>
      exact core_cast_node (a := .sint src) (b := .sint dst) state child argument (fun value => BitVec.ofInt dst.bits value.toInt)
        ordinary (fun value => sintCast_effect registry 1 _ state.heap src dst value)
  | toSigned width =>
      exact core_cast_node (a := .uint width) (b := .sint width) state child argument id ordinary
        (fun value => signed_effect registry 1 _ state.heap width value)
  | toUnsigned width =>
      exact core_cast_node (a := .sint width) (b := .uint width) state child argument id ordinary
        (fun value => unsigned_effect registry 1 _ state.heap width value)
  | addressOfUint =>
      exact core_cast_node (a := .uint 19) (b := .address) state child argument id ordinary
        (fun value => address_effect registry 1 _ state.heap value)
  | uintOfAddress =>
      exact core_cast_node (a := .address) (b := .uint 19) state child argument id ordinary
        (fun value => uintOfAddress_effect registry 1 _ state.heap value)
  | boolWord =>
      cases argument with
      | error bytes =>
          exact pure_conditional_error state child (.literal ⟨.uint 31, 1⟩) (.literal ⟨.uint 31, 0⟩)
            (Effects.failureOfBytes bytes) ordinary
      | ok value =>
          cases value <;>
            exact pure_conditional state child (.literal ⟨.uint 31, 1⟩) (.literal ⟨.uint 31, 0⟩) _ ordinary
              (pure_literal state _)

/-- Only primitive reference observations are supplied by a read adapter. All
compound expression steps are proved below by induction on closed syntax. -/
def ReadsCorrect (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (read : σ → Locals → ∀ {type}, Ref type → type.Value) (valid : σ → Locals → Prop) : Prop :=
  ∀ state, valid state.external state.locals → ∀ {type} (reference : Ref type),
    PureResult backend registry program state (resolve reference)
      (.ok (.atom (scalar type (read state.external state.locals reference))))

theorem expression_left (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (read : σ → Locals → ∀ {type}, Ref type → type.Value) (valid : σ → Locals → Prop)
    (reads : ReadsCorrect (backend := backend) (registry := registry) (program := program) resolve read valid)
    (value : Core.Expr Ref type) :
    ∀ state, valid state.external state.locals →
      PureResult backend registry program state (expression resolve value)
        (coreResult type (value.eval (read state.external state.locals) .leftFirst)) := by
  induction value with
  | literal value => intro state _; exact pure_literal state (scalar _ value)
  | read reference => intro state h; exact reads state h reference
  | unary operation value ih =>
      intro state h
      exact core_unary state operation _ _ (fun mode => ih {state with mode} h)
  | binary operation left right first second =>
      intro state h
      exact core_binary state operation _ _ _ _
        (fun mode => first {state with mode} h) (fun mode => second {state with mode} h)
  | ite test yes no condition first second =>
      intro state h
      have tested := condition state h
      cases calculated : test.eval (read state.external state.locals) .leftFirst with
      | error bytes =>
          simp only [calculated] at tested
          simpa [expression, Core.Expr.eval, calculated] using
            pure_conditional_error state _ _ _ (Effects.failureOfBytes bytes) tested
      | ok choice =>
          simp only [calculated] at tested
          cases choice with
          | false =>
              simpa [expression, Core.Expr.eval, calculated] using
                pure_conditional state _ _ _ false tested (second state h)
          | true =>
              simpa [expression, Core.Expr.eval, calculated] using
                pure_conditional state _ _ _ true tested (first state h)
  | and left right first second =>
      intro state h
      have tested := first state h
      cases calculated : left.eval (read state.external state.locals) .leftFirst with
      | error bytes =>
          simp only [calculated] at tested
          simpa [expression, Core.Expr.eval, calculated, lazyExpression] using
            pure_lazy_error state false _ _ (Effects.failureOfBytes bytes) tested
      | ok choice =>
          simp only [calculated] at tested
          cases choice with
          | false =>
              simpa [expression, Core.Expr.eval, calculated, lazyExpression] using
                pure_lazy_stop state false _ _ tested
          | true =>
              simpa [expression, Core.Expr.eval, calculated, lazyExpression] using
                pure_lazy_next state false _ _ tested (second state h)
  | or left right first second =>
      intro state h
      have tested := first state h
      cases calculated : left.eval (read state.external state.locals) .leftFirst with
      | error bytes =>
          simp only [calculated] at tested
          simpa [expression, Core.Expr.eval, calculated, lazyExpression] using
            pure_lazy_error state true _ _ (Effects.failureOfBytes bytes) tested
      | ok choice =>
          simp only [calculated] at tested
          cases choice with
          | false =>
              simpa [expression, Core.Expr.eval, calculated, lazyExpression] using
                pure_lazy_next state true _ _ tested (second state h)
          | true =>
              simpa [expression, Core.Expr.eval, calculated, lazyExpression] using
                pure_lazy_stop state true _ _ tested

theorem external_reads (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) :
    ReadsCorrect (backend := Compatibility.backend store) (registry := registry) (program := program)
      (fun reference => .externalRead (.read reference)) (fun external _ => store.read external) (fun _ _ => True) := by
  intro state _ type reference
  exact pure_external (backend := Compatibility.backend store) (registry := registry) (program := program)
    state (Key.read reference) (scalarValue type (store.read state.external reference)) rfl

theorem frame_reads (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (environment : Core.Env types) :
    ReadsCorrect (backend := Compatibility.backend store) (registry := registry) (program := program)
      frameReference (fun external _ => Core.FrameRef.read (store.read external) environment)
      (fun _ locals => Represents locals environment) := by
  intro state represented type reference
  cases reference with
  | «local» var =>
      exact pure_local state (localId var) (SType.ofCore type) (scalar type (environment.get var))
        (read_local_given registry 0 state.heap state.locals _ _ _ (represented var))
  | global reference =>
      exact pure_external (backend := Compatibility.backend store) (registry := registry) (program := program)
        state (Key.read reference) (scalarValue type (store.read state.external reference)) rfl

theorem externalExpression_left (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (value : Core.Expr Ref type) :
    PureResult (Compatibility.backend store) registry program state (externalExpression value)
      (coreResult type (value.eval (store.read state.external) .leftFirst)) :=
  expression_left _ _ _ (external_reads store registry program) value state trivial

theorem frameExpression_left (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (environment : Core.Env types)
    (represented : Represents state.locals environment) (value : Core.Expr (Core.FrameRef Ref types) type) :
    PureResult (Compatibility.backend store) registry program state (frameExpression value)
      (coreResult type (value.eval (Core.FrameRef.read (store.read state.external) environment) .leftFirst)) :=
  expression_left _ _ _ (frame_reads store registry program environment) value state represented

end Solidity.Execution.Compatibility
