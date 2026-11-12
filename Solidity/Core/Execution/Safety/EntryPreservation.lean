/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Machine

/-! Structural checkpoint preservation for the actual machine. Primitive
results stay opaque: every continuation that constructs a next configuration
retains the entry field. No source safety, successful primitive, reachability
or evaluator-callback premise is used. -/
namespace Solidity.Execution.Machine
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private def EntrySafe (entry : MachineState σ) (result : Result (Progress (Config σ Key) (Observation σ))) : Prop :=
  ∀ after, result = .ok (.next after) → after.entry = entry

private theorem entry_error (failure : Failure) : EntrySafe (Key := Key) entry (.error failure) := by
  intro after impossible
  cases impossible

private theorem entry_done (observed : Observation σ) : EntrySafe (Key := Key) entry (.ok (.done observed)) := by
  intro after impossible
  cases impossible

private theorem entry_suspended (config : Config σ Key) : EntrySafe entry (.ok (.suspended config)) := by
  intro after impossible
  cases impossible

private theorem entry_bind {action : Result α}
    {continuation : α → Result (Progress (Config σ Key) (Observation σ))}
    (safe : ∀ value, EntrySafe entry (continuation value)) : EntrySafe entry (action >>= continuation) := by
  cases action with
  | error failure => exact entry_error failure
  | ok value => exact safe value

private theorem entry_next (config : Config σ Key) (task : Task Key) (state : MachineState σ) (stack : List (Frame Key)) :
    EntrySafe config.entry (next config task state stack) := by
  intro after completed
  cases completed
  rfl

macro "entry_safety" "(" extra:tactic ")" : tactic =>
  `(tactic|
    repeat first
      | $extra:tactic
      | apply entry_next
      | apply entry_error
      | apply entry_done
      | apply entry_suspended
      | (apply entry_bind; intro value)
      | split
      | simp only [Bind.bind,Except.bind,Pure.pure,Except.pure])

private theorem entry_gather (config : Config σ Key) (values : List (Expr Key)) (finish : Completion) :
    EntrySafe config.entry (gather config values finish) := by
  unfold gather
  apply entry_next

private theorem entry_finishCall (config : Config σ Key) (locals : Locals) (mode : Core.ArithmeticMode)
    (returns : List Binder) (stack : List (Frame Key)) :
    EntrySafe config.entry (finishCall config locals mode returns stack) := by
  unfold finishCall
  entry_safety (fail)

private theorem entry_invoke (backend : Backend σ Key) (registry : Registry) (limits : Limits) (program : Program Key)
    (config : Config σ Key) (signature : FunctionSignature) (function : Value) (arguments : Packet) :
    EntrySafe config.entry (invoke backend registry limits program config signature function arguments) := by
  unfold invoke
  entry_safety (fail)

private theorem entry_commit (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (config : Config σ Key) (target : Target Key) (right : Datum) (compound : Option BinaryCode)
    (stack : List (Frame Key)) :
    EntrySafe config.entry (commit backend registry limits config target right compound stack) := by
  unfold commit
  entry_safety (fail)

private theorem entry_update (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (config : Config σ Key) (target : Target Key) (code : UpdateCode) (stack : List (Frame Key)) :
    EntrySafe config.entry (update backend registry limits config target code stack) := by
  unfold update
  entry_safety (fail)

private theorem entry_apply (backend : Backend σ Key) (registry : Registry) (limits : Limits) (program : Program Key)
    (config : Config σ Key) (finish : Completion) (values : Packet) :
    EntrySafe config.entry (apply backend registry limits program config finish values) := by
  unfold apply
  entry_safety (apply entry_invoke)

private theorem entry_transition (backend : Backend σ Key) (registry : Registry) (limits : Limits) (program : Program Key)
    (choice : Nat) (config : Config σ Key) :
    EntrySafe config.entry (transition backend registry limits program choice config) := by
  unfold transition
  entry_safety (first | apply entry_apply | apply entry_gather | apply entry_finishCall | apply entry_commit | apply entry_update)

theorem step_next_entry
    (stepped : step backend registry limits program choice config = .next after) :
    after.entry = config.entry := by
  cases changed : transition backend registry limits program choice config with
  | error failure =>
      cases failure <;> simp [step,changed,isSourceFailure] at stepped
  | ok progress =>
      cases progress with
      | done result => simp [step,changed] at stepped
      | suspended result => simp [step,changed] at stepped
      | next current =>
          have preserved := entry_transition backend registry limits program choice config current changed
          cases limit : limits.hostContinuationLimit with
          | none =>
              simp only [step,changed,limit] at stepped
              cases stepped
              exact preserved
          | some maximum =>
              simp only [step,changed,limit] at stepped
              split at stepped
              · cases stepped
              · cases stepped
                exact preserved

end Solidity.Execution.Machine
