/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Conformance.Scalar

/-! Kernel fixtures for the scalar corpus's checked continuation machine.
Loop results use ordinary function entry; rollback and host exhaustion inspect
actual machine observations as well as the native-expectation projection. -/
namespace Solidity.Conformance.ScalarMachine.Tests
open Solidity.Execution Solidity.Static
open Solidity.Conformance.ScalarMachine

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/- Keep result comparison local to these kernel computations. The runtime
interface gains no instance, evaluator, or proof assumption. -/
@[reducible] private def resultEq : DecidableEq (Core.Result (BitVec 256))
  | .ok left, .ok right => decidable_of_iff (left = right) (by simp)
  | .error left, .error right => decidable_of_iff (left = right) (by simp)
  | .ok _, .error _ => isFalse (by intro equality; cases equality)
  | .error _, .ok _ => isFalse (by intro equality; cases equality)
attribute [local instance] resultEq

example : outcomes (expressionRun (boolWord (.binary .and .bool (boolean false) testCondition))) =
    [.ok 0] := by decide +kernel

example : outcomes (expressionRun (boolWord (.binary .or .bool (boolean true) testCondition))) =
    [.ok 1] := by decide +kernel

example : outcomes (expressionRun (.conditional (boolean false) division (word 3))) =
    [.ok 3] := by decide +kernel

/-- The eager operands choose different first source failures. Both restore
the complete expression-entry checkpoint. -/
example : expressionRun twoPanics = .ok (.finished (.failed (.panic 0x12) initial)) ∧
    expressionRun twoPanics 1 = .ok (.finished (.failed (.panic 0x11) initial)) := by
  constructor <;> rfl

example : outcomes (loopRun whileCount) = [.ok 3] := by decide +kernel
example : outcomes (loopRun forContinue) = [.ok 3] := by decide +kernel
example : outcomes (loopRun forBreak) = [.ok 0] := by decide +kernel
example : outcomes (loopRun nestedBreak) = [.ok 3] := by decide +kernel

private def checkpoint : MachineState Unit := {
  initial with
  heap := { initial.heap with
    invocation := 7
    generations := fun _ _ _ => 4
    layouts := fun _ _ => 5
    historyEpoch := fun _ => 6
    execution := { initial.heap.execution with
      world := { (initial.heap.execution.world.store 0 7 55).tstore 0 8 66 with
        logs := [{emitter := 0, topics := [77], data := [0xaa]}] } } }
  locals := [[(40, ⟨.uint 0, some 23#8⟩)], [(41, ⟨.bool, some true⟩)]]
  mode := .unchecked
  materializationRemaining := 4321 }

/-- A checked callee overflows despite the caller's unchecked mode. Function
locals, heap metadata, world, arithmetic mode and work allowance all roll back. -/
example : loopRun whileOverflow 254 (state := checkpoint) =
    .ok (.finished (.failed (.panic 0x11) checkpoint)) := by rfl

private def mutation : Stmt EmptyKey :=
  .seq (.expr (.assign (.heap ⟨.uint 31, {region := .storage 0, address := 7}⟩) (word 99)))
    (.seq (.expr (.assign (.heap ⟨.uint 31, {region := .transient 0, address := 8}⟩) (word 88)))
      (.emit [word 4] [word 5]))

private def mutatingFunction : FunctionDefinition EmptyKey := {
  loopFunction (.seq mutation whileOverflow) with mutability := .nonpayable }

private def mutatingRun (value : BitVec 8 := 254) (fuel : Nat := 1000) : RunResult :=
  SourceFacade.executeFunction physicalBackend registry {} ⟨[(1, mutatingFunction)]⟩ fuel [] checkpoint
    mutatingFunction.signature 1 [.literal ⟨.uint 0, value⟩]

/-- Writes and an emitted event occur before the loop's checked overflow;
the failed invocation restores the observed slots, logs and caller fields. -/
example : (match mutatingRun 254 1000 with
    | .ok (.finished (.failed (.panic code) state)) =>
        code == 0x11 && state.heap.execution.world.storage 0 7 == 55 &&
        state.heap.execution.world.tload 0 8 == 66 &&
        decide (state.heap.execution.world.logs = checkpoint.heap.execution.world.logs) &&
        state.mode == .unchecked && state.materializationRemaining == 4321 &&
        (match state.locals.read 40 (.uint 0) with
          | .ok ⟨.uint _, value⟩ => value.toNat == 23
          | _ => false) &&
        (match state.locals.read 41 .bool with
          | .ok ⟨.bool, value⟩ => value
          | _ => false)
    | _ => false) = true := by decide +kernel

private def hasCall (stack : List (Frame EmptyKey)) : Bool :=
  stack.any fun frame => match frame with | .call .. => true | _ => false

private def inLoop (config : Config Unit EmptyKey) : Bool :=
  match config.task with
  | .loopTest .. => true
  | _ => config.stack.any fun frame => match frame with
      | .loopCondition .. | .loopBody .. | .loopPost .. => true
      | _ => false

/-- Host transition exhaustion retains the real call/loop continuation and
partial writes. It produces no source panic or native expected outcome. -/
example : (match mutatingRun 0 100 with
    | .ok (.exhausted config _) =>
        hasCall config.stack && inLoop config &&
        config.state.mode == .checked &&
        config.state.heap.execution.world.storage 0 7 == 99 &&
        config.state.heap.execution.world.tload 0 8 == 88 &&
        config.state.heap.execution.world.logs.length == 2
    | _ => false) = true ∧ outcomes (mutatingRun 0 100) = [] := by decide +kernel

/-- The corpus helpers cannot fall back to raw execution when resolved
admission rejects an invalid scalar operation. -/
example : expressionRun (.binary (.arithmetic .add) (.uint 31) (boolean true) (word 1)) =
    .error .rejected := by rfl

end Solidity.Conformance.ScalarMachine.Tests
