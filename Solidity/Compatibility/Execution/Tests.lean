/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Expressions
import Solidity.Compatibility.Execution.Observations

namespace Solidity.Execution.Compatibility.Tests
open Core Static
open Contract.Interaction (Word wordBytes)

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }

inductive Counter : Core.Ty → Type where
  | counter : Counter .word

private def store : Core.Store Counter Counter Nat where
  read state := fun {_} reference => match reference with | .counter => BitVec.ofNat 256 state
  write _ := fun {_} place value => match place with | .counter => some value.toNat

private def runBlock (body : Core.Block Counter Counter) (state : Nat)
    (fallthroughBytes : List UInt8) : Option (List UInt8 × Nat) :=
  match Machine.execute (Compatibility.backend store) registry legacyLimits {} 20000 []
      (Config.start (initial state Core.Env.nil) (blockBody body)) with
  | .finished observed => match blockObservation observed with
      | some (.next after) => some (fallthroughBytes, after)
      | some (.halt (.returned bytes after)) => some (bytes, after)
      | _ => none
  | _ => none

/-- Arbitrary raw deployment/fallthrough bytes are applied only to the marker.
An explicit stop and a uint256 return have different actual machine packets. -/
example : runBlock .skip 3 [0xaa, 0xbb] = some ([0xaa, 0xbb], 3) := by decide +kernel
example : runBlock .stop 3 [0xaa, 0xbb] = some ([], 3) := by decide +kernel
example : runBlock (.ret (.literal 7)) 3 [0xaa, 0xbb] = some (wordBytes 7, 3) := by decide +kernel
example : runBlock (.seq (.assign .counter (.literal 7)) .skip) 3 [0xaa] = some ([0xaa], 7) := by decide +kernel

private def helper : Core.Procedure Counter Counter [.word] [.word] :=
  .emit (by decide) .nil (.cons (.read (.local .here)) .nil)
    (.store .counter (.binary (.uintArithmetic 31 .checked .add) (.read (.local .here)) (.literal 1))
      (.ret (.cons (.read (.global .counter)) .nil)))

private def caller : Core.Procedure Counter Counter [.word] [.word] :=
  .call helper (.cons (.literal 2) .nil)
    (.ret (.cons (.binary (.uintArithmetic 31 .checked .add)
      (.read (.local .here)) (.read (.local (.there .here)))) .nil))

private def runCaller : Option (Nat × Nat × List (List UInt8)) :=
  let compiled := procedure 0 caller
  match Machine.execute (Compatibility.backend store) registry legacyLimits (program compiled) 20000 []
      (Config.start (initial 0 (.cons (type := .word) 10 .nil) 5) compiled.body) with
  | .finished observed => match procedureObservation [.word] observed with
      | some (.returned after (.cons value .nil) logs) => some (after, value.toNat, logs.map (·.data))
      | _ => none
  | _ => none

/-- Real call frames preserve the caller local10, transfer result3, and retain
the helper's event before returning13. No legacy evaluator opcode is used. -/
example : runCaller = some (3, 13, [wordBytes 2]) := by decide +kernel

private def failingHelper : Core.Procedure Counter Counter [.word] [.word] :=
  .emit (by decide) .nil (.cons (.read (.local .here)) .nil)
    (.store .counter (.literal 7) (.revert [0xee]))

private def runFailure : Option (Nat × Nat × List UInt8) :=
  let caller : Core.Procedure Counter Counter [.word] [] :=
    .call failingHelper (.cons (.literal 2) .nil) (.ret (.cons (.read (.local .here)) .nil))
  let compiled := procedure 0 caller
  match Machine.execute (Compatibility.backend store) registry legacyLimits (program compiled) 20000 []
      (Config.start (initial 3 Core.Env.nil) compiled.body) with
  | .finished (.failed (.revert bytes) restored) =>
      some (restored.external, restored.heap.execution.world.logs.length, bytes)
  | _ => none

example : runFailure = some (3, 0, [0xee]) := by decide +kernel

private def mixedMode : Core.Expr Counter (.uint 0) :=
  .binary (.uintArithmetic 0 .checked .add)
    (.binary (.uintArithmetic 0 .unchecked .add) (.literal 255) (.literal 1)) (.literal 1)

private def runMixedMode : Option (Nat × Bool) :=
  let state := {initial 0 Core.Env.nil with mode := .unchecked}
  match Machine.execute (Compatibility.backend store) registry legacyLimits {} 20000 []
      (Config.expression state (externalExpression mixedMode)) with
  | .finished (.returned [.atom ⟨.uint _, value⟩] after) => some (value.toNat, after.mode == .unchecked)
  | _ => none

example : runMixedMode = some (1, true) := by decide +kernel

end Solidity.Execution.Compatibility.Tests
