/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.TypedStatements

namespace Solidity.Execution.Compatibility.TypedTests
open Core Static
open Contract.Interaction (Word wordBytes)

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 4096

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }

private def helper : Contract.Stmt 1 [.bool, .address, .word] [.bool, .address] :=
  .store 0 (.word 7)
    (.emit (by decide) (.cons .self .nil) (.cons (.var .here) (.cons (.var (.there .here)) .nil))
      (.ret (.cons (.var .here) (.cons (.var (.there .here)) (.cons (.load 0) .nil)))))

private def caller : Contract.Stmt 1 [.bool, .address, .word] [.word] :=
  .call helper (.cons (.bool true) (.cons .caller .nil))
    (.assign (.there (.there .here))
      (.add (.var (.there (.there .here))) (.var (.there (.there (.there .here)))))
      (.ret (.cons (.var .here) (.cons (.var (.there .here)) (.cons (.var (.there (.there .here))) .nil)))))

private def context : Contract.Context := {caller := 19, self := 42}
private def environment : Contract.Env [.word] := .cons 10 .nil
private def storage : Contract.Storage 1 := fun _ => 3

private def runTypedCaller : Option (List Nat × Nat × List (Nat × List Nat × List UInt8)) :=
  let body := Solidity.Compatibility.Typed.procedure caller
  let state := initial storage (Solidity.Compatibility.Typed.environment environment) context.self
  match Machine.execute (backend (Solidity.Compatibility.Typed.frameStore context)) registry legacyLimits
      (procedureProgram body) 20000 [] (procedureConfig body state (Solidity.Compatibility.Typed.environment environment)) with
  | .finished (.returned packet state) => match Machine.encodePacket packet with
      | .ok values => some (values.map BitVec.toNat, (state.external 0).toNat,
          state.heap.execution.world.logs.map fun event => (event.emitter.toNat, event.topics.map BitVec.toNat, event.data))
      | _ => none
  | _ => none

/-- Three typed helper results pass through actual odd return cells and shifted
even caller bindings. The caller's older local10 survives the helper call. -/
example : runTypedCaller = some ([1, 19, 17], 7, [(42, [42], wordBytes 1 ++ wordBytes 19)]) := by decide +kernel

private def failingHelper : Contract.Stmt 1 [.word] [] :=
  .store 0 (.word 7) (.emit (by decide) .nil (.cons (.word 9) .nil) (.revert [0xee]))
private def failing : Contract.Stmt 1 [.word] [] :=
  .call failingHelper .nil
    (.ret (.cons (.var .here) .nil))

private def runFailure : Option (Nat × Nat × List UInt8) :=
  let body := Solidity.Compatibility.Typed.procedure failing
  let state := initial storage Core.Env.nil context.self
  match Machine.execute (backend (Solidity.Compatibility.Typed.frameStore context)) registry legacyLimits
      (procedureProgram body) 20000 [] (procedureConfig body state Core.Env.nil) with
  | .finished (.failed (.revert bytes) state) =>
      some ((state.external 0).toNat, state.heap.execution.world.logs.length, bytes)
  | _ => none

example : runFailure = some (3, 0, [0xee]) := by decide +kernel

/-- The attachment theorem has no normalized raw-store or callee execution
premise, and retains the complete legacy result and event observation. -/
example (state : Contract.Storage slots) (ctx : Contract.Context) (env : Contract.Env vars)
    (body : Contract.Stmt slots returns vars) :
    ∃ observed,
      Executes (transition (backend (Solidity.Compatibility.Typed.frameStore ctx)) registry
          (procedureProgram (Solidity.Compatibility.Typed.procedure body)))
        (procedureConfig (Solidity.Compatibility.Typed.procedure body)
          (initial state (Solidity.Compatibility.Typed.environment env) ctx.self)
          (Solidity.Compatibility.Typed.environment env)) observed ∧
      procedureObservation (Solidity.Compatibility.Typed.types returns) observed =
        some (Solidity.Compatibility.Typed.procedureOutcome (body.eval state ctx env)) :=
  Solidity.Compatibility.Typed.statement_machine body state ctx env registry

end Solidity.Execution.Compatibility.TypedTests
