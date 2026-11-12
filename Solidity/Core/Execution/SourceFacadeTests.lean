/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.SourceFacade

namespace Solidity.Execution.SourceFacade.Tests
open Static Core Aggregates
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }
private def initial : MachineState Unit := {
  external := (), heap := MemoryOps.initialHeap, materializationRemaining := 1000 }
private def u (value : Nat) : Expr EmptyKey := .literal ⟨.uint 31, BitVec.ofNat 256 value⟩
private def b (value : Bool) : Expr EmptyKey := .literal ⟨.bool, value⟩
private def empty : Program EmptyKey := ⟨[]⟩
private def runExpression (expression : Expr EmptyKey) (limits : Limits := {}) (fuel : Nat := 1000) :=
  executeExpression physicalBackend registry limits empty fuel [] initial expression
private def classify : Aggregates.Result (Execution (Config Unit EmptyKey) (Observation Unit)) → String
  | .error .rejected => "rejected"
  | .error .exhausted => "admissionExhausted"
  | .error (.unsupported _) => "admissionUnsupported"
  | .error _ => "otherAdmissionFailure"
  | .ok (.exhausted _ _) => "suspended"
  | .ok (.finished (.returned _ _)) => "returned"
  | .ok (.finished (.failed (.panic _) _)) => "panic"
  | .ok (.finished (.inconclusive (.unsupported _) _)) => "executionUnsupported"
  | .ok (.finished _) => "otherObservation"

example : classify (runExpression (.conditional (b true) (u 7) (.unary .neg (u 2)))) =
    "rejected" := by decide +kernel
example : classify (runExpression (.binary .and .bool (b false) (.cast .implicit .bool (u 1)))) =
    "rejected" := by decide +kernel
example : classify (runExpression (.binary (.arithmetic .div) (.uint 31) (u 1) (u 0))) =
    "panic" := by decide +kernel
example : classify (runExpression (u 7) {aggregateFuel := 0}) = "admissionExhausted" := by decide +kernel
example : classify (runExpression (u 7) {} 0) = "suspended" := by decide +kernel
example : classify (runExpression (.newArray (.fixedPoint true 15 18) (u 1))) =
    "executionUnsupported" := by decide +kernel
example : classify (executeStatement physicalBackend registry {} empty 100 [] initial
    (.arithmetic .unchecked (.arithmetic .unchecked .skip))) = "rejected" := by decide +kernel
example : classify (executeStatement physicalBackend registry {} empty 100 [] initial
    (.emit [] [.bytesLiteral false [1]])) = "admissionUnsupported" := by decide +kernel

private def successor : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [⟨0, .uint 0, none⟩], returns := [⟨1, .uint 0, some "result"⟩],
  body := .seq (.expr (.assign (.local 1 (.uint 0))
    (.binary (.arithmetic .add) (.uint 0) (.local 0 (.uint 0)) (.literal ⟨.uint 0, 1⟩)))) (.return_ none) }
private def signature : FunctionSignature := ⟨.pure, .cons (.uint 0) .nil, .cons (.uint 0) .nil⟩
private def resultNumber : Aggregates.Result (Execution (Config Unit EmptyKey) (Observation Unit)) → Option Nat
  | .ok (.finished (.returned [.atom ⟨.uint _, value⟩] _)) => some value.toNat
  | _ => none

example : resultNumber (executeFunction physicalBackend registry {} ⟨[(1, successor)]⟩
    1000 [] initial signature 1 [.literal ⟨.uint 0, 4⟩]) = some 5 := by decide +kernel
example : classify (executeFunction physicalBackend registry {} ⟨[(1, successor), (1, successor)]⟩
    1000 [] initial signature 1 [.literal ⟨.uint 0, 4⟩]) = "rejected" := by decide +kernel
example : classify (executeExpression physicalBackend registry {}
    ⟨[(1, successor), (2, {parameters := [], returns := [], body := .break_})]⟩ 1000 [] initial (u 7)) =
    "rejected" := by decide +kernel

end Solidity.Execution.SourceFacade.Tests
