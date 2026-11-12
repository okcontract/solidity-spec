/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.SourceFacade
import Solidity.Core.Execution.MachineProofs

namespace Solidity.Execution.InternalCallConversionTests
open Static Aggregates

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }
private def initial : MachineState Unit := {
  external := (), heap := MemoryOps.initialHeap, materializationRemaining := 1000 }
private abbrev word : SType := .uint 31
private def parameterTypes : Types := .cons word .nil
private def resultTypes : Types := .cons word .nil
private def pureSignature : FunctionSignature := ⟨.pure, parameterTypes, resultTypes⟩
private def viewSignature : FunctionSignature := ⟨.view, parameterTypes, resultTypes⟩
private def nonpayableSignature : FunctionSignature := ⟨.nonpayable, parameterTypes, resultTypes⟩
private def pureFunction : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [⟨0, word, none⟩], returns := [⟨1, word, none⟩],
  body := .return_ (some (.local 0 word)) }
private def viewFunction : FunctionDefinition EmptyKey := {pureFunction with mutability := .view}
private def pairSignature (mutability : Mutability) : FunctionSignature :=
  ⟨mutability, .cons word (.cons word .nil), resultTypes⟩
private def pairFunction : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [⟨0, word, none⟩, ⟨1, word, none⟩], returns := [⟨2, word, none⟩],
  body := .return_ (some (.binary (.arithmetic .add) word
    (.binary (.arithmetic .mul) word (.local 0 word) (.literal ⟨word, 10⟩)) (.local 1 word))) }
private def voidSignature (mutability : Mutability) : FunctionSignature := ⟨mutability, .nil, .nil⟩
private def voidFunction : FunctionDefinition EmptyKey := {mutability := .pure, parameters := [], returns := [], body := .skip}
private def program : Program EmptyKey := ⟨[(1, pureFunction), (2, viewFunction), (3, pairFunction), (4, voidFunction)]⟩
private def argument : Expr EmptyKey := .literal ⟨.uint 0, 37⟩
private def run (expression : Expr EmptyKey) :=
  SourceFacade.executeExpression physicalBackend registry {} program 1000 [] initial expression
private def number : Aggregates.Result (Execution (Config Unit EmptyKey) (Observation Unit)) → Option Nat
  | .ok (.finished (.returned [.atom ⟨.uint _, value⟩] _)) => some value.toNat
  | _ => none
private def sourceFailure : Aggregates.Result (Execution (Config Unit EmptyKey) (Observation Unit)) → Option Failure
  | .ok (.finished (.failed failure _)) => some failure
  | _ => none
private def admissionFailure : Aggregates.Result α → Option Failure
  | .error failure => some failure
  | .ok _ => none
private def returned : Aggregates.Result (Execution (Config Unit EmptyKey) (Observation Unit)) → Bool
  | .ok (.finished (.returned _ _)) => true
  | _ => false

/-- The admitted implicit callee conversion uses the same path as the
explicitly materialized implicit cast, including ordinary argument widening. -/
example : number (run (.call viewSignature (.literal ⟨pureSignature.type, some 1⟩) [argument])) = some 37 := by decide +kernel
example : number (run (.call viewSignature
    (.cast .implicit viewSignature.type (.literal ⟨pureSignature.type, some 1⟩)) [argument])) = some 37 := by decide +kernel
example : number (run (.call pureSignature (.literal ⟨pureSignature.type, some 1⟩) [argument])) = some 37 := by decide +kernel
example : number (run (.call nonpayableSignature (.literal ⟨pureSignature.type, some 1⟩) [argument])) = some 37 := by decide +kernel
example : number (run (.call nonpayableSignature (.literal ⟨viewSignature.type, some 2⟩) [argument])) = some 37 := by decide +kernel
example : returned (run (.call (voidSignature .view) (.literal ⟨(voidSignature .pure).type, some 4⟩) [])) = true := by decide +kernel

example : number (run (.namedCall (pairSignature .view) (.literal ⟨(pairSignature .pure).type, some 3⟩)
    [.literal ⟨.uint 0, 7⟩, .literal ⟨.uint 0, 3⟩] [1,0])) = some 37 := by decide +kernel

/-- Narrowing mutability and changing parameter/result shapes still reject
at admission; a wider view does not change which table entry can be called. -/
example : admissionFailure (run (.call pureSignature (.literal ⟨viewSignature.type, some 2⟩) [argument])) =
    some .rejected := by decide +kernel
example : admissionFailure (run (.call viewSignature (.literal ⟨(voidSignature .pure).type, some 4⟩) [argument])) =
    some .rejected := by decide +kernel
example : sourceFailure (run (.call viewSignature (.literal ⟨pureSignature.type, none⟩) [argument])) =
    some (.panic 0x51) := by decide +kernel

private def argumentEffects : Option (Nat × Nat) :=
  match run (.call viewSignature (.literal ⟨pureSignature.type, some 1⟩)
      [.assign (.heap ⟨word, {region := .storage 0, address := 5}⟩) argument]) with
  | .ok (.finished (.returned [.atom ⟨.uint _, value⟩] after)) =>
      some (value.toNat, (after.heap.execution.world.storage 0 5).toNat)
  | _ => none
example : argumentEffects = some (37,37) := by decide +kernel

/-- Diagnostic raw-header boundary: parameter conversion must still occur
before null dispatch. Invalid storage bytes panic22, rather than null panic51.
No source admission of this corrupt physical header is asserted. -/
private def nullConversionFailure : Option Failure :=
  let heap := initial.heap
  let world := {heap.execution.world with storage := fun owner slot => if owner == 0 && slot == 7 then 1 else 0}
  let state := {initial with heap := {heap with execution := {heap.execution with world}}}
  let actual : FunctionSignature := ⟨.pure, .cons (.bytes .memory true) .nil, .nil⟩
  let expected : FunctionSignature := ⟨.view, .cons (.bytes .memory true) .nil, .nil⟩
  match Machine.invoke physicalBackend registry {} program
      (Config.expression state (.literal ⟨actual.type, none⟩)) expected ⟨actual.type, none⟩
      [.atom ⟨.bytes .storage false, {region := .storage 0, address := 7}⟩] with
  | .error failure => some failure
  | .ok _ => none
example : nullConversionFailure = some (.panic 0x22) := by decide +kernel

end Solidity.Execution.InternalCallConversionTests
