/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.SourceFacade
import Solidity.Core.Execution.ReadinessLaws

namespace Solidity.Execution.ReferenceReadinessTests
open Static Core Aggregates
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }
private abbrev word : SType := .uint 31
private abbrev byte : SType := .fixedBytes 0
private abbrev ref : SType := .bytes .storage true
private def number (n : Nat) : Expr EmptyKey := .literal ⟨word, BitVec.ofNat 256 n⟩
private def p : Expr EmptyKey := .local 1 ref
private def reference : Expr EmptyKey := .literal ⟨ref, {region := .storage 0, address := 0}⟩
private def assignP : Expr EmptyKey := .assign (.local 1 ref) reference
private def length : Expr EmptyKey := .length p
private def assignedLength : Expr EmptyKey := .length assignP
private def test : Expr EmptyKey := .binary (.compare .eq) .bool assignedLength (number 0)
private def readTest : Expr EmptyKey := .binary (.compare .eq) .bool length (number 0)
private def signature : FunctionSignature := ⟨.pure, .cons word .nil, .nil⟩
private def callee : Expr EmptyKey := .literal ⟨signature.type, some 1⟩
private def function : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [⟨10, word, none⟩], returns := [], body := .skip }
private def program : Program EmptyKey := ⟨[(1, function)]⟩
private def initial : MachineState Unit := {
  external := (), heap := MemoryOps.initialHeap, materializationRemaining := 1000,
  locals := [[(1, ⟨ref, none⟩)]] }
private def failure : Aggregates.Result α → Option Failure
  | .ok _ => none
  | .error problem => some problem
private def checked (expression : Expr EmptyKey) :=
  failure (Admission.admitExpression registry 256 initial.locals expression)
private def orderUnproved : Option Failure :=
  some (.unsupported "reference readiness is not established independently of operand order")
private def classify : Execution (Config Unit EmptyKey) (Observation Unit) → String
  | .exhausted _ _ => "exhausted"
  | .finished (.returned _ _) => "returned"
  | .finished (.inconclusive (.invalidContext reason) _) => reason
  | .finished _ => "source failure"
private def tuple : Expr EmptyKey := .tuple [assignP, length]

/-- The reported counterexample now fails the defined-domain check, for every
strategy. The raw machine retains both schedules rather than fixing an order. -/
example : checked tuple = orderUnproved := by decide +kernel
example : failure (SourceFacade.executeExpression physicalBackend registry {} program
    1000 [] initial tuple) = orderUnproved := by decide +kernel
example : failure (SourceFacade.executeExpression physicalBackend registry {} program
    1000 [0,1] initial tuple) = orderUnproved := by decide +kernel
example : classify (Machine.execute physicalBackend registry {} program 1000 []
    (Config.expression initial tuple)) = "returned" := by decide +kernel
example : classify (Machine.execute physicalBackend registry {} program 1000 [0,1]
    (Config.expression initial tuple)) = "uninitialized local reference" := by decide +kernel

/-- Each other eager grouping must use the same entry readiness too. -/
example : checked (.binary (.arithmetic .add) word assignedLength length) = orderUnproved := by decide +kernel
example : checked (.inlineArray word [assignedLength, length]) = orderUnproved := by decide +kernel
example : checked (.call signature (.conditional test callee callee) [length]) = orderUnproved := by decide +kernel
example : checked (.namedCall signature (.conditional test callee callee) [length] [0]) = orderUnproved := by decide +kernel
example : checked (.index byte assignP length) = orderUnproved := by decide +kernel
example : checked (.require_ (.custom 0 (.cons word .nil)) test [length]) = orderUnproved := by decide +kernel
private def byteFromP : Expr EmptyKey :=
  .cast (.explicit .ordinary) byte (.cast (.explicit .ordinary) (.uint 0) length)
example : checked (.push assignP byteFromP) = orderUnproved := by decide +kernel

/-- Destination selectors can run before the RHS. Pattern targets are captured
before any pattern write, so a sibling target cannot initialize their base. -/
private def indexed : LValue EmptyKey := .index byte p (number 0)
private def right : Expr EmptyKey := .index byte assignP (number 0)
example : checked (.assign indexed right) = orderUnproved := by decide +kernel
example : checked (.tupleAssign (.tuple [.target (.local 1 ref), .target indexed])
    (.tuple [reference, .literal ⟨byte, 0⟩])) = orderUnproved := by decide +kernel
example : checked (.tupleAssign (.target indexed) right) = orderUnproved := by decide +kernel
example : checked (.compound (.bits .bitxor) indexed right) = orderUnproved := by decide +kernel

private def mapping : Expr EmptyKey :=
  .literal ⟨.mapping word word, {region := .storage 0, address := 9}⟩
example : checked (.read (.mapping word (.conditional test mapping mapping) length)) =
    orderUnproved := by decide +kernel

private def structRegistry : Registry := {registry with
  structures := fun id => id == 4,
  structFields := fun id => if id == 4 then some [("first",word),("second",word)] else none }
example : failure (Admission.admitExpression structRegistry 256 initial.locals
    (.structConstructor 4 [assignedLength, length] [0,1])) = orderUnproved := by decide +kernel

private abbrev calldataType : SType := .bytes .calldata false
private def calldataValue : Expr EmptyKey :=
  .literal ⟨calldataType, {region := .calldata 0, address := 0}⟩
example : failure (Admission.admitExpression registry 256 [[(2,⟨calldataType,none⟩)]]
    (.slice (.assign (.local 2 calldataType) calldataValue)
      (some (.length (.local 2 calldataType))) none)) = orderUnproved := by decide +kernel

/-- Required sequencing remains available, both inside a child and between
statements. Conditional branches and Boolean short circuiting remain lazy. -/
example : checked (.binary .and .bool test readTest) = none := by decide +kernel
example : checked (.conditional test length length) = none := by decide +kernel
example : checked (.tuple [.conditional test length length, number 7]) = none := by decide +kernel
example : failure (Admission.admitStatement registry 256 initial.locals []
    (.seq (.expr assignP) (.expr length))) = none := by decide +kernel
example : failure (Admission.admitStatement registry 256 initial.locals []
    (.seq (.expr (.tuple [assignP, number 7])) (.expr length))) = none := by decide +kernel

private def ready : MachineState Unit :=
  {initial with locals := [[(1, ⟨ref, some {region := .storage 0, address := 7}⟩)]]}
example : failure (Admission.admitExpression registry 256 ready.locals tuple) = none := by decide +kernel
example : classify (Machine.execute physicalBackend registry {} program 1000 []
    (Config.expression ready tuple)) = "returned" := by decide +kernel
example : classify (Machine.execute physicalBackend registry {} program 1000 [0,1]
    (Config.expression ready tuple)) = "returned" := by decide +kernel

/-- Direct definitely-uninitialized source reads keep their original static
rejection class; unrelated source-permission errors are not reclassified. -/
example : checked length = some .rejected := by decide +kernel
example : checked (.binary (.arithmetic .add) .bool (number 1) (number 2)) = some .rejected := by decide +kernel

/-- Topics and data form a single eager group in the actual machine. -/
private def event : Stmt EmptyKey := .emit [assignedLength] [length]
example : failure (Admission.admitStatement registry 256 initial.locals [] event) =
    orderUnproved := by decide +kernel
example : failure (SourceFacade.executeStatement physicalBackend registry {} program
    1000 [0,1] initial event) = orderUnproved := by decide +kernel
example : classify (Machine.execute physicalBackend registry {} program 1000 []
    (Config.start initial event)) = "returned" := by decide +kernel
example : classify (Machine.execute physicalBackend registry {} program 1000 [0,1]
    (Config.start initial event)) = "uninitialized local reference" := by decide +kernel

end Solidity.Execution.ReferenceReadinessTests
