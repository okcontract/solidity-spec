/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.MachineProofs
import Solidity.Core.Aggregates.Memory

namespace Solidity.Execution.Tests
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Static
open Core (ArithmeticMode)
open Machine

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }
private def initial : MachineState Unit := ⟨(), Aggregates.MemoryOps.initialHeap, Locals.empty, .checked, 10000⟩
private def word : SType := .uint 31
private def number (n : Nat) : Expr EmptyKey := .literal ⟨word, BitVec.ofNat 256 n⟩
private def readLocal (id : Nat) : Expr EmptyKey := .local id word
private def target (id : Nat) : LValue EmptyKey := .local id word
private def set (id : Nat) (value : Expr EmptyKey) : Stmt EmptyKey := .expr (.assign (target id) value)
private def decl (id : Nat) (value : Expr EmptyKey) : Stmt EmptyKey := .declare [some ⟨id, word, none⟩] (some value)
private def add (a b : Expr EmptyKey) : Expr EmptyKey := .binary (.arithmetic .add) word a b
private def mul (a b : Expr EmptyKey) : Expr EmptyKey := .binary (.arithmetic .mul) word a b
private def eq (a b : Expr EmptyKey) : Expr EmptyKey := .binary (.compare .eq) .bool a b
private def lt (a b : Expr EmptyKey) : Expr EmptyKey := .binary (.compare .lt) .bool a b
private def sequence (statements : List (Stmt EmptyKey)) : Stmt EmptyKey := statements.foldr Stmt.seq .skip

private def outcomeWord : Execution (Config Unit EmptyKey) (Observation Unit) → Option Nat
  | .finished (.returned [.atom ⟨.uint _, value⟩] _) => some value.toNat
  | _ => none

private def outcomeFailure : Execution (Config Unit EmptyKey) (Observation Unit) → Option Aggregates.Failure
  | .finished (.failed failure _) => some failure
  | .finished (.inconclusive failure _) => some failure
  | _ => none

private def runBody (body : Stmt EmptyKey) (program : Program EmptyKey := {}) (choices : List Nat := []) :=
  execute physicalBackend registry {} program 2000 choices (Config.start initial body)

private def scopeExample : Stmt EmptyKey := sequence [
  decl 0 (number 1), .block (sequence [decl 1 (number 99), set 0 (number 7)]), .return_ (some (readLocal 0))]
example : outcomeWord (runBody scopeExample) = some 7 := by decide +kernel

private def forExample : Stmt EmptyKey := sequence [decl 0 (number 0),
  .for_ (decl 1 (number 0)) (some (lt (readLocal 1) (number 6)))
    (.expr (.update (.inc false) (target 1)))
    (.block (sequence [.if_ (eq (readLocal 1) (number 1)) .continue_ .skip,
      .if_ (eq (readLocal 1) (number 4)) .break_ .skip,
      set 0 (add (readLocal 0) (number 1))])),
  .return_ (some (readLocal 0))]
example : outcomeWord (runBody forExample) = some 3 := by decide +kernel

private def doExample : Stmt EmptyKey := sequence [decl 0 (number 0),
  .doWhile (.block (sequence [.expr (.update (.inc false) (target 0)), .continue_])) (lt (readLocal 0) (number 3)),
  .return_ (some (readLocal 0))]
example : outcomeWord (runBody doExample) = some 3 := by decide +kernel

private def tupleExample : Stmt EmptyKey := sequence [decl 0 (number 1), decl 1 (number 2),
  .expr (.tupleAssign (.tuple [.target (target 0), .hole, .target (target 1)])
    (.tuple [readLocal 1, number 99, readLocal 0])),
  .return_ (some (add (mul (number 10) (readLocal 0)) (readLocal 1)))]
example : outcomeWord (runBody tupleExample) = some 21 := by decide +kernel

private def nestedTuple : Stmt EmptyKey := sequence [decl 0 (number 0), decl 1 (number 0),
  .expr (.tupleAssign (.tuple [.tuple [.target (target 0), .hole], .target (target 1)])
    (.tuple [.tuple [number 4, number 88], number 7])),
  .return_ (some (add (mul (number 10) (readLocal 0)) (readLocal 1)))]
example : outcomeWord (runBody nestedTuple) = some 47 := by decide +kernel

private def shortCircuit : Stmt EmptyKey := sequence [decl 0 (number 0),
  .expr (.binary .and .bool (.literal ⟨.bool, false⟩) (eq (.assign (target 0) (number 9)) (number 9))),
  .expr (.conditional (.literal ⟨.bool, true⟩) (number 1) (.binary (.arithmetic .div) word (number 1) (number 0))),
  .return_ (some (readLocal 0))]
example : outcomeWord (runBody shortCircuit) = some 0 := by decide +kernel

private def signature : FunctionSignature := ⟨.pure, .cons word .nil, .cons word .nil⟩
private def function (handle : Option Nat) : Expr EmptyKey := .literal ⟨signature.type, handle⟩
private def factorial : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [⟨0, word, none⟩], returns := [⟨1, word, none⟩],
  body := .if_ (eq (readLocal 0) (number 0)) (.return_ (some (number 1)))
    (.return_ (some (mul (readLocal 0) (.call signature (function (some 7))
      [.binary (.arithmetic .sub) word (readLocal 0) (number 1)])))) }
private def functions : Program EmptyKey := ⟨[(7, factorial)]⟩
example : outcomeWord (runBody (.return_ (some (.call signature (function (some 7)) [number 5]))) functions) = some 120 := by decide +kernel

private def named : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [⟨0, word, none⟩], returns := [⟨1, word, none⟩],
  body := sequence [set 1 (add (readLocal 0) (number 3)), .return_ none] }
example : outcomeWord (runBody (.return_ (some (.call signature (function (some 9)) [number 4]))) ⟨[(9, named)]⟩) = some 7 := by decide +kernel

private def byteSig : FunctionSignature := ⟨.pure, .nil, .cons (.uint 0) .nil⟩
private def checkedHelper : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [], returns := [⟨0, .uint 0, none⟩],
  body := .return_ (some (.binary (.arithmetic .add) (.uint 0)
    (.literal ⟨.uint 0, 255⟩) (.literal ⟨.uint 0, 1⟩))) }
private def modeCall : Stmt EmptyKey := .arithmetic .unchecked
  (.return_ (some (.call byteSig (.literal ⟨byteSig.type, some 10⟩) [])))
example : outcomeFailure (runBody modeCall ⟨[(10, checkedHelper)]⟩) = some (.panic 0x11) := by decide +kernel

example : outcomeFailure (runBody (.return_ (some (.call signature (function none) [number 0])))) = some (.panic 0x51) := by decide +kernel
example : outcomeFailure (runBody (.return_ (some (.call signature (function (some 99)) [number 0])))) =
    some (.invalidContext "unresolved internal function handle") := by decide +kernel

private def multiSig : FunctionSignature := ⟨.pure, .nil, .cons word (.cons word .nil)⟩
private def multi : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [], returns := [⟨0, word, none⟩, ⟨1, word, none⟩],
  body := .return_ (some (.tuple [number 4, number 8])) }
private def multiCall : Stmt EmptyKey := sequence [decl 0 (number 0), decl 1 (number 0),
  .expr (.tupleAssign (.tuple [.target (target 0), .target (target 1)])
    (.call multiSig (.literal ⟨multiSig.type, some 8⟩) [])),
  .return_ (some (add (mul (readLocal 0) (number 10)) (readLocal 1)))]
example : outcomeWord (runBody multiCall ⟨[(8, multi)]⟩) = some 48 := by decide +kernel

private def suspended : Bool := match execute physicalBackend registry {} ({} : Program EmptyKey) 10 []
    (Config.start initial (.while_ (.literal ⟨.bool, true⟩) .skip)) with
  | .exhausted _ _ => true
  | _ => false
example : suspended = true := by decide +kernel

private def limitObserved : Bool := match execute physicalBackend registry ⟨128, some 0⟩ ({} : Program EmptyKey) 10 []
    (Config.start initial (.seq .skip .skip)) with
  | .exhausted config _ => config.state.mode == initial.mode
  | _ => false
example : limitObserved = true := by decide +kernel

private def targetObserved : Bool := match run
    (targetStep (fun _ _ => some .stack) physicalBackend registry {} ({} : Program EmptyKey)) 10 []
    (Config.start initial (.seq .skip .skip)) with
  | .finished (.resourceLimit .stack state) => state.mode == initial.mode
  | _ => false
example : targetObserved = true := by decide +kernel

private def memoryArray : SType := .array word none .memory true
private def refSignature : FunctionSignature := ⟨.pure, .cons memoryArray .nil, .cons word .nil⟩
private def referenceHelper : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [⟨0, memoryArray, none⟩], returns := [⟨1, word, none⟩],
  body := sequence [.expr (.assign (.index word (.local 0 memoryArray) (number 0)) (number 7)), .return_ (some (number 0))] }
private def referenceCall : Stmt EmptyKey := sequence [
  .declare [some ⟨0, memoryArray, none⟩] (some (.newArray word (number 2))),
  .expr (.call refSignature (.literal ⟨refSignature.type, some 11⟩) [.local 0 memoryArray]),
  .return_ (some (.index word (.local 0 memoryArray) (number 0)))]
example : outcomeWord (runBody referenceCall ⟨[(11, referenceHelper)]⟩) = some 7 := by decide +kernel

private def effectsBeforeFailure : Stmt EmptyKey := sequence [
  .emit [number 3] [number 5], .expr (.assign (.heap ⟨word, {region := .storage 0, address := 1}⟩) (number 9)),
  .revert [0xaa]]
private def rollbackObserved : Bool := match runBody effectsBeforeFailure with
  | .finished (.failed (.revert [0xaa]) state) =>
      state.heap.execution.world.logs.isEmpty && state.heap.execution.world.storage 0 1 == 0
  | _ => false
example : rollbackObserved = true := by decide +kernel

private def staticLog : Bool :=
  let state := {initial with heap := {initial.heap with execution := {initial.heap.execution with
    context := {initial.heap.execution.context with readOnly := true}}}}
  match execute physicalBackend registry {} ({} : Program EmptyKey) 100 []
      (Config.start state (.emit [] [number 1])) with
  | .finished (.failed .exceptional state) => state.heap.execution.world.logs.isEmpty
  | _ => false
example : staticLog = true := by decide +kernel

-- Diagnostic raw-header boundary: return conversions must preserve their
-- declaration order. The first copy panics41, while the second would panic22.
-- This fixture does not claim source admission of the raw header setup.
private def nestedMemory : SType := .array (.bytes .memory false) none .memory true
private def returnOrderSignature : FunctionSignature :=
  ⟨.view, .nil, .cons nestedMemory (.cons (.bytes .memory true) .nil)⟩
private def returnOrderFunction : FunctionDefinition EmptyKey := {
  mutability := .view, parameters := [],
  returns := [⟨0, nestedMemory, none⟩, ⟨1, .bytes .memory true, none⟩],
  body := .return_ (some (.tuple [
    .read (.heap ⟨.array (.bytes .storage false) none .storage false, {region := .storage 0, address := 0}⟩),
    .read (.heap ⟨.bytes .storage false, {region := .storage 0, address := 1}⟩)])) }
private def resultOrderObserved : Option Aggregates.Failure :=
  let heap := initial.heap
  let world := {heap.execution.world with storage := fun owner slot =>
    if owner == 0 && slot == 0 then BitVec.ofNat 256 (2^64)
    else if owner == 0 && slot == 1 then 1 else 0}
  let state := {initial with heap := {heap with execution := {heap.execution with world}}}
  outcomeFailure (execute physicalBackend registry {} ⟨[(20, returnOrderFunction)]⟩ 200 []
    (Config.expression state (.call returnOrderSignature (.literal ⟨returnOrderSignature.type, some 20⟩) [])))
example : resultOrderObserved = some (.panic 0x41) := by decide +kernel

private def partialContext : Bool := match runBody (sequence [
    .expr (.assign (.heap ⟨word, {region := .storage 0, address := 1}⟩) (number 9)),
    .expr (.local 999 word)]) with
  | .finished (.inconclusive (.invalidContext _) state) => state.heap.execution.world.storage 0 1 == 9
  | _ => false
example : partialContext = true := by decide +kernel

example : outcomeFailure (runBody (.expr (.assert_ (.literal ⟨.bool, false⟩)))) = some (.panic 0x01) := by decide +kernel

private def eagerRequire : Stmt EmptyKey := sequence [decl 0 (number 0),
  .expr (.require_ (.custom 0x12345678 (.cons word .nil)) (.literal ⟨.bool, true⟩)
    [.assign (target 0) (number 7)]), .return_ (some (readLocal 0))]
example : outcomeWord (runBody eagerRequire) = some 7 := by decide +kernel

end Solidity.Execution.Tests
