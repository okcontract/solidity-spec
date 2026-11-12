/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Machine
import Solidity.Core.Execution.Admission
import Solidity.Target
import Lean.Data.Json.FromToJson

/-! Manually paired Solidity bodies and closed programs in the shared continuation
machine. No operation-specific evaluator supplies expected outcomes. Named
finite strategies select independent machine transitions; Source parsing and
external ABI admission are explicit source/model input assumptions. -/
namespace Solidity.Conformance.Effects
open Static Core Execution Aggregates Lean
open Contract.Interaction (Word wordBytes)

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun identity => identity < 2,
  structFields := fun
    | 0 => some [("a", .uint 31), ("b", .uint 31)]
    | 1 => some [("a", .array (.uint 0) none .memory false), ("ignored", .uint 31)]
    | _ => none }
private def initial : MachineState Unit := {
  external := (), heap := MemoryOps.initialHeap, materializationRemaining := 100000 }
private def word : SType := .uint 31
private def byte : SType := .uint 0
private def memoryArray : SType := .array byte none .memory true
private def storageArray : SType := .array byte none .storage true
private def memoryBytes : SType := .bytes .memory true
private def arrayPlace (slot : Nat) : Place :=
  ⟨.array byte none .storage false, {region := .storage 0, address := BitVec.ofNat 256 slot}⟩
private def scalarPlace (slot : Nat) : Place := ⟨word, {region := .storage 0, address := BitVec.ofNat 256 slot}⟩
private def n (value : Nat) : Expr EmptyKey := .literal ⟨word, BitVec.ofNat 256 value⟩
private def b (value : Nat) : Expr EmptyKey := .literal ⟨byte, BitVec.ofNat 8 value⟩
private def truth (value : Bool) : Expr EmptyKey := .literal ⟨.bool, value⟩
private def var (id : Nat) (type : SType := word) : Expr EmptyKey := .local id type
private def target (id : Nat) (type : SType := word) : LValue EmptyKey := .local id type
private def global (slot : Nat) : Expr EmptyKey := .read (.heap (scalarPlace slot))
private def array (slot : Nat := 3) : Expr EmptyKey := .read (.heap (arrayPlace slot))
private def bin (code : BinaryCode) (type : SType) (a b : Expr EmptyKey) : Expr EmptyKey := .binary code type a b
private def add := bin (.arithmetic .add) word
private def mul := bin (.arithmetic .mul) word
private def eq := bin (.compare .eq) .bool
private def lt := bin (.compare .lt) .bool
private def sub := bin (.arithmetic .sub) word
private def seq (values : List (Stmt EmptyKey)) : Stmt EmptyKey := values.foldr Stmt.seq .skip
private def binder (id : Nat) (type : SType := word) : Binder := {id, type}
private def declare (id : Nat) (value : Expr EmptyKey) (type : SType := word) : Stmt EmptyKey :=
  .declare [some (binder id type)] (some value)
private def set (id : Nat) (value : Expr EmptyKey) (type : SType := word) : Stmt EmptyKey :=
  .expr (.assign (target id type) value)
private def store (slot : Nat) (value : Expr EmptyKey) : Stmt EmptyKey := .expr (.assign (.heap (scalarPlace slot)) value)
private def ret (value : Expr EmptyKey) : Stmt EmptyKey := .return_ (some (.cast .implicit word value))
private def post (id : Nat) : Expr EmptyKey := .update (.inc true) (target id)
private def push (value : Nat) (slot : Nat := 3) : Stmt EmptyKey := .expr (.push (array slot) (b value))
private def elementAt (value : Expr EmptyKey) (offset : Nat) : Expr EmptyKey := .index byte value (n offset)
private def asWord (value : Expr EmptyKey) : Expr EmptyKey := .cast .implicit word value
private def sig (parameters returns : Types) (mutability : Mutability := .pure) : FunctionSignature :=
  ⟨mutability, parameters, returns⟩
private def one : Types := .cons word .nil
private def unarySig : FunctionSignature := sig one one
private def sideSig : FunctionSignature := sig one one .nonpayable
private def noArgSig : FunctionSignature := sig .nil one .nonpayable
private def boolSig : FunctionSignature := sig one (.cons .bool .nil)
private def pairSig : FunctionSignature := sig one (.cons word (.cons word .nil))
private def combineSig : FunctionSignature := sig (.cons word one) one
private def memorySig : FunctionSignature := sig (.cons memoryArray .nil) one
private def storageSig : FunctionSignature := sig (.cons storageArray .nil) one .nonpayable
private def storageMapping : SType := .mapping word word
private def mappingSig : FunctionSignature := sig .nil (.cons storageMapping .nil) .view
private def saved : Place := ⟨storageMapping, {region := .storage 0, address := 5}⟩
private def byteSig : FunctionSignature := sig .nil (.cons byte .nil)
private def pureNoArg : FunctionSignature := sig .nil one
private def panicArgSig : FunctionSignature := sig .nil one .view
private def fn (signature : FunctionSignature) (handle : Option Nat) : Expr EmptyKey := .literal ⟨signature.type, handle⟩
private def call (signature : FunctionSignature) (handle : Nat) (arguments : List (Expr EmptyKey)) : Expr EmptyKey :=
  .call signature (fn signature (some handle)) arguments

private def side : FunctionDefinition EmptyKey := {
  parameters := [binder 0], returns := [binder 1],
  body := seq [store 0 (var 0), .return_ (some (var 0))] }
private def nextIndex : FunctionDefinition EmptyKey := {
  parameters := [], returns := [binder 0],
  body := .return_ (some (.update (.inc true) (.heap (scalarPlace 2)))) }
private def factorial : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [binder 0], returns := [binder 1],
  body := .if_ (eq (var 0) (n 0)) (.return_ (some (n 1)))
    (.return_ (some (mul (var 0) (call unarySig 7 [sub (var 0) (n 1)])))) }
private def evenFunction : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [binder 0], returns := [binder 1 .bool],
  body := .if_ (eq (var 0) (n 0)) (.return_ (some (truth true)))
    (.return_ (some (call boolSig 9 [sub (var 0) (n 1)]))) }
private def oddFunction : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [binder 0], returns := [binder 1 .bool],
  body := .if_ (eq (var 0) (n 0)) (.return_ (some (truth false)))
    (.return_ (some (call boolSig 8 [sub (var 0) (n 1)]))) }
private def namedPair : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [binder 0], returns := [binder 1, binder 2],
  body := seq [set 1 (add (var 0) (n 1)), set 2 (add (var 0) (n 2)), .return_ none] }
private def mutateMemory : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [binder 0 memoryArray], returns := [binder 1],
  body := seq [.expr (.assign (.index byte (var 0 memoryArray) (n 0)) (b 9)),
    .return_ (some (.length (var 0 memoryArray)))] }
private def mutateStorage : FunctionDefinition EmptyKey := {
  parameters := [binder 0 storageArray], returns := [binder 1],
  body := seq [.expr (.push (var 0 storageArray) (b 7)), .return_ (some (.length (var 0 storageArray)))] }
private def overflow : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [], returns := [binder 0 byte],
  body := .return_ (some (bin (.arithmetic .add) byte (b 255) (b 1))) }
private def zero : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [], returns := [binder 0], body := .return_ (some (n 0)) }
private def panicArgument : FunctionDefinition EmptyKey := {
  mutability := .view, parameters := [], returns := [binder 0], body := .return_ (some (bin (.arithmetic .div) word (n 1) (global 1))) }
private def combine : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [binder 0, binder 1], returns := [binder 2],
  body := .return_ (some (add (mul (var 0) (n 10)) (var 1))) }
private def mappingResult : FunctionDefinition EmptyKey := {
  mutability := .view, parameters := [], returns := [binder 0 storageMapping],
  body := seq [set 0 (.read (.heap saved)) storageMapping, .return_ none] }
private def append : FunctionDefinition EmptyKey := {
  parameters := [], returns := [binder 0], body := seq [push 2, .return_ (some (n 0))] }
private def consumeSig : FunctionSignature := sig (.cons memoryArray one) one
private def consume : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [binder 0 memoryArray, binder 1], returns := [binder 2],
  body := .return_ (some (.length (var 0 memoryArray))) }
private def mutateRevert : FunctionDefinition EmptyKey := {
  parameters := [binder 0 memoryArray], returns := [binder 1],
  body := seq [.expr (.assign (.index byte (var 0 memoryArray) (n 0)) (b 9)), store 0 (n 9), .revert []] }
private def program : Program EmptyKey := ⟨[
  (1, side), (2, nextIndex), (3, namedPair), (4, mutateMemory), (5, mutateStorage),
  (6, panicArgument), (7, factorial), (8, evenFunction), (9, oddFunction), (10, overflow), (11, zero), (12, combine),
  (13, mappingResult), (14, append), (15, consume), (16, mutateRevert)]⟩

/-- Policy bits select the two effectful sibling groups independently. The
canonical profile follows native RHS-first capture and reverse tuple commits.
Other profiles are permitted source strategies, not compiler expectations. -/
private def policyChoice (policy : Nat) (config : Config Unit EmptyKey) : Nat :=
  match config.task with
  | .eval (.assign _ _) | .eval (.tupleAssign _ _) => if policy = 6 then 1 else 0
  | .eval (.compound _ _ _) => if policy = 8 then 1 else if policy = 9 then 2 else 0
  | .inlineElements _ _ pending => if policy = 10 then pending.length-1 else 0
  | .collect pending _ (.structConstructor _ _) => if policy = 11 then pending.length-1 else 0
  | .collect pending _ .tuple => if policy = 12 then pending.length-1 else 0
  | .collect pending _ (.namedCall _ _) => if policy = 7 then pending.length-1 else 0
  | .collect pending _ (.binary (.arithmetic .add) _) =>
      match pending.findSome? (fun item => match item.2 with
        | .update _ (.local id _) => some id | _ => none) with
      | some 0 => policy % 2
      | some 1 => policy / 2 % 2
      | _ => if policy = 5 then 1 else 0
  | _ => 0

private def execute (body : Stmt EmptyKey) (policy : Nat := 0) (state : MachineState Unit := initial)
    (functions : Program EmptyKey := program) : Execution (Config Unit EmptyKey) (Observation Unit) :=
  Execution.run (fun _ config => Machine.step physicalBackend registry {} functions (policyChoice policy config) config)
    20000 [] (Config.start state body)

private def capturedOnce : Stmt EmptyKey := seq [store 2 (n 0), push 1, push 2,
  .expr (.compound (.arithmetic .add) (.index byte (array 3) (call noArgSig 2 [])) (b 3)),
  ret (add (mul (global 2) (n 65536)) (add (mul (asWord (elementAt (array 3) 0)) (n 256)) (asWord (elementAt (array 3) 1))))]
private def assignmentOrders : Stmt EmptyKey := seq [declare 0 (n 0),
  .declare [some (binder 1 (.array word (some 2) .memory true))] none,
  .expr (.assign (.index word (var 1 (.array word (some 2) .memory true)) (post 0)) (var 0)),
  ret (add (mul (.index word (var 1 (.array word (some 2) .memory true)) (n 0)) (n 10)) (var 0))]
private def postAndCompound : Stmt EmptyKey := seq [declare 0 (n 5), declare 1 (post 0),
  .expr (.compound (.arithmetic .mul) (target 0) (n 3)), ret (add (mul (var 1) (n 100)) (var 0))]
private def compoundReadOrders : Stmt EmptyKey := seq [declare 0 (n 1),
  .expr (.compound (.arithmetic .add) (target 0) (post 0)), ret (var 0)]
private def inlineConstruction : Stmt EmptyKey :=
  let type := SType.array word (some 2) .memory true
  seq [declare 0 (.inlineArray word [call sideSig 1 [n 1],call sideSig 1 [n 2]]) type,
    ret (add (mul (.index word (var 0 type) (n 0)) (n 100))
      (add (mul (.index word (var 0 type) (n 1)) (n 10)) (global 0)))]
private def structConstruction : Stmt EmptyKey :=
  let type := SType.structType 0 .memory true
  seq [declare 0 (.structConstructor 0 [call sideSig 1 [n 2],call sideSig 1 [n 1]] [1,0]) type,
    ret (add (mul (.read (.field word (var 0 type) 0)) (n 100))
      (add (mul (.read (.field word (var 0 type) 1)) (n 10)) (global 0)))]
private def structReferenceConversion : Stmt EmptyKey :=
  let type := SType.structType 1 .memory true
  let values : Expr EmptyKey := .read (.field (.array byte none .memory false) (var 0 type) 0)
  seq [push 1,declare 0 (.structConstructor 1 [array 3,call noArgSig 14 []] [0,1]) type,
    ret (add (mul (.length values) (n 256)) (asWord (elementAt values 1)))]
private def structCopyLength : Stmt EmptyKey :=
  let type := SType.structType 1 .memory true
  seq [push 1, declare 0 (.structConstructor 1 [array 3,call noArgSig 14 []] [0,1]) type,
    ret (.length (.read (.field (.array byte none .memory false) (var 0 type) 0)))]
private def callCopyLength : Stmt EmptyKey :=
  seq [push 1, ret (call consumeSig 15 [array 3,call noArgSig 14 []])]
private def checkedAfterEffect : Stmt EmptyKey :=
  seq [store 0 (n 9), declare 0 (b 255) byte, ret (bin (.arithmetic .add) byte (var 0 byte) (b 1))]
private def aliasOrderOverflow : Stmt EmptyKey :=
  let arrayType := SType.array word none .memory true
  seq [declare 0 (.newArray word (n 1)) arrayType, declare 1 (var 0 arrayType) arrayType,
    ret (add (.assign (.index word (var 0 arrayType) (n 0)) (n (2^255)))
      (.index word (var 1 arrayType) (n 0)))]
private def aliasCallRevert : Stmt EmptyKey :=
  seq [declare 0 (.newArray byte (n 1)) memoryArray,
    ret (call (sig (.cons memoryArray .nil) one .nonpayable) 16 [var 0 memoryArray])]
private def tupleConditionalReference : Stmt EmptyKey :=
  let group := SType.tuple (.cons memoryArray (.cons word .nil))
  seq [push 1, declare 0 (.newArray byte (n 1)) memoryArray,
    .expr (.assign (.index byte (var 0 memoryArray) (n 0)) (b 9)),
    .declare [some (binder 1 memoryArray),some (binder 2)] (some (.conditional (truth true)
      (.cast .implicit group (.tuple [array 3,call noArgSig 14 []]))
      (.cast .implicit group (.tuple [var 0 memoryArray,n 2])))),
    ret (add (mul (.length (var 1 memoryArray)) (n 256)) (asWord (elementAt (var 1 memoryArray) 1)))]
private def tupleHole : Stmt EmptyKey := seq [declare 0 (n 1), declare 1 (n 2),
  .expr (.tupleAssign (.tuple [.target (target 0), .hole, .target (target 1)]) (.tuple [var 1, n 99, var 0])),
  ret (add (mul (var 0) (n 10)) (var 1))]
private def nestedTuple : Stmt EmptyKey := seq [declare 0 (n 0), declare 1 (n 0),
  .expr (.tupleAssign (.tuple [.tuple [.target (target 0), .hole], .target (target 1)])
    (.tuple [.tuple [n 4, n 88], n 7])), ret (add (mul (var 0) (n 10)) (var 1))]
private def tupleOverlap : Stmt EmptyKey := seq [
  .expr (.tupleAssign (.tuple [.target (.heap (scalarPlace 0)), .target (.heap (scalarPlace 0))]) (.tuple [n 1, n 2])), ret (global 0)]
private def storageTuple : Stmt EmptyKey := seq [push 1, push 2, push 9 4,
  .expr (.tupleAssign (.tuple [.target (.heap (arrayPlace 3)), .target (.heap (arrayPlace 4))]) (.tuple [array 4, array 3])),
  ret (add (mul (asWord (elementAt (array 3) 0)) (n 256)) (asWord (elementAt (array 4) 0)))]
private def independentOrders : Stmt EmptyKey := seq [declare 0 (n 0), declare 1 (n 0),
  ret (add (mul (add (mul (post 0) (n 10)) (post 0)) (n 100)) (add (mul (post 1) (n 10)) (post 1)))]
private def lazyBranches : Stmt EmptyKey := seq [declare 0 (n 0),
  .expr (bin .and .bool (truth false) (eq (.assign (target 0) (n 9)) (n 9))),
  .expr (bin .or .bool (truth true) (eq (.assign (target 0) (n 8)) (n 8))),
  ret (.conditional (truth true) (var 0) (bin (.arithmetic .div) word (n 1) (n 0)))]
private def scope : Stmt EmptyKey := seq [declare 0 (n 1), .block (seq [declare 1 (n 99), set 0 (n 7)]), ret (var 0)]
private def whileLoop : Stmt EmptyKey := seq [declare 0 (n 0), declare 1 (n 0),
  .while_ (lt (var 0) (n 6)) (.block (seq [.expr (.update (.inc false) (target 0)),
    .if_ (eq (var 0) (n 2)) .continue_ .skip, .if_ (eq (var 0) (n 5)) .break_ .skip,
    .expr (.compound (.arithmetic .add) (target 1) (var 0))])), ret (var 1)]
private def forLoop : Stmt EmptyKey := seq [declare 0 (n 0),
  .for_ (declare 1 (n 0)) (some (lt (var 1) (n 6))) (.expr (.update (.inc false) (target 1)))
    (.block (seq [.if_ (eq (var 1) (n 1)) .continue_ .skip, .if_ (eq (var 1) (n 4)) .break_ .skip,
      .expr (.compound (.arithmetic .add) (target 0) (var 1))])), ret (var 0)]
private def doLoop : Stmt EmptyKey := seq [declare 0 (n 0),
  .doWhile (.block (seq [.expr (.update (.inc false) (target 0)), .continue_])) (lt (var 0) (n 3)), ret (var 0)]
private def namedResults : Stmt EmptyKey := seq [
  .declare [some (binder 0), some (binder 1)] (some (call pairSig 3 [n 3])), ret (add (mul (var 0) (n 10)) (var 1))]
private def memoryParameter : Stmt EmptyKey := seq [declare 0 (.newArray byte (n 1)) memoryArray,
  .expr (.assign (.index byte (var 0 memoryArray) (n 0)) (b 1)), declare 1 (call memorySig 4 [var 0 memoryArray]),
  ret (add (mul (var 1) (n 256)) (asWord (elementAt (var 0 memoryArray) 0)))]
private def storageParameter : Stmt EmptyKey := seq [declare 0 (call storageSig 5 [array 3]),
  ret (add (mul (var 0) (n 256)) (asWord (elementAt (array 3) 0)))]
private def namedMappingResult : Stmt EmptyKey := seq [declare 0 (call mappingSig 13 []) storageMapping,
  .expr (.assign (.mapping word (var 0 storageMapping) (n 4)) (n 9)),
  ret (.read (.mapping word (.read (.heap saved)) (n 4)))]
private def widenedMappingKey : Stmt EmptyKey := seq [declare 0 (b 4) byte,
  .expr (.assign (.mapping word (.read (.heap saved)) (var 0 byte)) (n 9)),
  ret (.read (.mapping word (.read (.heap saved)) (n 4)))]
private def memoryAssignment : Stmt EmptyKey :=
  let outer := SType.array (.bytes .memory false) none .memory true
  seq [declare 0 (.newArray (.bytes .memory false) (n 1)) outer,
    declare 1 (.newBytes false (n 3)) memoryBytes,
    declare 2 (.assign (.index (.bytes .memory false) (var 0 outer) (n 0)) (var 1 memoryBytes)) memoryBytes,
    ret (add (mul (.length (var 2 memoryBytes)) (n 256)) (.length (.index (.bytes .memory false) (var 0 outer) (n 0))))]
private def indirectRecursion : Stmt EmptyKey := seq [declare 0 (fn unarySig (some 7)) unarySig.type,
  ret (.call unarySig (var 0 unarySig.type) [n 5])]
private def nilCall : Stmt EmptyKey := seq [.declare [some (binder 0 sideSig.type)] none,
  ret (.call sideSig (var 0 sideSig.type) [call sideSig 1 [n 7]])]
private def nilArgumentPanic : Stmt EmptyKey := seq [.declare [some (binder 0 sideSig.type)] none,
  ret (.call sideSig (var 0 sideSig.type) [call panicArgSig 6 []])]
private def checkedCall : Stmt EmptyKey := .arithmetic .unchecked (ret (call byteSig 10 []))
private def restoredCallerMode : Stmt EmptyKey := .arithmetic .unchecked
  (seq [declare 0 (b 255) byte, .expr (call pureNoArg 11 []), ret (bin (.arithmetic .add) byte (var 0 byte) (b 1))])
private def restoredBlockMode : Stmt EmptyKey := seq [declare 0 (b 255) byte,
  .arithmetic .unchecked (.block (.expr (.update (.inc false) (target 0 byte)))), set 0 (b 255) byte,
  ret (.update (.inc false) (target 0 byte))]
private def inheritedBlockMode : Stmt EmptyKey := .arithmetic .unchecked
  (.block (seq [declare 0 (b 255) byte, ret (bin (.arithmetic .add) byte (var 0 byte) (b 1))]))
private def panicOrder : Stmt EmptyKey := ret (add (bin (.arithmetic .div) word (n 1) (n 0)) (sub (n 0) (n 1)))
private def namedArguments : Stmt EmptyKey := seq [declare 0
  (.namedCall combineSig (fn combineSig (some 12)) [call sideSig 1 [n 2], call sideSig 1 [n 1]] [1,0]),
  ret (add (mul (var 0) (n 100)) (global 0))]
private def problemSelector : BitVec 32 := (Access.hash ("Problem(uint256)".toUTF8.toList) >>> 224).setWidth 32
private def problem : ErrorEncoding := .custom problemSelector one
private def requireTrue : Stmt EmptyKey := seq [.expr (.require_ problem (truth true) [call sideSig 1 [n 7]]), ret (global 0)]
private def requireArgumentPanic : Stmt EmptyKey := seq [.expr (.require_ problem (truth true)
  [bin (.arithmetic .div) word (n 1) (n 0)]), ret (n 0)]
private def errorString (useRequire : Bool) : Stmt EmptyKey :=
  let type := SType.string .memory true
  let bytes := Expr.referenceCast (.bytes .memory true) (var 0 type)
  seq [declare 0 (.newBytes true (n 3)) type,
    .expr (.assign (.index (.fixedBytes 0) bytes (n 0)) (.literal ⟨.fixedBytes 0, 98⟩)),
    .expr (.assign (.index (.fixedBytes 0) bytes (n 1)) (.literal ⟨.fixedBytes 0, 97⟩)),
    .expr (.assign (.index (.fixedBytes 0) bytes (n 2)) (.literal ⟨.fixedBytes 0, 100⟩)),
    .expr (if useRequire then .require_ .string (truth false) [var 0 type]
      else .revertWith .string [var 0 type]), ret (n 0)]

private def topic : Word := Access.hash ("E(uint256,uint256)".toUTF8.toList)
private def emitBody : Stmt EmptyKey := seq [.emit [.literal ⟨word, topic⟩, n 1] [n 2], ret (n 7)]
private def rollbackBody : Stmt EmptyKey := seq [.emit [.literal ⟨word, topic⟩, n 1] [n 2], store 0 (n 9), .revert []]

structure Case where
  name : String
  body : String
  model : Stmt EmptyKey
  policies : List Nat := [0]
  mutability : String := "pure"
  observeLogs : Bool := false

private def cases : List Case := [
  {name := "capture_once_compound", body := "counter=0; values.push(1); values.push(2); values[nextIndex()] += uint8(3); return counter*65536+uint256(values[0])*256+values[1];", model := capturedOnce, policies := [0], mutability := "nonpayable"},
  {name := "assignment_operand_order", body := "uint256 i=0; uint256[2] memory a; a[i++]=i; return a[0]*10+i;", model := assignmentOrders, policies := [0,6]},
  {name := "postfix_compound", body := "uint256 a=5; uint256 old=a++; a*=3; return old*100+a;", model := postAndCompound},
  {name := "compound_old_value_order", body := "uint256 a=1; a+=a++; return a;", model := compoundReadOrders, policies := [0,8,9]},
  {name := "inline_array_effects", body := "uint256[2] memory a=[side(1),side(2)]; return a[0]*100+a[1]*10+x;", model := inlineConstruction, policies := [0,10], mutability := "nonpayable"},
  {name := "named_struct_constructor_effects", body := "Pair memory p=Pair({b:side(2),a:side(1)}); return p.a*100+p.b*10+x;", model := structConstruction, policies := [0,11], mutability := "nonpayable"},
  {name := "struct_argument_conversion_after_effects", body := "values.push(1); Holder memory h=Holder(values,append()); return h.a.length*256+h.a[1];", model := structReferenceConversion, mutability := "nonpayable"},
  {name := "struct_argument_copy_length", body := "values.push(1); Holder memory h=Holder(values,append()); return h.a.length;", model := structCopyLength, mutability := "nonpayable"},
  {name := "internal_argument_conversion_after_effects", body := "values.push(1); return consume(values,append());", model := callCopyLength, mutability := "nonpayable"},
  {name := "checked_overflow_after_effect", body := "x=9; uint8 a=255; return a+uint8(1);", model := checkedAfterEffect, mutability := "nonpayable"},
  {name := "aliased_order_overflow", body := "uint256[] memory a=new uint256[](1); uint256[] memory b_=a; return (a[0]=2**255)+b_[0];", model := aliasOrderOverflow, policies := [0,5]},
  {name := "internal_alias_revert", body := "uint8[] memory a=new uint8[](1); return mutateRevert(a);", model := aliasCallRevert, mutability := "nonpayable"},
  {name := "tuple_conditional_conversion_after_effects", body := "values.push(1); uint8[] memory m=new uint8[](1); m[0]=9; (uint8[] memory a,uint256 n)=true ? (values,append()) : (m,uint256(2)); return a.length*256+a[1];", model := tupleConditionalReference, policies := [0,12], mutability := "nonpayable"},
  {name := "tuple_hole_swap", body := "uint256 a=1; uint256 b_=2; (a,,b_)=(b_,99,a); return a*10+b_;", model := tupleHole},
  {name := "nested_tuple_hole", body := "uint256 a; uint256 b_; ((a,),b_)=((4,88),7); return a*10+b_;", model := nestedTuple},
  {name := "tuple_same_target", body := "(x,x)=(uint256(1),uint256(2)); return x;", model := tupleOverlap, mutability := "nonpayable"},
  {name := "tuple_storage_copies", body := "values.push(1); values.push(2); other.push(9); (values,other)=(other,values); return uint256(values[0])*256+other[0];", model := storageTuple, mutability := "nonpayable"},
  {name := "independent_operand_orders", body := "uint256 a; uint256 b_; return (a++*10+a++)*100+(b_++*10+b_++);", model := independentOrders, policies := [0,1,2,3]},
  {name := "lazy_effect_branches", body := "uint256 a; false && ((a=9)==9); true || ((a=8)==8); uint256 z=0; return true ? a : 1/z;", model := lazyBranches},
  {name := "scope_outer_update", body := "uint256 a=1; { uint256 inner=99; a=7; } return a;", model := scope},
  {name := "while_continue_break", body := "uint256 i; uint256 sum; while(i<6) { ++i; if(i==2) continue; if(i==5) break; sum+=i; } return sum;", model := whileLoop},
  {name := "for_continue_break", body := "uint256 sum; for(uint256 i=0;i<6;++i) { if(i==1) continue; if(i==4) break; sum+=i; } return sum;", model := forLoop},
  {name := "do_while_continue", body := "uint256 i; do { ++i; continue; } while(i<3); return i;", model := doLoop},
  {name := "named_multiple_results", body := "(uint256 a,uint256 b_)=namedPair(3); return a*10+b_;", model := namedResults},
  {name := "memory_reference_parameter", body := "uint8[] memory a=new uint8[](1); a[0]=1; uint256 count=mutateMemory(a); return count*256+a[0];", model := memoryParameter},
  {name := "storage_reference_parameter", body := "uint256 count=mutateStorage(values); return count*256+values[0];", model := storageParameter, policies := [0], mutability := "nonpayable"},
  {name := "named_mapping_reference_return", body := "mapping(uint256=>uint256) storage r=mappingResult(); r[4]=9; return saved[4];", model := namedMappingResult, mutability := "nonpayable"},
  {name := "mapping_scalar_key_widening", body := "uint8 k=4; saved[k]=9; return saved[4];", model := widenedMappingKey, mutability := "nonpayable"},
  {name := "memory_assignment_expression", body := "bytes[] memory a=new bytes[](1); bytes memory value=new bytes(3); bytes memory assigned=(a[0]=value); return assigned.length*256+a[0].length;", model := memoryAssignment},
  {name := "indirect_recursive_function", body := "function(uint256) internal pure returns(uint256) f=factorial; return f(5);", model := indirectRecursion},
  {name := "mutually_recursive_functions", body := "return isEven(6) ? 1 : 0;", model := ret (.conditional (call boolSig 8 [n 6]) (n 1) (n 0))},
  {name := "nil_function_after_argument_effect", body := "function(uint256) internal returns(uint256) f; return f(side(7));", model := nilCall, policies := [0], mutability := "nonpayable"},
  {name := "nil_function_argument_panic", body := "function(uint256) internal returns(uint256) f; return f(panicArgument());", model := nilArgumentPanic, policies := [0], mutability := "nonpayable"},
  {name := "internal_call_resets_checked", body := "unchecked { return overflow(); }", model := checkedCall},
  {name := "internal_call_restores_mode", body := "unchecked { uint8 a=255; zero(); return a+uint8(1); }", model := restoredCallerMode},
  {name := "block_restores_checked", body := "uint8 a=255; unchecked { a++; } a=255; return ++a;", model := restoredBlockMode},
  {name := "nested_block_inherits_unchecked", body := "unchecked { { uint8 a=255; return a+uint8(1); } }", model := inheritedBlockMode},
  {name := "permitted_panic_order", body := "uint256 z; return 1/z+(z-1);", model := panicOrder, policies := [0,5]},
  {name := "named_argument_association", body := "uint256 result=combine({b:side(2),a:side(1)}); return result*100+x;", model := namedArguments, policies := [0,7], mutability := "nonpayable"},
  {name := "require_true_argument_effect", body := "require(true,Problem(side(7))); return x;", model := requireTrue, mutability := "nonpayable"},
  {name := "require_true_argument_panic", body := "uint256 z; require(true,Problem(1/z)); return 0;", model := requireArgumentPanic},
  {name := "assert_false", body := "assert(false); return 0;", model := seq [.expr (.assert_ (truth false)),ret (n 0)]},
  {name := "require_false_empty", body := "require(false); return 0;", model := seq [.expr (.require_ .empty (truth false) []),ret (n 0)]},
  {name := "require_false_string", body := "require(false,\"bad\"); return 0;", model := errorString true},
  {name := "revert_string", body := "revert(\"bad\");", model := errorString false},
  {name := "revert_custom_scalar", body := "revert Problem(7);", model := seq [.expr (.revertWith problem [n 7]),ret (n 0)]},
  {name := "emit_shared_world", body := "emit E(1,2); return 7;", model := emitBody, policies := [0], mutability := "nonpayable", observeLogs := true},
  {name := "emit_storage_rollback", body := "emit E(1,2); x=9; revert();", model := rollbackBody, policies := [0], mutability := "nonpayable", observeLogs := true}]

private def failureName : Failure → String
  | .rejected => "rejected" | .revert _ => "revert" | .panic code => "panic:" ++ toString code.toNat
  | .exceptional => "exceptional" | .invalidContext reason => "invalidContext:" ++ reason
  | .unsupported reason => "unsupported:" ++ reason | .undefinedBehavior reason => "undefinedBehavior:" ++ reason
  | .exhausted => "exhausted"
private def logJson (event : Contract.Interaction.Event) : Json := Json.mkObj [
  ("emitter", toJson "self"), ("topics", toJson (event.topics.map fun word => toString word.toNat)),
  ("data", toJson (event.data.map UInt8.toNat))]
private def observed : Execution (Config Unit EmptyKey) (Observation Unit) → Json
  | .finished (.returned [.atom value] state) =>
      match encodeMemory value.type value.value with
      | .ok word => Json.mkObj [("status",toJson "returned"),("word",toJson (toString word.toNat)),
          ("logs",toJson (state.heap.execution.world.logs.map logJson))]
      | .error failure => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson (failureName failure))]
  | .finished (.failed (.panic code) state) => Json.mkObj [("status",toJson "reverted"),
      ("bytes",toJson ((Contract.panic code).map UInt8.toNat)),("logs",toJson (state.heap.execution.world.logs.map logJson))]
  | .finished (.failed (.revert bytes) state) => Json.mkObj [("status",toJson "reverted"),
      ("bytes",toJson (bytes.map UInt8.toNat)),("logs",toJson (state.heap.execution.world.logs.map logJson))]
  | .finished (.inconclusive failure _) => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson (failureName failure))]
  | .finished (.failed failure _) => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson (failureName failure))]
  | .finished (.resourceLimit _ _) => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson "targetResource")]
  | .finished (.returned _ _) => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson "returnPacketShape")]
  | .exhausted _ _ => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson "exhausted")]
private def caseJson (case : Case) : Json := Json.mkObj [
  ("name",toJson case.name),("body",toJson case.body),("mutability",toJson case.mutability),
  ("admitted",toJson (match Admission.checkProgram registry 128 program,
      Admission.checkFunction registry 128 (Key := EmptyKey)
        {parameters := [], returns := [binder 999], body := case.model} with
    | .ok (), .ok () => true | _, _ => false)),
  ("observeLogs",toJson case.observeLogs),("outcomes",toJson (case.policies.map fun policy => observed (execute case.model policy))),
  ("strategies",toJson case.policies),("storageProbes",toJson (["0","1","2","3","4"] : List String))]

private def rejected : Stmt EmptyKey := seq [declare 0 (b 1) byte,
  .expr (.compound (.arithmetic .add) (target 0 byte) (.literal ⟨.uint 1, 1⟩)), ret (n 0)]
private def deleteNominal : Stmt EmptyKey :=
  let type := SType.valueType 0 (.scalar (.uint 0))
  seq [declare 0 (.literal ⟨type, 1#8⟩) type, .expr (.update .delete (target 0 type)), ret (n 0)]
private def badAddressInc : Stmt EmptyKey := seq [declare 0 (.literal ⟨.address false, 0⟩) (.address false),
  .expr (.update (.inc false) (target 0 (.address false))), ret (n 0)]
private def rejection (name body code message : String) (model : Stmt EmptyKey) : Json :=
  let result := match execute model with
    | .finished (.inconclusive .rejected _) => toJson "staticRejected" | _ => Json.null
  Json.mkObj [("name",toJson name),("body",toJson body),("modelError",result),
    ("diagnostics",toJson [Json.mkObj [("type",toJson "TypeError"),("errorCode",toJson code),("message",toJson message)]])]
private def rejections : List Json := [
  rejection "compound_narrowing" "uint8 a=1; a+=uint16(1); return a;" "7366"
    "Operator += not compatible with types uint8 and uint16." rejected,
  rejection "delete_value_type" "Tiny a=Tiny.wrap(1); delete a; return 0;" "9767"
    "Built-in unary operator delete cannot be applied to type C.Tiny." deleteNominal,
  rejection "increment_address" "address a=address(0); ++a; return 0;" "9767"
    "Built-in unary operator ++ cannot be applied to type address." badAddressInc]

private def check (name expected actual : String) : Json := Json.mkObj [
  ("name",toJson name),("expectedFailure",toJson expected),("actualFailure",toJson actual),("passed",toJson (expected==actual))]
private def modelChecks : List Json := [
  check "divergent_loop_host_suspend" "exhausted"
    (match Execution.run (fun _ config => Machine.step physicalBackend registry {} program 0 config)
      30 [] (Config.start initial (.while_ (truth true) .skip)) with | .exhausted _ _ => "exhausted" | _ => "unexpectedCompletion"),
  check "aggregate_allowance_host_suspend" "exhausted"
    (match execute (ret (.length (.newArray byte (n 1)))) 0 {initial with materializationRemaining:=0} with
      | .exhausted _ _ => "exhausted" | _ => "unexpectedCompletion")]

private def declarations : String :=
  "uint256 x; uint256 y; uint256 counter; uint8[] values; uint8[] other; mapping(uint256=>uint256) saved; error Problem(uint256 value); event E(uint256 indexed n,uint256 value); type Tiny is uint8;\n" ++
  "function consume(uint8[] memory a,uint256) internal pure returns(uint256) { return a.length; }\n" ++
  "function mutateRevert(uint8[] memory a) internal returns(uint256) { a[0]=9; x=9; revert(); }\n" ++
  "struct Pair { uint256 a; uint256 b; } struct Holder { uint8[] a; uint256 ignored; }\n" ++
  "function append() internal returns(uint256) { values.push(2); return 0; }\n" ++
  "function mappingResult() internal view returns(mapping(uint256=>uint256) storage r) { r=saved; }\n" ++
  "function combine(uint256 a,uint256 b) internal pure returns(uint256) { return a*10+b; }\n" ++
  "function side(uint256 n) internal returns(uint256) { x=n; return n; }\n" ++
  "function nextIndex() internal returns(uint256) { return counter++; }\n" ++
  "function namedPair(uint256 n) internal pure returns(uint256 a,uint256 b) { a=n+1; b=n+2; }\n" ++
  "function mutateMemory(uint8[] memory a) internal pure returns(uint256) { a[0]=9; return a.length; }\n" ++
  "function mutateStorage(uint8[] storage a) internal returns(uint256) { a.push(7); return a.length; }\n" ++
  "function panicArgument() internal view returns(uint256) { return 1/y; }\n" ++
  "function factorial(uint256 n) internal pure returns(uint256) { if(n==0) return 1; return n*factorial(n-1); }\n" ++
  "function isEven(uint256 n) internal pure returns(bool) { if(n==0) return true; return isOdd(n-1); }\n" ++
  "function isOdd(uint256 n) internal pure returns(bool) { if(n==0) return false; return isEven(n-1); }\n" ++
  "function overflow() internal pure returns(uint8) { uint8 a=255; return a+uint8(1); }\n" ++
  "function zero() internal pure returns(uint256) { return 0; }\n"

def json : Json := Json.mkObj [
  ("solidityVersion",toJson Target.solidityVersion),("referenceCompilerVersion",toJson Target.referenceCompilerVersion),
  ("evmVersion",toJson Target.evmVersion),("sourceModelPairing",toJson "manualResolvedMachinePrograms"),
  ("calldataAdmission",toJson "resolvedInternalReferences;externalDecoderCorrespondenceNotProved"),
  ("declarations",toJson declarations),("cases",toJson (cases.map caseJson)),
  ("rejections",toJson rejections),("modelChecks",toJson modelChecks)]

end Solidity.Conformance.Effects

def main : IO Unit := IO.println Solidity.Conformance.Effects.json.compress
