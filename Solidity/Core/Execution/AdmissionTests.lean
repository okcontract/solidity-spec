/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Admission

namespace Solidity.Execution.Admission.Tests
open Static Core Aggregates
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

private def registry : Registry := {
  enumerations := fun _ => none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun _ => false }
private def Key (_ : SType) := Empty
private def u (value : Nat) : Expr Key := .literal ⟨.uint 31, BitVec.ofNat 256 value⟩
private def b (value : Bool) : Expr Key := .literal ⟨.bool, value⟩
private def result : Aggregates.Result α → Option Failure
  | .ok _ => none
  | .error reason => some reason
private def checked (expression : Expr Key) : Option Failure :=
  result (checkExpression registry 120 {} expression)
private def fn (body : Stmt Key) (parameters returns : List Binder := []) : FunctionDefinition Key :=
  ⟨.nonpayable, parameters, returns, body⟩
private def admitted (function : FunctionDefinition Key) : Option Failure :=
  result (checkFunction registry 160 function)

example : checked (.conditional (b true) (u 1) (.unary .neg (u 2))) = some .rejected := by decide +kernel
example : checked (.binary .and .bool (b false) (.cast .implicit .bool (u 1))) = some .rejected := by decide +kernel
example : checked (.assert_ (u 1)) = some .rejected := by decide +kernel
example : checked (.require_ .string (b true) [.unary .neg (u 1)]) = some .rejected := by decide +kernel
example : checked (.require_ .empty (b true) []) = none := by decide +kernel

private def immutable : LValue Key := .index (.fixedBytes 0) (.literal ⟨.fixedBytes 3, 0⟩) (u 0)
example : checked (.conditional (b true) (u 1)
    (.cast (.explicit .ordinary) (.uint 31) (.assign immutable (.literal ⟨.fixedBytes 0, 1⟩)))) =
    some .rejected := by decide +kernel
example : checked (.index (.fixedBytes 0) (.literal ⟨.fixedBytes 3, 0⟩) (u 0)) = none := by decide +kernel
example : (Expr.length (.literal ⟨.fixedBytes 31, 0⟩) : Expr Key).type = .uint 0 := by decide +kernel

example : admitted (fn .break_) = some .rejected := by decide +kernel
example : admitted (fn (.if_ (b false) .continue_ .skip)) = some .rejected := by decide +kernel
example : admitted (fn (.arithmetic .unchecked (.block (.arithmetic .unchecked (.block .skip))))) =
    some .rejected := by decide +kernel
example : admitted (fn (.while_ (b true) .continue_)) = none := by decide +kernel

private def reference : Expr Key := .literal ⟨.bytes .storage true, {region := .storage 0, address := 0}⟩
private def binding : Binder := ⟨1, .bytes .storage true, some "pointer"⟩
private def assignReference : Stmt Key := .expr (.assign (.local 1 binding.type) reference)
private def readReference : Stmt Key := .expr (.length (.local 1 binding.type))

example : admitted (fn (.block (.seq (.declare [some binding] none)
    (.seq (.if_ (.local 0 .bool) assignReference assignReference) readReference))) [⟨0, .bool, none⟩]) =
    none := by decide +kernel
example : admitted (fn (.block (.seq (.declare [some binding] none)
    (.seq (.if_ (.local 0 .bool) assignReference .skip) readReference))) [⟨0, .bool, none⟩]) =
    some .rejected := by decide +kernel
example : admitted (fn (.block (.seq (.declare [some binding] none)
    (.seq (.while_ (.local 0 .bool) assignReference) readReference))) [⟨0, .bool, none⟩]) =
    some .rejected := by decide +kernel
example : admitted (fn (.block (.seq (.declare [some binding] none)
    (.seq (.doWhile assignReference (.local 0 .bool)) readReference))) [⟨0, .bool, none⟩]) =
    none := by decide +kernel

example : admitted (fn (.expr (.revertWith .empty [])) [] [binding]) = none := by decide +kernel
example : admitted (fn .skip [] [binding]) = some .rejected := by decide +kernel

private def mappingType := SType.mapping (.uint 31) (.uint 31)
private def mappingResult : Binder := ⟨2, mappingType, some "r"⟩
private def mappingValue : Expr Key := .literal ⟨mappingType, {region := .storage 0, address := 0}⟩
example : admitted (fn (.expr (.assign (.local 2 mappingType) mappingValue)) [] [mappingResult]) = none := by decide +kernel
example : admitted (fn .skip [] [mappingResult]) = some .rejected := by decide +kernel
example : admitted (fn (.declare [some mappingResult] none)) = some .rejected := by decide +kernel

private def noResults : FunctionSignature := ⟨.nonpayable, .nil, .nil⟩
private def callUnknown : Expr Key := .call noResults (.literal ⟨noResults.type, some 0⟩) []
example : admitted (fn (.expr callUnknown) [] [binding]) =
    some (.unsupported "reference readiness requires a callee reachability summary") := by decide +kernel

private def namedSignature : FunctionSignature :=
  ⟨.nonpayable, .cons .bool (.cons (.uint 31) .nil), .nil⟩
private def namedCallee : Expr Key := .literal ⟨namedSignature.type, some 0⟩
example : checked (.namedCall namedSignature namedCallee [u 7, b true] [1,0]) = none := by decide +kernel
example : checked (.namedCall namedSignature namedCallee [u 7, b true] [0,0]) = some .rejected := by decide +kernel

private def tupleContext : Context :=
  ⟨[[⟨0, .uint 31, none⟩, ⟨1, .bool, none⟩, ⟨2, .uint 0, none⟩]], [0,1,2], false, false⟩
private def tupleSwap : Expr Key := .tupleAssign
  (.tuple [.target (.local 0 (.uint 31)), .hole,
    .tuple [.target (.local 1 .bool), .target (.local 2 (.uint 0))]])
  (.tuple [u 7, u 99, .tuple [b true, .literal ⟨.uint 0, 2⟩]])
example : result (checkExpression registry 120 tupleContext tupleSwap) = none := by decide +kernel
example : result (checkExpression registry 0 tupleContext tupleSwap) = some .exhausted := by decide +kernel

example : checked (.tupleAssign (.tuple []) (.tuple [])) = some .rejected := by decide +kernel
example : checked (.cast .implicit (.bytes .memory true) reference) = none := by decide +kernel
example : checked (.cast (.explicit .ordinary) (.fixedBytes 3) (.bytesLiteral false [1,2])) = none := by decide +kernel

private def groupType : SType := .tuple (.cons (.uint 31) (.cons .bool .nil))
private def rawGroup : Expr Key := .tuple [.literal ⟨.uint 0, 7⟩, b true]
example : checked (.cast .implicit groupType rawGroup) = none := by decide +kernel
example : checked (.cast (.explicit .ordinary) groupType rawGroup) = some .rejected := by decide +kernel
example : checked (.cast .implicit groupType (.tuple [u 7])) = some .rejected := by decide +kernel
example : checked (.cast .implicit groupType (u 7)) = some .rejected := by decide +kernel
example : checked (.cast .implicit (.uint 31) rawGroup) = some .rejected := by decide +kernel
example : checked (.conditional (b true) (.cast .implicit groupType rawGroup)
    (.cast .implicit groupType (.tuple [u 8, b false]))) = none := by decide +kernel
example : checked (.cast .implicit (.tuple (.cons groupType (.cons (.uint 31) .nil)))
    (.tuple [rawGroup, .literal ⟨.uint 0, 9⟩])) = none := by decide +kernel
example : GroupTransferAllowed (.tuple (.cons (.uint 0) (.cons .bool .nil))) groupType :=
  groupTransfer_sound (registry := registry) (fuel := 16) (by rfl)
example : checked (.require_ (.custom 0x11223344 (.cons (.array (.uint 0) none .memory true) .nil))
    (b true) [.newArray (.uint 0) (u 2)]) = none := by decide +kernel

private def valueRegistry : Registry :=
  {registry with valueTypes := fun id => if id == 7 then some (.scalar (.uint 0)) else none}
example : result (checkExpression valueRegistry 120 {}
    (.unwrap 7 (.scalar (.uint 0)) (.wrap 7 (.scalar (.uint 0)) (.literal ⟨.uint 0, 1⟩)) : Expr Key)) =
    none := by decide +kernel
example : result (checkExpression valueRegistry 120 {}
    (.wrap 8 (.scalar (.uint 0)) (.literal ⟨.uint 0, 1⟩) : Expr Key)) = some .rejected := by decide +kernel

private def externalFunction : Expr Key :=
  .literal ⟨.function .external .nonpayable .nil .nil, (7, 0x11223344)⟩
example : checked (.functionAddress externalFunction) = none := by decide +kernel
example : checked (.functionSelector externalFunction) = none := by decide +kernel
example : checked (.functionSelector (.literal ⟨noResults.type, some 0⟩)) = some .rejected := by decide +kernel

private def structRegistry : Registry :=
  {registry with
    structures := fun id => id == 1
    structFields := fun id => if id == 1 then some [("n", .uint 0), ("flag", .bool)] else none}
example : result (checkExpression structRegistry 120 {}
    (.structConstructor 1 [b true, .literal ⟨.uint 0, 1⟩] [1,0] : Expr Key)) = none := by decide +kernel
example : result (checkExpression structRegistry 120 {}
    (.structConstructor 1 [b true, .literal ⟨.uint 0, 1⟩] [0,1] : Expr Key)) = some .rejected := by decide +kernel
example : checked (.inlineArray (.uint 0) [.literal ⟨.uint 0, 1⟩, .literal ⟨.uint 0, 2⟩]) = none := by decide +kernel
example : checked (.inlineArray (.uint 31) [.literal ⟨.uint 0, 1⟩, .literal ⟨.uint 0, 2⟩]) =
    some .rejected := by decide +kernel
example : checked (.inlineArray (.uint 31) [.literal ⟨.uint 31, 1⟩, .literal ⟨.uint 0, 2⟩]) = none := by decide +kernel
example : checked (.inlineArray (.uint 31) [.literal ⟨.uint 0, 1⟩, .literal ⟨.uint 31, 2⟩]) = none := by decide +kernel
example : checked (.inlineArray (.uint 0) [.literal ⟨.uint 0, 1⟩, b true]) = some .rejected := by decide +kernel
example : checked (.inlineArray (.uint 0) []) = some .rejected := by decide +kernel
example : inlineElementType [.array (.uint 0) none .storage false, .array (.uint 0) none .calldata true] = none := by decide +kernel
example : inlineElementType [.array (.uint 0) none .storage false, .array (.uint 0) none .memory true] =
    some (.array (.uint 0) none .memory false) := by decide +kernel
example : inlineElementType [.array (.uint 0) none .memory true, .array (.uint 0) none .storage false] =
    some (.array (.uint 0) none .memory false) := by decide +kernel
example : result (scalarBinaryType (.arithmetic .add) (.fixedPoint false 0 1) (.fixedPoint false 1 2)) =
    some (.unsupported "fixed-point expression execution") := by decide +kernel
example : result (checkExpression registry 120
    ⟨[[⟨0, .fixedPoint false 0 1, none⟩, ⟨1, .fixedPoint false 1 2, none⟩]], [0,1], false, false⟩
    (.inlineArray (.fixedPoint false 1 2) [.local 0 (.fixedPoint false 0 1), .local 1 (.fixedPoint false 1 2)] : Expr Key)) =
    some (.unsupported "fixed-point inline-array inference") := by decide +kernel
example : admitted (fn (.emit [] [.bytesLiteral false [1,2]])) =
    some (.unsupported "aggregate event ABI encoding") := by decide +kernel

end Solidity.Execution.Admission.Tests
