/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Execution
import Solidity.Frontend.Literal
import Lean.Data.Json.FromToJson

/-! Differential witnesses pair explicit source bodies with core computations.
This corpus tests adequacy of scalar primitives; it is not a verified parser or
compiler-preservation theorem. No expected result comes from the native compiler. -/
namespace Solidity.Conformance
open Core Lean

structure Case where
  name : String
  body : String
  outcomes : List (Result (BitVec 256))

def uintWord (result : Result (BitVec bits)) : Result (BitVec 256) :=
  result.map fun word => BitVec.ofNat 256 word.toNat

def sintWord (result : Result (BitVec bits)) : Result (BitVec 256) :=
  result.map fun word => BitVec.ofInt 256 word.toInt

namespace ScalarMachine
open Execution Static

abbrev Closed := Execution.Expr EmptyKey
abbrev RunResult := Aggregates.Result (Execution.Execution (Config Unit EmptyKey) (Observation Unit))

def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }
def initial : MachineState Unit := {external := (), heap := Aggregates.MemoryOps.initialHeap}
def word (value : Nat) : Closed := .literal ⟨.uint 31, BitVec.ofNat 256 value⟩
def boolean (value : Bool) : Closed := .literal ⟨.bool, value⟩
def boolWord (value : Closed) : Closed := .conditional value (word 1) (word 0)

/-- Admission precedes evaluation. Each strategy supplies independent choices
at the actual machine steps; no legacy expression interpreter is involved. -/
def expressionRun (value : Closed) (choice : Nat := 0) (fuel : Nat := 1000)
    (state : MachineState Unit := initial) : RunResult :=
  SourceFacade.executeExpression physicalBackend registry {} ⟨[]⟩ fuel (List.replicate (fuel+1) choice) state value

/-- Unresolved/model/resource outcomes leave no expected native result. The
conformance driver rejects empty expectations rather than inventing a revert. -/
def outcomes : RunResult → List (Core.Result (BitVec 256))
  | .ok (.finished (.returned [.atom ⟨.uint 31, value⟩] _)) => [.ok value]
  | .ok (.finished (.failed (.panic code) _)) => [.error (Contract.panic code)]
  | .ok (.finished (.failed (.revert bytes) _)) => [.error bytes]
  | _ => []

def division : Closed := .binary (.arithmetic .div) (.uint 31) (word 7) (word 0)
def overflow : Closed := .binary (.arithmetic .sub) (.uint 31) (word 0) (word 1)
def testCondition : Closed := .binary (.compare .gt) .bool division (word 0)
def twoPanics : Closed := .binary (.arithmetic .add) (.uint 31) division overflow

def increment : Stmt EmptyKey := .expr (.update (.inc false) (.local 0 (.uint 0)))
def belowThree : Closed := .binary (.compare .lt) .bool (.local 0 (.uint 0)) (.literal ⟨.uint 0, 3⟩)
def whileCount : Stmt EmptyKey := .while_ belowThree increment
def forContinue : Stmt EmptyKey := .for_ .skip (some belowThree) increment .continue_
def forBreak : Stmt EmptyKey := .for_ .skip (some (boolean true)) increment .break_
def nestedBreak : Stmt EmptyKey := .for_ .skip (some belowThree) increment (.while_ (boolean true) .break_)
def whileOverflow : Stmt EmptyKey := .while_ (boolean true) increment

def loopFunction (command : Stmt EmptyKey) : FunctionDefinition EmptyKey := {
  mutability := .pure, parameters := [⟨0, .uint 0, none⟩], returns := [⟨1, .uint 31, none⟩],
  body := .seq command (.return_ (some (.cast .implicit (.uint 31) (.local 0 (.uint 0))))) }

/-- Result-bearing loops enter through a checked ordinary function call. The
caller checkpoint includes the complete heap, locals, mode and work allowance. -/
def loopRun (command : Stmt EmptyKey) (value : BitVec 8 := 0) (fuel : Nat := 1000)
    (state : MachineState Unit := initial) : RunResult :=
  let function := loopFunction command
  SourceFacade.executeFunction physicalBackend registry {} ⟨[(1, function)]⟩ fuel [] state
    function.signature 1 [.literal ⟨.uint 0, value⟩]

end ScalarMachine

def scalarCases : List Case := [
  ⟨"uint8_checked_add", "uint8 a = 255; return uint256(a + uint8(1));",
    [uintWord (unsigned 0 .checked .add 255 1)]⟩,
  ⟨"uint8_unchecked_add", "uint8 a = 255; unchecked { return uint256(a + uint8(1)); }",
    [uintWord (unsigned 0 .unchecked .add 255 1)]⟩,
  ⟨"uint256_checked_sub", "uint256 a = 0; return a - uint256(1);",
    [unsigned 31 .checked .sub 0 1]⟩,
  ⟨"uint256_unchecked_sub", "uint256 a = 0; unchecked { return a - uint256(1); }",
    [unsigned 31 .unchecked .sub 0 1]⟩,
  ⟨"uint16_checked_mul", "uint16 a = 256; return uint256(a * a);",
    [uintWord (unsigned 1 .checked .mul 256 256)]⟩,
  ⟨"uint16_unchecked_mul", "uint16 a = 256; unchecked { return uint256(a * a); }",
    [uintWord (unsigned 1 .unchecked .mul 256 256)]⟩,
  ⟨"unchecked_div_zero", "uint256 a = 7; uint256 b = 0; unchecked { return a / b; }",
    [unsigned 31 .unchecked .div 7 0]⟩,
  ⟨"unchecked_mod_zero", "uint256 a = 7; uint256 b = 0; unchecked { return a % b; }",
    [unsigned 31 .unchecked .mod 7 0]⟩,
  ⟨"int8_div_min_checked", "int8 a = -128; int8 b = -1; return uint256(int256(a / b));",
    [sintWord (signed 0 .checked .div 128 255)]⟩,
  ⟨"int8_div_min_unchecked", "int8 a = -128; int8 b = -1; unchecked { return uint256(int256(a / b)); }",
    [sintWord (signed 0 .unchecked .div 128 255)]⟩,
  ⟨"int8_mod_min", "int8 a = -128; int8 b = -1; return uint256(int256(a % b));",
    [sintWord (signed 0 .checked .mod 128 255)]⟩,
  ⟨"int8_div_rounding", "int8 a = -5; int8 b = 2; return uint256(int256(a / b));",
    [sintWord (signed 0 .checked .div 251 2)]⟩,
  ⟨"int8_mod_sign", "int8 a = -5; int8 b = 2; return uint256(int256(a % b));",
    [sintWord (signed 0 .checked .mod 251 2)]⟩,
  ⟨"int8_right_shift", "int8 a = -3; return uint256(int256(a >> uint256(1)));",
    [sintWord ((Binary.sintShr 0 31).eval 253 1)]⟩,
  ⟨"int8_large_right_shift", "int8 a = -3; return uint256(int256(a >> uint256(256)));",
    [sintWord ((Binary.sintShr 0 31).eval 253 256)]⟩,
  ⟨"uint8_left_shift", "uint8 a = 1; return uint256(a << uint256(8));",
    [uintWord ((Binary.uintShl 0 31).eval 1 8)]⟩,
  ⟨"uint8_cast_truncates", "uint256 a = 257; return uint256(uint8(a));",
    [uintWord ((Unary.uintCast 31 0).eval 257)]⟩,
  ⟨"int8_cast_extends", "int8 a = -1; return uint256(int256(a));",
    [sintWord ((Unary.sintCast 0 31).eval 255)]⟩,
  ⟨"int8_checked_negate", "int8 a = -128; return uint256(int256(-a));",
    [sintWord ((Unary.negate 0 .checked).eval 128)]⟩,
  ⟨"int8_unchecked_negate", "int8 a = -128; unchecked { return uint256(int256(-a)); }",
    [sintWord ((Unary.negate 0 .unchecked).eval 128)]⟩,
  ⟨"short_circuit_and", "uint256 a = 7; uint256 b = 0; return false && (a / b > 0) ? 1 : 0;",
    ScalarMachine.outcomes (ScalarMachine.expressionRun (ScalarMachine.boolWord
      (.binary .and .bool (ScalarMachine.boolean false) ScalarMachine.testCondition)))⟩,
  ⟨"short_circuit_or", "uint256 a = 7; uint256 b = 0; return true || (a / b > 0) ? 1 : 0;",
    ScalarMachine.outcomes (ScalarMachine.expressionRun (ScalarMachine.boolWord
      (.binary .or .bool (ScalarMachine.boolean true) ScalarMachine.testCondition)))⟩,
  ⟨"conditional_skips_panic", "uint256 a = 7; uint256 b = 0; return false ? a / b : 3;",
    ScalarMachine.outcomes (ScalarMachine.expressionRun
      (.conditional (ScalarMachine.boolean false) ScalarMachine.division (ScalarMachine.word 3)))⟩,
  ⟨"permitted_panic_order", "uint256 a = 7; uint256 b = 0; return a / b + (b - uint256(1));",
    ScalarMachine.outcomes (ScalarMachine.expressionRun ScalarMachine.twoPanics) ++
      ScalarMachine.outcomes (ScalarMachine.expressionRun ScalarMachine.twoPanics 1)⟩]

def controlCases : List Case := [
  ⟨"while_count", "uint8 i = 0; while (i < 3) { ++i; } return uint256(i);",
    ScalarMachine.outcomes (ScalarMachine.loopRun ScalarMachine.whileCount)⟩,
  ⟨"for_continue", "uint8 i = 0; for (; i < 3; ++i) { continue; } return uint256(i);",
    ScalarMachine.outcomes (ScalarMachine.loopRun ScalarMachine.forContinue)⟩,
  ⟨"for_break", "uint8 i = 0; for (; true; ++i) { break; } return uint256(i);",
    ScalarMachine.outcomes (ScalarMachine.loopRun ScalarMachine.forBreak)⟩,
  ⟨"nested_break", "uint8 i = 0; for (; i < 3; ++i) { while (true) { break; } } return uint256(i);",
    ScalarMachine.outcomes (ScalarMachine.loopRun ScalarMachine.nestedBreak)⟩,
  ⟨"while_overflow", "uint8 i = 254; while (true) { ++i; } return uint256(i);",
    ScalarMachine.outcomes (ScalarMachine.loopRun ScalarMachine.whileOverflow 254)⟩]

namespace Constants
open Frontend.Literal

def number (n : Int) : Frontend.Literal.Expr := .number (Rat.ofInt n)
def pow (base exponent : Int) : Frontend.Literal.Expr := .binary .pow (number base) (number exponent)
def denominator : Frontend.Literal.Expr := .binary .mul (pow 2 2048) (number 2)
def small : Frontend.Literal.Expr := .binary .div (number 1) denominator

def outcomes (expr : Frontend.Literal.Expr) (signed : Bool := false) (width : Width := 31) :
    List (Result (BitVec 256)) :=
  if signed then match expr.signed width with
    | .ok word => [.ok (BitVec.ofInt 256 word.toInt)]
    | .error _ => []
  else match expr.unsigned width with
    | .ok word => [.ok (BitVec.ofNat 256 word.toNat)]
    | .error _ => []

def cases : List Case := [
  ⟨"literal_fractional_product", "return uint256(0.5 * 8);",
    outcomes (.binary .mul (.number (mkRat 1 2)) (number 8))⟩,
  ⟨"literal_fractional_mod", "return uint256((5.5 % 2) * 2);",
    outcomes (.binary .mul (.binary .mod (.number (mkRat 11 2)) (number 2)) (number 2))⟩,
  ⟨"literal_negative_mod", "return uint256(int256((-5.5 % 2) * 2));",
    outcomes (.binary .mul (.binary .mod (.number (mkRat (-11) 2)) (number 2)) (number 2)) true⟩,
  ⟨"literal_negative_power", "return uint256((2 ** -3) * 8);",
    outcomes (.binary .mul (pow 2 (-3)) (number 8))⟩,
  ⟨"literal_zero_negative_power", "return uint256(0 ** -1);", outcomes (pow 0 (-1))⟩,
  ⟨"literal_zero_zero_power", "return uint256(0 ** 0);", outcomes (pow 0 0)⟩,
  ⟨"literal_large_parity", "return uint256(int256((-1) ** 4294967297));",
    outcomes (pow (-1) 4294967297) true⟩,
  ⟨"literal_large_intermediate", "return uint256((2 ** 800 + 1) - 2 ** 800);",
    outcomes (.binary .sub (.binary .add (pow 2 800) (number 1)) (pow 2 800))⟩,
  ⟨"literal_normalized_precision", "return uint256((1/(2**2048*2) + 1/(2**2048*2)) * (2**2048));",
    outcomes (.binary .mul (.binary .add small small) (pow 2 2048))⟩,
  ⟨"literal_normalized_zero", "return uint256(1/(2**2048*2) - 1/(2**2048*2));",
    outcomes (.binary .sub small small)⟩,
  ⟨"literal_negative_shift", "return uint256(int256(-5 >> 1));",
    outcomes (.binary .shr (number (-5)) (number 1)) true⟩,
  ⟨"literal_large_right_shift", "return uint256(int256(-5 >> 4294967295));",
    outcomes (.binary .shr (number (-5)) (number 4294967295)) true⟩,
  ⟨"literal_signed_bits", "return uint256(int256(-5 ^ 3));",
    outcomes (.binary .bitxor (number (-5)) (number 3)) true⟩,
  ⟨"literal_signed_and", "return uint256(int256(-5 & -3));",
    outcomes (.binary .bitand (number (-5)) (number (-3))) true⟩,
  ⟨"literal_uint8_limit", "return uint256(uint8(255));", outcomes (number 255) false 0⟩,
  ⟨"literal_int8_limit", "return uint256(int256(int8(-128)));", outcomes (number (-128)) true 0⟩]

structure Rejection where
  name : String
  body : String
  computation : Except Frontend.Literal.Error Rat
  diagnostics : List (String × String)

def castUint (width : Width) (value : Rat) : Except Frontend.Literal.Error Rat :=
  (toUnsigned width value).map fun _ => value

def castSint (width : Width) (value : Rat) : Except Frontend.Literal.Error Rat :=
  (toSigned width value).map fun _ => value

def rejections : List Rejection := [
  ⟨"constant_zero_divisor", "return uint256(1 / 0);", Binary.div.eval 1 0,
    [("2271", "Built-in binary operator / cannot be applied to types int_const 1 and int_const 0.")]⟩,
  ⟨"constant_fractional_bits", "return uint256(1.5 & 1);", Binary.bitand.eval (mkRat 3 2) 1,
    [("2271", "Built-in binary operator & cannot be applied to types rational_const 3 / 2 and int_const 1."),
     ("9640", "Explicit type conversion not allowed from \"rational_const 3 / 2\" to \"uint256\".")]⟩,
  ⟨"constant_fractional_power", "return uint256(2 ** 0.5);", Binary.pow.eval 2 (mkRat 1 2),
    [("2271", "Built-in binary operator ** cannot be applied to types int_const 2 and rational_const 1 / 2.")]⟩,
  ⟨"constant_negative_shift", "return uint256(1 << -1);", Binary.shl.eval 1 (-1),
    [("2271", "Built-in binary operator << cannot be applied to types int_const 1 and int_const -1.")]⟩,
  ⟨"constant_large_power", "return uint256(2 ** 2049);", Binary.pow.eval 2 2049,
    [("2271", "Built-in binary operator ** cannot be applied to types int_const 2 and int_const 2049.")]⟩,
  ⟨"constant_large_shift", "return uint256(1 << 4096);", Binary.shl.eval 1 4096,
    [("2271", "Built-in binary operator << cannot be applied to types int_const 1 and int_const 4096.")]⟩,
  ⟨"constant_shift_count", "return uint256(0 >> 4294967296);", Binary.shr.eval 0 4294967296,
    [("2271", "Built-in binary operator >> cannot be applied to types int_const 0 and int_const 4294967296.")]⟩,
  ⟨"constant_uint8_overflow", "return uint256(uint8(256));", castUint 0 256,
    [("9640", "Explicit type conversion not allowed from \"int_const 256\" to \"uint8\".")]⟩,
  ⟨"constant_int8_overflow", "return uint256(int256(int8(128)));", castSint 0 128,
    [("9640", "Explicit type conversion not allowed from \"int_const 128\" to \"int8\".")]⟩,
  ⟨"constant_fractional_cast", "return uint256(1.5);", castUint 31 (mkRat 3 2),
    [("9640", "Explicit type conversion not allowed from \"rational_const 3 / 2\" to \"uint256\".")]⟩]

def errorName : Frontend.Literal.Error → String
  | .zeroDivisor => "zeroDivisor" | .fractionalOperand => "fractionalOperand"
  | .negativeShift => "negativeShift" | .precisionLimit => "precisionLimit"
  | .notRepresentable => "notRepresentable"

def rejectionJson (c : Rejection) : Json := Json.mkObj [
  ("name", toJson c.name), ("body", toJson c.body),
  ("modelError", match c.computation with | .ok _ => Json.null | .error e => toJson (errorName e)),
  ("diagnostics", toJson (c.diagnostics.map fun (code, message) => Json.mkObj [
    ("type", toJson "TypeError"), ("errorCode", toJson code), ("message", toJson message)]))]

end Constants

def cases : List Case := scalarCases ++ controlCases ++ Constants.cases

def resultJson : Result (BitVec 256) → Json
  | .ok word => Json.mkObj [("status", toJson "returned"), ("word", toJson (toString word.toNat))]
  | .error bytes => Json.mkObj [("status", toJson "reverted"), ("bytes", toJson (bytes.map UInt8.toNat))]

def json : Json := Json.mkObj [
  ("solidityVersion", toJson Target.solidityVersion),
  ("referenceCompilerVersion", toJson Target.referenceCompilerVersion),
  ("evmVersion", toJson Target.evmVersion),
  ("rejections", toJson (Constants.rejections.map Constants.rejectionJson)),
  ("cases", toJson (cases.map fun c => Json.mkObj [
    ("name", toJson c.name), ("body", toJson c.body),
    ("outcomes", toJson (c.outcomes.map resultJson))]))]

end Solidity.Conformance

def main : IO Unit := IO.println Solidity.Conformance.json.compress
