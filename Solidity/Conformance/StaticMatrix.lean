/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Assignment
import Solidity.Frontend.Resolved
import Lean.Data.Json.FromToJson

/-! Generated scalar-rule witnesses. Each body and its expected acceptance use
the same type/operator inputs. Compilation requests AST only, so diagnostics
test static rules without confusing unsupported code generation with rejection.
The renderer is a conformance fixture, not a verified parser or theorem. -/
namespace Solidity.Conformance.StaticMatrix
open Core Static Frontend Frontend.Inference Lean

def names : List (String × SType) := [
  ("uint8", .uint 0), ("uint16", .uint 1), ("uint160", .uint 19), ("uint256", .uint 31),
  ("int8", .sint 0), ("int16", .sint 1), ("int160", .sint 19), ("int256", .sint 31),
  ("bytes1", .fixedBytes 0), ("bytes2", .fixedBytes 1), ("bytes20", .fixedBytes 19),
  ("bytes32", .fixedBytes 31), ("bool", .bool), ("address", .address false),
  ("address payable", .address true), ("E", .enumType 1 1), ("F", .enumType 2 1),
  ("U", .valueType 1 (.scalar (.uint 0))), ("V", .valueType 2 (.scalar (.uint 0))),
  ("Base", .contract 1 false []), ("Child", .contract 2 false [1]),
  ("Pay", .contract 3 true []),
  ("function(uint8) internal pure returns(uint8)", .function .internal .pure (.cons (.uint 0) .nil) (.cons (.uint 0) .nil)),
  ("function(uint8) internal view returns(uint8)", .function .internal .view (.cons (.uint 0) .nil) (.cons (.uint 0) .nil)),
  ("function(uint8) internal returns(uint8)", .function .internal .nonpayable (.cons (.uint 0) .nil) (.cons (.uint 0) .nil)),
  ("function(uint8) external pure returns(uint8)", .function .external .pure (.cons (.uint 0) .nil) (.cons (.uint 0) .nil)),
  ("function(uint8) external payable returns(uint8)", .function .external .payable (.cons (.uint 0) .nil) (.cons (.uint 0) .nil)),
  ("function(uint8) external returns(uint8)", .function .external .nonpayable (.cons (.uint 0) .nil) (.cons (.uint 0) .nil)),
  ("function(uint16) external returns(uint8)", .function .external .nonpayable (.cons (.uint 1) .nil) (.cons (.uint 0) .nil))]

def registry : Registry := {
  enumerations := fun identity => if identity == 1 || identity == 2 then some 1 else none
  valueTypes := fun identity => if identity == 1 || identity == 2 then some (.scalar (.uint 0)) else none
  contracts := fun identity => match identity with
    | 1 => some (false, []) | 2 => some (false, [1]) | 3 => some (true, []) | _ => none
  structures := fun _ => false }

def operations : List (String × BinaryCode) := [
  ("+", .arithmetic .add), ("-", .arithmetic .sub), ("*", .arithmetic .mul),
  ("/", .arithmetic .div), ("%", .arithmetic .mod), ("**", .pow),
  ("&", .bits .bitand), ("|", .bits .bitor), ("^", .bits .bitxor),
  ("<<", .shl), (">>", .shr), ("==", .compare .eq), ("!=", .compare .ne),
  ("<", .compare .lt), ("<=", .compare .le), (">", .compare .gt), (">=", .compare .ge),
  ("&&", .and), ("||", .or)]

def context (a b : SType) : Context := fun name =>
  if name == "a" then some a else if name == "b" then some b else none

def accepted : Except StaticError α → Bool
  | .ok _ => true | .error _ => false

def witness (category parameters body : String) (accept : Bool) (complete : Bool := true) : Json :=
  Json.mkObj [("category", toJson category), ("parameters", toJson parameters),
    ("body", toJson body), ("accepted", toJson accept), ("modelComplete", toJson complete)]

def conversions (a b : String × SType) : List Json :=
  let plain := witness "implicit" (a.1 ++ " a") (b.1 ++ " r = a;") (implicit a.2 b.2)
  let cast := if b.2 == .address true then
      [witness "payable" (a.1 ++ " a") "payable(a);" (sourceCast .payable a.2 b.2)]
    else if castTarget b.2 then
      [witness "explicit" (a.1 ++ " a") (b.1 ++ "(a);") (sourceCast .ordinary a.2 b.2)]
    else []
  plain :: cast

def binaryCases (a b : String × SType) : List Json :=
  operations.map fun (spelling, code) =>
    let checked := inferResolved registry (context a.2 b.2) (.binary code (.name "a") (.name "b"))
    witness "binary" (a.1 ++ " a, " ++ b.1 ++ " b") ("a " ++ spelling ++ " b;")
      (accepted checked) (match checked with | .ok _ | .error .rejected => true | _ => false)

def unaryCases (a : String × SType) : List Json :=
  ([ ("!", UnaryCode.not), ("-", .neg), ("~", .bitnot) ].map fun (spelling, code) =>
    witness "unary" (a.1 ++ " a") (spelling ++ "a;") (checkUnary code a.2).isSome) ++
  ([ ("++a;", UpdateCode.inc false), ("a++;", .inc true),
      ("--a;", .dec false), ("a--;", .dec true), ("delete a;", .delete) ].map fun (body, code) =>
    witness "update" (a.1 ++ " a") body (updateAllowed code a.2 true))

def cases : List Json :=
  names.flatMap (fun a => unaryCases a ++ names.flatMap (fun b => conversions a b ++ binaryCases a b))

def json : Json := Json.mkObj [
  ("solidityVersion", toJson Target.solidityVersion),
  ("referenceCompilerVersion", toJson Target.referenceCompilerVersion),
  ("evmVersion", toJson Target.evmVersion),
  ("preamble", toJson "type U is uint8; type V is uint8; contract Base {} contract Child is Base {} contract Pay { receive() external payable {} }"),
  ("declarations", toJson "enum E { A, B } enum F { A, B }"),
  ("cases", toJson cases)]

end Solidity.Conformance.StaticMatrix

def main : IO Unit := IO.println Solidity.Conformance.StaticMatrix.json.compress
