/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Resolved
import Lean.Data.Json.FromToJson

/-! Source bodies and model inputs are generated from the same unannotated
expression trees. Rendering is not a verified source parser; results come
from Lean checking/execution, never from the tested compiler. -/
namespace Solidity.Conformance.Inference
open Core Static Frontend Frontend.Inference Lexical Lean

private def typeName : SType → String
  | .uint w => "uint" ++ toString w.bits
  | .sint w => "int" ++ toString w.bits
  | .fixedBytes w => "bytes" ++ toString (w.val+1)
  | .bool => "bool" | .address false => "address" | .address true => "address payable"
  | .enumType identity _ => "E" ++ toString identity
  | .valueType identity _ => "U" ++ toString identity
  | .fixedPoint signed width decimals => (if signed then "fixed" else "ufixed") ++
      toString width.bits ++ "x" ++ toString decimals.val
  | _ => "UNRENDERABLE_TYPE"

private def binaryName : BinaryCode → String
  | .arithmetic .add => "+" | .arithmetic .sub => "-" | .arithmetic .mul => "*"
  | .arithmetic .div => "/" | .arithmetic .mod => "%"
  | .bits .bitand => "&" | .bits .bitor => "|" | .bits .bitxor => "^"
  | .compare .eq => "==" | .compare .ne => "!=" | .compare .lt => "<"
  | .compare .le => "<=" | .compare .gt => ">" | .compare .ge => ">="
  | .pow => "**" | .shl => "<<" | .shr => ">>" | .and => "&&" | .or => "||"

private def unitName : Lexical.Unit → String
  | .none => "" | .wei => " wei" | .gwei => " gwei" | .ether => " ether"
  | .seconds => " seconds" | .minutes => " minutes" | .hours => " hours"
  | .days => " days" | .weeks => " weeks" | .years => " years"

private def pieceSource (piece : StringPiece) : String :=
  (match piece.kind with | .ascii => "" | .unicode => "unicode" | .hex => "hex") ++
    String.singleton piece.quote ++ piece.body ++ String.singleton piece.quote

def render : Source → String
  | .name name => name
  | .number spelling unit => spelling ++ unitName unit
  | .string pieces => String.intercalate " " (pieces.map pieceSource)
  | .bool value => if value then "true" else "false"
  | .unary op arg => "(" ++ (match op with | .neg => "-" | .bitnot => "~" | .not => "!") ++ render arg ++ ")"
  | .binary op a b => "(" ++ render a ++ " " ++ binaryName op ++ " " ++ render b ++ ")"
  | .cast kind type arg => (if kind == .payable then "payable" else typeName type) ++ "(" ++ render arg ++ ")"
  | .ite test a b => "(" ++ render test ++ " ? " ++ render a ++ " : " ++ render b ++ ")"
  | .wrap identity _ arg => "U" ++ toString identity ++ ".wrap(" ++ render arg ++ ")"
  | .unwrap identity _ arg => "U" ++ toString identity ++ ".unwrap(" ++ render arg ++ ")"

def context : Context := fun name => if name == "x" then some (.uint 0) else none

def registry : Registry := {
  enumerations := fun identity => if identity == 17 then some 1 else none
  valueTypes := fun identity => if identity == 7 then some (.scalar (.uint 0)) else none
  contracts := fun _ => none
  structures := fun _ => false }

def environment : Environment context := by
  intro type ref
  have h := ref.property
  simp only [context] at h
  split at h
  next => cases Option.some.inj h; exact BitVec.ofNat 8 7
  next => cases h

structure Case where
  name : String
  source : Source
  mode : ArithmeticMode := .checked

def num (s : String) : Source :=
  if s.toList.head? == some '-' then .unary .neg (.number (String.ofList (s.toList.drop 1)) .none)
  else .number s .none
def cast (t : SType) (arg : Source) : Source := .cast .ordinary t arg
def u8 (s : String) : Source := cast (.uint 0) (num s)
def i8 (s : String) : Source := cast (.sint 0) (num s)
def u256 (arg : Source) : Source := cast (.uint 31) arg
def signedWord (arg : Source) : Source := u256 (cast (.sint 31) arg)
def bitword (width : Width) (arg : Source) : Source := u256 (cast (.uint width) arg)
def boolword (arg : Source) : Source := .ite arg (num "1") (num "0")
def e2 : SType := .enumType 17 1

def cases : List Case := [
  ⟨"infer_mixed_widen", .binary (.arithmetic .add) (.name "x") (num "256"), .checked⟩,
  ⟨"infer_mixed_keep", .binary (.arithmetic .add) (.name "x") (num "1"), .checked⟩,
  ⟨"infer_literal_shift_runtime", .binary .shl (num "1") (.name "x"), .checked⟩,
  ⟨"infer_checked_pow", .binary .pow (u8 "2") (num "8"), .checked⟩,
  ⟨"infer_unchecked_pow", .binary .pow (u8 "2") (num "8"), .unchecked⟩,
  ⟨"infer_signed_pow_min", signedWord (.binary .pow (i8 "-2") (num "7")), .checked⟩,
  ⟨"infer_signed_pow_overflow", signedWord (.binary .pow (i8 "-2") (num "8")), .checked⟩,
  ⟨"infer_huge_exponent_one", .binary .pow (u8 "1") (num "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"), .checked⟩,
  ⟨"infer_huge_shift", .binary .shl (u8 "1") (num "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"), .checked⟩,
  ⟨"infer_huge_signed_shift", signedWord (.binary .shr (i8 "-3") (num "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")), .checked⟩,
  ⟨"infer_leading_dot", .binary (.arithmetic .mul) (num ".5") (num "2"), .checked⟩,
  ⟨"infer_dot_scientific", num ".5e2", .checked⟩,
  ⟨"infer_zero_plus", num "0e+2", .checked⟩,
  ⟨"infer_zero_octal_invalid", num "0e08", .checked⟩,
  ⟨"infer_octal_exponent", num "1e010", .checked⟩,
  ⟨"infer_negative_octal_exponent", .binary (.arithmetic .div) (num "1") (num "1e-010"), .checked⟩,
  ⟨"infer_normalized_scientific", .binary (.arithmetic .div)
    (.binary (.arithmetic .mul) (num "0.5e1233") (num "2")) (num "1e1233"), .checked⟩,
  ⟨"infer_normalized_negative_scientific", .binary (.arithmetic .div) (num "5.0e-1233") (num "1e-1233"), .checked⟩,
  ⟨"infer_uppercase_separator", num "1E_2", .checked⟩,
  ⟨"infer_gwei", .number "1.5" .gwei, .checked⟩,
  ⟨"infer_weeks", .number "2" .weeks, .checked⟩,
  ⟨"infer_bytes_widen", bitword 3 (cast (.fixedBytes 3) (cast (.fixedBytes 1) (num "0x1234"))), .checked⟩,
  ⟨"infer_bytes_narrow", bitword 0 (cast (.fixedBytes 0) (cast (.fixedBytes 1) (num "0x1234"))), .checked⟩,
  ⟨"infer_string_pad", bitword 1 (cast (.fixedBytes 1) (.string [⟨.ascii, '"', "a"⟩])), .checked⟩,
  ⟨"infer_hex_string", bitword 1 (cast (.fixedBytes 1) (.string [⟨.hex, '"', "ab_cd"⟩])), .checked⟩,
  ⟨"infer_unicode_string", bitword 1 (cast (.fixedBytes 1) (.string [⟨.unicode, '"', "é"⟩])), .checked⟩,
  ⟨"infer_unicode_concatenated", bitword 1 (cast (.fixedBytes 1)
    (.string [⟨.unicode, '"', "\\xc3"⟩, ⟨.unicode, '"', "\\xa9"⟩])), .checked⟩,
  ⟨"infer_enum_ok", u256 (cast e2 (u8 "1")), .checked⟩,
  ⟨"infer_enum_panic", u256 (cast e2 (u8 "2")), .checked⟩,
  ⟨"infer_enum_negative", u256 (cast e2 (i8 "-1")), .checked⟩,
  ⟨"infer_udvt", .unwrap 7 (.scalar (.uint 0)) (.wrap 7 (.scalar (.uint 0)) (num "255")), .checked⟩,
  ⟨"infer_payable_zero", u256 (cast (.uint 19) (cast (.address false) (.cast .payable (.address true) (num "0")))), .checked⟩,
  ⟨"infer_address_order", boolword (.binary (.compare .lt) (cast (.address false) (num "1")) (cast (.address false) (num "2"))), .checked⟩,
  ⟨"infer_bytes_literal_right", bitword 0 (.binary (.bits .bitor) (cast (.fixedBytes 0) (num "0x01")) (num "0")), .checked⟩,
  ⟨"infer_lazy_and", boolword (.binary .and (.bool false) (.binary (.compare .eq)
    (.binary (.arithmetic .div) (u8 "1") (u8 "0")) (num "0"))), .checked⟩,
  ⟨"infer_checksum_address", u256 (cast (.uint 19) (num "0x52908400098527886E0F7030069857D2E4169EE7")), .checked⟩,
  ⟨"infer_escaped_string", bitword 3 (cast (.fixedBytes 3) (.string [⟨.ascii, '"', "a\\n\\x62"⟩])), .checked⟩,
  ⟨"infer_conditional_common", .ite (.bool true) (num "1") (num "256"), .checked⟩]

structure Rejection where
  name : String
  source : Source

def rejections : List Rejection := [
  ⟨"infer_bad_signed_width", cast (.sint 1) (.name "x")⟩,
  ⟨"infer_bad_signed_compare", boolword (.binary (.compare .lt) (.unary .neg (num "1")) (num "0"))⟩,
  ⟨"infer_dead_cast", .ite (.bool true) (num "0") (boolword (cast .bool (num "1")))⟩,
  ⟨"infer_dead_logical_cast", boolword (.binary .and (.bool false) (cast .bool (num "1")))⟩,
  ⟨"infer_decimal_bytes", bitword 1 (cast (.fixedBytes 1) (num "1"))⟩,
  ⟨"infer_bad_payable", u256 (cast (.uint 19) (cast (.address false) (.cast .payable (.address true) (num "1"))))⟩,
  ⟨"infer_bad_enum_literal", u256 (cast e2 (num "2"))⟩,
  ⟨"infer_bad_udvt_cast", .unwrap 7 (.scalar (.uint 0)) (cast (.valueType 7 (.scalar (.uint 0))) (num "1"))⟩,
  ⟨"infer_scientific_plus", num "1e+2"⟩,
  ⟨"infer_bad_octal_exponent", num "1e08"⟩,
  ⟨"infer_hex_unit", .number "0x01" .wei⟩,
  ⟨"infer_retired_year", .number "1" .years⟩,
  ⟨"infer_bad_literal_left", bitword 0 (.binary (.bits .bitor) (num "0") (cast (.fixedBytes 0) (num "0x01")))⟩,
  ⟨"infer_bad_address_checksum", u256 (cast (.uint 19) (num "0x52908400098527886e0F7030069857D2E4169EE7"))⟩,
  ⟨"infer_bad_unicode_ascii", bitword 1 (cast (.fixedBytes 1) (.string [⟨.ascii, '"', "é"⟩]))⟩,
  ⟨"infer_bad_string_left", boolword (.binary (.compare .eq) (.string [⟨.ascii, '"', "a"⟩]) (cast (.fixedBytes 0) (num "0x61")))⟩]

def body (source : Source) (mode : ArithmeticMode := .checked) : String :=
  "uint8 x = 7; " ++ (if mode == .unchecked then "unchecked { " else "") ++
    "return " ++ render source ++ ";" ++ (if mode == .unchecked then " }" else "")

def resultJson : Except ConversionFailure (BitVec 256) → Json
  | .ok word => Json.mkObj [("status", toJson "returned"), ("word", toJson (toString word.toNat))]
  | .error (.panic bytes) => Json.mkObj [("status", toJson "reverted"), ("bytes", toJson (bytes.map UInt8.toNat))]
  | .error _ => Json.mkObj [("status", toJson "modelFailure")]

def caseJson (c : Case) : Json :=
  let outcomes := match checkResolved registry context c.source (.uint 31) with
    | .error _ => []
    | .ok expression => [resultJson (expression.eval environment c.mode .leftFirst),
        resultJson (expression.eval environment c.mode .rightFirst)]
  Json.mkObj [("name", toJson c.name), ("body", toJson (body c.source c.mode)), ("outcomes", toJson outcomes)]

-- Filled from the retained pinned reference responses; these diagnostic fixtures
-- never supply the model's acceptance or runtime result.
def diagnostics : String → Json
  | "infer_bad_signed_width" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "9640"), ("message", toJson "Explicit type conversion not allowed from \"uint8\" to \"int16\".")],
      Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "6359"), ("message", toJson "Return argument type int16 is not implicitly convertible to expected type (type of first return variable) uint256.")]]
  | "infer_bad_signed_compare" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "2271"), ("message", toJson "Built-in binary operator < cannot be applied to types int_const -1 and int_const 0.")]]
  | "infer_dead_cast" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "9640"), ("message", toJson "Explicit type conversion not allowed from \"int_const 1\" to \"bool\".")]]
  | "infer_dead_logical_cast" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "9640"), ("message", toJson "Explicit type conversion not allowed from \"int_const 1\" to \"bool\".")]]
  | "infer_decimal_bytes" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "9640"), ("message", toJson "Explicit type conversion not allowed from \"int_const 1\" to \"bytes2\".")]]
  | "infer_bad_payable" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "9640"), ("message", toJson "Explicit type conversion not allowed from \"int_const 1\" to \"address payable\".")]]
  | "infer_bad_enum_literal" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "9640"), ("message", toJson "Explicit type conversion not allowed from \"int_const 2\" to \"enum C.E17\".")]]
  | "infer_bad_udvt_cast" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "9640"), ("message", toJson "Explicit type conversion not allowed from \"int_const 1\" to \"U7\".")]]
  | "infer_scientific_plus" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "2826"), ("message", toJson "Invalid literal value.")]]
  | "infer_bad_octal_exponent" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "2826"), ("message", toJson "Invalid literal value.")]]
  | "infer_hex_unit" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "5145"), ("message", toJson "Hexadecimal numbers cannot be used with unit denominations. You can use an expression of the form \"0x1234 * 1 days\" instead.")]]
  | "infer_retired_year" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "4820"), ("message", toJson "Using \"years\" as a unit denomination is deprecated.")]]
  | "infer_bad_literal_left" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "2271"), ("message", toJson "Built-in binary operator | cannot be applied to types int_const 0 and bytes1.")]]
  | "infer_bad_address_checksum" => toJson [Json.mkObj [("type", toJson "SyntaxError"), ("errorCode", toJson "9429"), ("message", toJson "This looks like an address but has an invalid checksum. Correct checksummed address: \"0x52908400098527886E0F7030069857D2E4169EE7\". If this is not used as an address, please prepend '00'. For more information please see https://docs.soliditylang.org/en/develop/types.html#address-literals")]]
  | "infer_bad_unicode_ascii" => toJson [Json.mkObj [("type", toJson "ParserError"), ("errorCode", toJson "8936"), ("message", toJson "Invalid character in string. If you are trying to use Unicode characters, use a unicode\"...\" string literal.")]]
  | "infer_bad_string_left" => toJson [Json.mkObj [("type", toJson "TypeError"), ("errorCode", toJson "2271"), ("message", toJson "Built-in binary operator == cannot be applied to types literal_string \"a\" and bytes1.")]]
  | _ => toJson ([] : List Json)

def rejectionJson (c : Rejection) : Json :=
  let error := match checkResolved registry context c.source (.uint 31) with
    | .error .rejected | .error (.literal _) | .error (.lexical _) | .error (.unknownName _) => toJson "staticRejected"
    | _ => Json.null
  Json.mkObj [("name", toJson c.name), ("body", toJson (body c.source)),
    ("modelError", error), ("diagnostics", diagnostics c.name)]

def json : Json := Json.mkObj [
  ("solidityVersion", toJson Target.solidityVersion),
  ("referenceCompilerVersion", toJson Target.referenceCompilerVersion),
  ("evmVersion", toJson Target.evmVersion),
  ("preamble", toJson "type U7 is uint8;\n"),
  ("declarations", toJson "enum E17 { A, B }\n"),
  ("rejections", toJson (rejections.map rejectionJson)),
  ("cases", toJson (cases.map caseJson))]

end Solidity.Conformance.Inference

def main : IO Unit := IO.println Solidity.Conformance.Inference.json.compress
