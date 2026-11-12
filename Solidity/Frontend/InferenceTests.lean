/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Assignment
import Solidity.Core.OperatorBindings

namespace Solidity.Frontend.Inference.Tests
open Core Static Lexical

set_option exponentiation.threshold 8192
set_option maxRecDepth 16384

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)


private def context : Context := fun _ => some (.uint 0)
private def environment : Environment context := by
  intro type ref
  have h : SType.uint 0 = type := Option.some.inj ref.property
  subst type
  exact BitVec.ofNat 8 7

private def num (s : String) : Source := .number s .none
private def cast (t : SType) (s : String) : Source := .cast .ordinary t (num s)
private def typeOf (source : Source) : Except StaticError SType := do
  (← infer context source).mobile
private def runUint (width : Width) (source : Source) (mode : ArithmeticMode := .checked) :
    Except StaticError (Except ConversionFailure Nat) := do
  let expression ← check context source (.uint width)
  pure ((expression.eval environment mode .leftFirst).map BitVec.toNat)
private def rejected (source : Source) : Bool := match infer context source with
  | .error .rejected => true | _ => false

example : typeOf (.binary (.arithmetic .add) (.name "x") (num "256")) = .ok (.uint 1) := by decide +kernel
example : typeOf (.binary (.arithmetic .add) (.name "x") (num "1")) = .ok (.uint 0) := by decide +kernel
example : runUint 1 (.binary (.arithmetic .add) (.name "x") (num "256")) = .ok (.ok 263) := by decide +kernel
example : rejected (.cast .ordinary (.sint 1) (.name "x")) = true := by decide +kernel
example : rejected (.binary (.compare .lt) (.unary .neg (num "1")) (num "0")) = true := by decide +kernel
example : rejected (.ite (.bool true) (num "0") (.cast .ordinary (.bool) (num "1"))) = true := by decide +kernel
example : rejected (.binary .and (.bool false) (.cast .ordinary .bool (num "1"))) = true := by decide +kernel
example : rejected (.binary .pow (.name "x") (num "0.5")) = true := by decide +kernel
example : rejected (.binary .shl (.name "x") (num "0.5")) = true := by decide +kernel
example : rejected (.binary .and (.bool false) (num "0.5")) = true := by decide +kernel
example : rejected (.binary (.arithmetic .add) (.bool true) (num "0.5")) = true := by decide +kernel
example : typeOf (.binary .shl (num "1") (.name "x")) = .ok (.uint 31) := by decide +kernel
example : runUint 31 (.binary .shl (num "1") (.name "x")) = .ok (.ok 128) := by decide +kernel
example : runUint 0 (.binary .pow (cast (.uint 0) "2") (num "8")) = .ok (.error (.panic (Contract.panic 0x11))) := by decide +kernel
example : runUint 0 (.binary .pow (cast (.uint 0) "2") (num "8")) .unchecked = .ok (.ok 0) := by decide +kernel
example : runUint 31 (.binary (.arithmetic .mul) (num ".5") (num "2")) = .ok (.ok 1) := by decide +kernel
example : runUint 0 (.binary .shl (.name "x") (num "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")) = .ok (.ok 0) := by decide +kernel
example : runUint 31 (num ".5e2") = .ok (.ok 50) := by decide +kernel
example : runUint 31 (num "0e+2") = .ok (.ok 0) := by decide +kernel
example : runUint 31 (num "1e+2") = .error (.lexical .malformed) := by decide +kernel
example : runUint 31 (num "1e010") = .ok (.ok 100000000) := by decide +kernel
example : runUint 31 (num "1e08") = .error (.lexical .malformed) := by decide +kernel
example : runUint 31 (num "0e08") = .ok (.ok 0) := by decide +kernel
example : runUint 31 (num "1_E2") = .ok (.ok 100) := by decide +kernel
example : runUint 31 (num "1e_2") = .error (.lexical .malformed) := by decide +kernel
example : runUint 0 (num "_1") = .error (.lexical .malformed) := by decide +kernel
example : runUint 0 (num "_0x01") = .error (.lexical .malformed) := by decide +kernel
example : runUint 0 (num "0_x01") = .error (.lexical .malformed) := by decide +kernel
example : runUint 0 (num "0x_01") = .error (.lexical .malformed) := by decide +kernel
example : runUint 0 (num "._5") = .error (.lexical .malformed) := by decide +kernel
example : runUint 0 (num "+1") = .error (.lexical .malformed) := by decide +kernel
example : runUint 0 (num "0x0_1") = .ok (.ok 1) := by decide +kernel
example : runUint 0 (num "1_0") = .ok (.ok 10) := by decide +kernel
example : runUint 31 (.number "1" .gwei) = .ok (.ok (10^9)) := by decide +kernel
example : runUint 31 (.number "0x01" .wei) = .error (.lexical .invalidUnit) := by decide +kernel
example : runUint 31 (.number "1" .years) = .error (.lexical .invalidUnit) := by decide +kernel
example : rejected (.cast .ordinary (.fixedBytes 1) (num "1")) = true := by decide +kernel
example : typeOf (.cast .ordinary (.fixedBytes 1) (num "0x0001")) = .ok (.fixedBytes 1) := by decide +kernel
example : typeOf (.cast .ordinary (.fixedBytes 31) (num "0")) = .ok (.fixedBytes 31) := by decide +kernel
example : rejected (.cast .payable (.address true) (num "1")) = true := by decide +kernel
example : typeOf (.cast .payable (.address true) (num "0")) = .ok (.address true) := by decide +kernel
example : rejected (.cast .ordinary (.enumType 17 1) (num "2")) = true := by decide +kernel
example : typeOf (.cast .ordinary (.enumType 17 1) (cast (.uint 0) "2")) = .ok (.enumType 17 1) := by decide +kernel
example : (do let e ← check context (.cast .ordinary (.enumType 17 1) (cast (.uint 0) "2")) (.enumType 17 1)
              pure ((e.eval environment .checked .leftFirst).map (fun v => v.val))) =
    Except.ok (Except.error (ConversionFailure.panic (Contract.panic 0x21))) := by decide +kernel
example : typeOf (.wrap 7 (.scalar (.uint 0)) (num "255")) = .ok (.valueType 7 (.scalar (.uint 0))) := by decide +kernel
example : runUint 0 (.unwrap 7 (.scalar (.uint 0)) (.wrap 7 (.scalar (.uint 0)) (num "255"))) = .ok (.ok 255) := by decide +kernel
example : rejected (.cast .ordinary (.valueType 7 (.scalar (.uint 0))) (num "1")) = true := by decide +kernel
example : StringPiece.decode ⟨.ascii, '"', "a\\n\\x62"⟩ = .ok [97, 10, 98] := by decide +kernel
example : StringPiece.decode ⟨.hex, '"', "ab_cd"⟩ = .ok [0xab, 0xcd] := by decide +kernel
example : StringPiece.decode ⟨.hex, '"', "a_b"⟩ = .error .malformed := by decide +kernel
example : StringPiece.decode ⟨.unicode, '"', "é"⟩ = .ok [0xc3, 0xa9] := by decide +kernel
example : StringPiece.decode ⟨.ascii, '"', "é"⟩ = .error .malformed := by decide +kernel
example : StringPiece.decode ⟨.unicode, '"', "\\xff"⟩ = .error .invalidUTF8 := by decide +kernel
example : StringPiece.decode ⟨.ascii, '"', "\\xff"⟩ = .ok [0xff] := by decide +kernel
example : stringPieces [⟨.unicode, '"', "\\xc3"⟩, ⟨.unicode, '"', "\\xa9"⟩] = .ok [0xc3, 0xa9] := by decide +kernel
example : stringConverts [0xff] (.string .memory true) = false := by decide +kernel
example : stringConverts [0xff] (.bytes .memory true) = true := by decide +kernel
example : stringWord 1 [0x61] = BitVec.ofNat 16 0x6100 := by decide +kernel
example : sourceCast .ordinary (.address true) (.uint 19) = false := by decide +kernel
example : implicit (.function .internal .pure .nil .nil) (.function .internal .view .nil .nil) = true := by decide +kernel
example : implicit (.function .internal .nonpayable .nil .nil) (.function .internal .payable .nil .nil) = false := by decide +kernel
example : deletable (.valueType 7 (.scalar (.uint 0))) = false := by decide +kernel

private def planned (kind : AssignmentKind) (right : Source) : Except StaticError Nat := do
  let term ← infer context right
  let expression ← assignment kind true (SourceExpr.literal (type := .uint 0) (BitVec.ofNat 8 7)) term
  match expression.eval environment .checked .leftFirst with
  | .ok value => pure value.toNat
  | .error _ => .error .unsupported

example : planned (.compound (.arithmetic .add)) (num "1") = .ok 8 := by decide +kernel
example : planned (.compound (.arithmetic .add)) (num "256") = .error .rejected := by decide +kernel
example : planned (.compound .pow) (num "2") = .error .rejected := by decide +kernel
example : planned .plain (num "255") = .ok 255 := by decide +kernel
example : ((updateScalar .unchecked (.inc true) (.uint 0) true (BitVec.ofNat 8 255)).map
    fun changed => (changed.next.toNat, changed.result.map BitVec.toNat)) = .ok (0, some 255) := by decide +kernel
example : ((updateScalar .checked (.inc false) (.sint 0) true (BitVec.ofInt 8 127)).map
    fun changed => changed.next.toNat) = .error (.panic (Contract.panic 0x11)) := by decide +kernel
example : ((updateScalar .checked .delete (.uint 0) true (BitVec.ofNat 8 7)).map
    fun changed => (changed.next.toNat, changed.result.map BitVec.toNat)) = .ok (0, none) := by decide +kernel
example : operatorSignature (.arithmetic .add) 7 (.scalar (.uint 0))
    ⟨3, .cons (.valueType 7 (.scalar (.uint 0))) (.cons (.valueType 7 (.scalar (.uint 0))) .nil),
      .cons (.valueType 7 (.scalar (.uint 0))) .nil, .pure, true⟩ = true := by decide +kernel
example : operatorSignature (.arithmetic .add) 7 (.scalar (.uint 0))
    ⟨3, .cons (.valueType 7 (.scalar (.uint 0))) (.cons (.valueType 7 (.scalar (.uint 0))) .nil),
      .cons (.valueType 7 (.scalar (.uint 0))) .nil, .view, true⟩ = false := by decide +kernel

end Solidity.Frontend.Inference.Tests
