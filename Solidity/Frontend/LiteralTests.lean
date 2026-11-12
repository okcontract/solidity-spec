/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Literal

namespace Solidity.Frontend.Literal.Tests

set_option exponentiation.threshold 8192
set_option maxRecDepth 16384

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

example : Binary.div.eval 5 2 = .ok (mkRat 5 2) := by decide +kernel
example : Binary.mod.eval (mkRat 11 2) 2 = .ok (mkRat 3 2) := by decide +kernel
example : Binary.mod.eval (mkRat (-11) 2) 2 = .ok (mkRat (-3) 2) := by decide +kernel
example : Binary.pow.eval 0 (-1) = .ok 0 := by decide +kernel
example : Binary.pow.eval 0 0 = .ok 1 := by decide +kernel
example : Binary.pow.eval 2 (-3) = .ok (mkRat 1 8) := by decide +kernel
example : Binary.pow.eval (-1) 4294967297 = .ok (-1) := by decide +kernel
example : Binary.pow.eval 2 2049 = .error .precisionLimit := by decide +kernel
example : Binary.shl.eval 1 4096 = .error .precisionLimit := by decide +kernel
example : Binary.shr.eval (-5) 1 = .ok (-3) := by decide +kernel
example : Binary.shr.eval (-5) 4294967295 = .ok (-1) := by decide +kernel
example : Binary.shr.eval 0 4294967296 = .error .precisionLimit := by decide +kernel
example : Binary.div.eval 1 0 = .error .zeroDivisor := by decide +kernel
example : Binary.bitand.eval (mkRat 1 2) 1 = .error .fractionalOperand := by decide +kernel
example : Binary.pow.eval 2 (mkRat 1 2) = .error .fractionalOperand := by decide +kernel
example : Binary.shl.eval 1 (-1) = .error .negativeShift := by decide +kernel
example : Binary.bitand.eval (-5) 3 = .ok 3 := by decide +kernel
example : Binary.bitor.eval (-5) 3 = .ok (-5) := by decide +kernel
example : Binary.bitxor.eval (-5) 3 = .ok (-8) := by decide +kernel
example : Binary.bitand.eval (-5) (-3) = .ok (-7) := by decide +kernel
example : Binary.bitor.eval (-5) (-3) = .ok (-1) := by decide +kernel
example : Binary.bitxor.eval (-5) (-3) = .ok 6 := by decide +kernel
example : Unary.bitnot.eval 5 = .ok (-6) := by decide +kernel

example : toUnsigned 0 255 = .ok 255 := by decide +kernel
example : toUnsigned 0 256 = .error .notRepresentable := by decide +kernel
example : toUnsigned 0 (-1) = .error .notRepresentable := by decide +kernel
example : toSigned 0 (-128) = .ok 128 := by decide +kernel
example : toSigned 0 (-129) = .error .notRepresentable := by decide +kernel
example : toSigned 0 128 = .error .notRepresentable := by decide +kernel
example : toUnsigned 0 (mkRat 1 2) = .error .notRepresentable := by decide +kernel

/-- Intermediate values are not truncated to a machine word. -/
def largeDifference : Expr := .binary .sub
  (.binary .add (.binary .pow (.number 2) (.number 800)) (.number 1))
  (.binary .pow (.number 2) (.number 800))
example : largeDifference.unsigned 0 = .ok 1 := by decide +kernel

/-- Fractional intermediate values can produce an integral representable result. -/
def fractionalProduct : Expr := .binary .mul (.number (mkRat 1 2)) (.number 8)
example : fractionalProduct.unsigned 0 = .ok 4 := by decide +kernel

/-- Normalization precedes the result precision check. Cross-products of the
same denominator need not fit when the reduced result does. -/
def smallFraction : Rat := mkRat 1 (2^2049)
example : Binary.add.eval smallFraction smallFraction = .ok (mkRat 1 (2^2048)) := by decide +kernel

end Solidity.Frontend.Literal.Tests
