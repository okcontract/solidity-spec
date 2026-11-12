/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Resolve

namespace Solidity.Frontend.Tests
open Core

def scope : Scope := [("flag", .bool), ("x", .uint 0), ("x", .word)]

example : resolveName scope "x" (.uint 0) = .ok (.there .here) := by rfl
-- A shadowing declaration with the wrong type is an error, not a fallback to x:uint256.
example : resolveName scope "x" .word = .error (.typeMismatch "x" .word (.uint 0)) := by rfl
example : resolveName scope "missing" .word = .error (.unbound "missing") := by rfl
example : resolve scope (Expr.and (.literal false) (.read (.name "missing"))) =
    .error (.unbound "missing") := by rfl
example : resolve scope (Expr.binary (.uintArithmetic 0 .checked .add)
    (.read (.name "x")) (.literal 1)) =
    .ok (.binary (.uintArithmetic 0 .checked .add) (.read (.there .here)) (.literal 1)) := by rfl

end Solidity.Frontend.Tests
