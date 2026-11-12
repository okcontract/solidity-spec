/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Prepare

namespace Solidity.Frontend.Tests
open Core

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

def scope : Scope := [("x", .uint 0)]
def four : Literal.Expr := .binary .mul (.number (mkRat 1 2)) (.number 8)
def sum (mode : ArithmeticMode) : Expr SourceLeaf (.uint 0) :=
  .binary (.uintArithmetic 0 mode .add) (.read (.name "x")) (.read (.uint 0 four))

def run (source : Expr SourceLeaf type) (value : BitVec 8) : Except PrepareError (Result type.Value) :=
  (prepare scope source).map fun target => Expr.eval (Env.cons value .nil).get .leftFirst target

example : run (sum .checked) 2 = .ok (.ok 6) := by decide +kernel
example : run (sum .checked) 252 = .ok (.error (Contract.panic 0x11)) := by decide +kernel
example : run (sum .unchecked) 252 = .ok (.ok 0) := by decide +kernel

/-- Static checking is eager even when runtime branch selection is lazy. -/
def invalidBranch : Expr SourceLeaf (.uint 0) :=
  .ite (.literal false) (.read (.uint 0 (.number 256))) (.literal 7)
example : run invalidBranch 0 = .error (.constant .notRepresentable) := by decide +kernel

def unknownBranch : Expr SourceLeaf (.uint 0) :=
  .ite (.literal false) (.read (.name "missing")) (.literal 7)
example : run unknownBranch 0 = .error (.binding (.unbound "missing")) := by decide +kernel

def fractional : Expr SourceLeaf (.uint 0) := .read (.uint 0 (.number (mkRat 1 2)))
example : run fractional 0 = .error (.constant .notRepresentable) := by decide +kernel

def constantZeroDivision : Expr SourceLeaf .word :=
  .read (.uint 31 (.binary .div (.number 1) (.number 0)))
example : run constantZeroDivision 0 = .error (.constant .zeroDivisor) := by decide +kernel

/-- A runtime divisor of zero reaches the runtime panic layer instead. -/
def runtimeZeroDivision : Expr SourceLeaf (.uint 0) :=
  .binary (.uintArithmetic 0 .unchecked .div) (.literal 1) (.read (.name "x"))
example : run runtimeZeroDivision 0 = .ok (.error (Contract.panic 0x12)) := by decide +kernel

example : run (.read (.sint 0 (.number (-128)))) 0 = .ok (.ok 128) := by decide +kernel

end Solidity.Frontend.Tests
