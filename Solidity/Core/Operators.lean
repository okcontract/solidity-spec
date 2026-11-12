/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Conversions
import Solidity.Core.Power

namespace Solidity.Static
open Core

inductive BinaryCode where
  | arithmetic : Arithmetic → BinaryCode
  | bits : Bitwise → BinaryCode
  | compare : Comparison → BinaryCode
  | pow | shl | shr | and | or
  deriving DecidableEq, Repr

def BinaryCode.asymmetric : BinaryCode → Bool
  | .pow | .shl | .shr => true | _ => false

/-- These indexed constructors are the independent scalar operator typing rules.
The executable checker below constructs a derivation, after the frontend has
selected and inserted the permitted operand conversions. -/
inductive ScalarBinary : BinaryCode → SType → SType → SType → Type where
  | uintArithmetic : ScalarBinary (.arithmetic op) (.uint w) (.uint w) (.uint w)
  | sintArithmetic : ScalarBinary (.arithmetic op) (.sint w) (.sint w) (.sint w)
  | uintBits : ScalarBinary (.bits op) (.uint w) (.uint w) (.uint w)
  | sintBits : ScalarBinary (.bits op) (.sint w) (.sint w) (.sint w)
  | bytesBits : ScalarBinary (.bits op) (.fixedBytes w) (.fixedBytes w) (.fixedBytes w)
  | uintCompare : ScalarBinary (.compare op) (.uint w) (.uint w) .bool
  | sintCompare : ScalarBinary (.compare op) (.sint w) (.sint w) .bool
  | bytesCompare : ScalarBinary (.compare op) (.fixedBytes w) (.fixedBytes w) .bool
  | addressCompare : ScalarBinary (.compare op) (.address pay) (.address pay) .bool
  | enumCompare : ScalarBinary (.compare op) (.enumType identity n) (.enumType identity n) .bool
  | contractCompare : ScalarBinary (.compare op) (.contract identity pay bases) (.contract identity pay bases) .bool
  | boolEq : ScalarBinary (.compare .eq) .bool .bool .bool
  | boolNe : ScalarBinary (.compare .ne) .bool .bool .bool
  | functionEq : ScalarBinary (.compare .eq) (.function vis stateMut ps rs) (.function vis stateMut ps rs) .bool
  | functionNe : ScalarBinary (.compare .ne) (.function vis stateMut ps rs) (.function vis stateMut ps rs) .bool
  | and : ScalarBinary .and .bool .bool .bool
  | or : ScalarBinary .or .bool .bool .bool
  | uintPow : ScalarBinary .pow (.uint w) (.uint count) (.uint w)
  | sintPow : ScalarBinary .pow (.sint w) (.uint count) (.sint w)
  | uintShl : ScalarBinary .shl (.uint w) (.uint count) (.uint w)
  | uintShr : ScalarBinary .shr (.uint w) (.uint count) (.uint w)
  | sintShl : ScalarBinary .shl (.sint w) (.uint count) (.sint w)
  | sintShr : ScalarBinary .shr (.sint w) (.uint count) (.sint w)
  | bytesShl : ScalarBinary .shl (.fixedBytes w) (.uint count) (.fixedBytes w)
  | bytesShr : ScalarBinary .shr (.fixedBytes w) (.uint count) (.fixedBytes w)

def checkHomogeneous (op : BinaryCode) (type : SType) : Option (Σ result, ScalarBinary op type type result) :=
  match op, type with
  | .arithmetic _, .uint _ => some ⟨_, .uintArithmetic⟩
  | .arithmetic _, .sint _ => some ⟨_, .sintArithmetic⟩
  | .bits _, .uint _ => some ⟨_, .uintBits⟩
  | .bits _, .sint _ => some ⟨_, .sintBits⟩
  | .bits _, .fixedBytes _ => some ⟨_, .bytesBits⟩
  | .compare _, .uint _ => some ⟨_, .uintCompare⟩
  | .compare _, .sint _ => some ⟨_, .sintCompare⟩
  | .compare _, .fixedBytes _ => some ⟨_, .bytesCompare⟩
  | .compare _, .address _ => some ⟨_, .addressCompare⟩
  | .compare _, .enumType _ _ => some ⟨_, .enumCompare⟩
  | .compare _, .contract _ _ _ => some ⟨_, .contractCompare⟩
  | .compare .eq, .bool => some ⟨_, .boolEq⟩
  | .compare .ne, .bool => some ⟨_, .boolNe⟩
  | .compare .eq, .function _ _ _ _ => some ⟨_, .functionEq⟩
  | .compare .ne, .function _ _ _ _ => some ⟨_, .functionNe⟩
  | .and, .bool => some ⟨_, .and⟩
  | .or, .bool => some ⟨_, .or⟩
  | _, _ => none

def checkBinary (op : BinaryCode) (a b : SType) : Option (Σ result, ScalarBinary op a b result) :=
  match op, a, b with
  | .pow, .uint _, .uint _ => some ⟨_, .uintPow⟩
  | .pow, .sint _, .uint _ => some ⟨_, .sintPow⟩
  | .shl, .uint _, .uint _ => some ⟨_, .uintShl⟩
  | .shr, .uint _, .uint _ => some ⟨_, .uintShr⟩
  | .shl, .sint _, .uint _ => some ⟨_, .sintShl⟩
  | .shr, .sint _, .uint _ => some ⟨_, .sintShr⟩
  | .shl, .fixedBytes _, .uint _ => some ⟨_, .bytesShl⟩
  | .shr, .fixedBytes _, .uint _ => some ⟨_, .bytesShr⟩
  | op, a, b => if same : b = a then same ▸ checkHomogeneous op a else none

variable {op : BinaryCode} {a b result : SType}

theorem checkBinary_complete (operation : ScalarBinary op a b result) :
    checkBinary op a b = some ⟨result, operation⟩ := by
  cases operation <;> simp [checkBinary, checkHomogeneous]

theorem checkBinary_iff (op : BinaryCode) (a b result : SType) :
    (∃ operation, checkBinary op a b = some ⟨result, operation⟩) ↔
      Nonempty (ScalarBinary op a b result) := by
  constructor
  · rintro ⟨operation, _⟩; exact ⟨operation⟩
  · rintro ⟨operation⟩; exact ⟨operation, checkBinary_complete operation⟩

private def functionEqual : (vis : Visibility) → FunctionValue vis → FunctionValue vis → Bool
  | .internal, a, b => (a : Option Nat) == b
  | .external, a, b => (a : BitVec 160 × BitVec 32) == b

def ScalarBinary.eval (mode : ArithmeticMode) : ScalarBinary op a b result →
    a.Value → b.Value → Core.Result result.Value
  | .uintArithmetic (op := operation), a, b => unsigned _ mode operation a b
  | .sintArithmetic (op := operation), a, b => signed _ mode operation a b
  | .uintBits (op := operation), a, b | .sintBits (op := operation), a, b | .bytesBits (op := operation), a, b => .ok (bitwise operation a b)
  | .uintCompare (op := operation), a, b | .bytesCompare (op := operation), a, b | .addressCompare (op := operation), a, b |
    .contractCompare (op := operation), a, b => .ok (compareUnsigned operation a b)
  | .sintCompare (op := operation), a, b => .ok (compareSigned operation a b)
  | .enumCompare (op := operation), a, b => .ok (compareUnsigned operation (BitVec.ofNat 8 a.val) (BitVec.ofNat 8 b.val))
  | .boolEq, a, b => .ok (a == b)
  | .boolNe, a, b => .ok (a != b)
  | .functionEq, a, b => .ok (functionEqual _ a b)
  | .functionNe, a, b => .ok (!(functionEqual _ a b))
  | .and, a, b => .ok (a && b)
  | .or, a, b => .ok (a || b)
  | .uintPow, a, b => unsignedPow _ _ mode a b
  | .sintPow, a, b => signedPow _ _ mode a b
  | .uintShl (w := w) (count := count), a, b => (Core.Binary.uintShl w count).eval a b
  | .sintShl (w := w) (count := count), a, b => (Core.Binary.sintShl w count).eval a b
  | .bytesShl (w := w) (count := count), a, b => (Core.Binary.uintShl w count).eval a b
  | .uintShr (w := w) (count := count), a, b => (Core.Binary.uintShr w count).eval a b
  | .bytesShr (w := w) (count := count), a, b => (Core.Binary.uintShr w count).eval a b
  | .sintShr (w := w) (count := count), a, b => (Core.Binary.sintShr w count).eval a b

/-- Comparison checks are symmetric only after selecting the common type. The
checker does not invent a common signed/unsigned type outside implicit rules. -/
def common (a b : SType) : Option SType :=
  if implicit b a then some a else if implicit a b then some b else none

def Common (a b result : SType) : Prop :=
  (Implicit b a ∧ result = a) ∨ (¬ Implicit b a ∧ Implicit a b ∧ result = b)

theorem common_iff (a b result : SType) : common a b = some result ↔ Common a b result := by
  simp only [common, Common]
  split
  next h => simp [(implicit_iff _ _).mp h, eq_comm]
  next h =>
    have no : ¬ Implicit b a := fun yes => h ((implicit_iff _ _).mpr yes)
    simp only [no, false_and, not_false_eq_true, true_and, false_or]
    split
    next yes => simp [(implicit_iff _ _).mp yes, eq_comm]
    next no2 => simp [show ¬ Implicit a b from fun yes => no2 ((implicit_iff _ _).mpr yes)]

end Solidity.Static
