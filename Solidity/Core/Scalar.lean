/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Target
import Contract.Language.Word

/-! Typed scalar primitives for Solidity 0.8.36. Widths are bytes minus one, so
only 8,16,...,256-bit integers/fixed bytes are representable. Arithmetic mode
is explicit. Source division by zero panics in both modes; EVM division is a
separate lower-level operation. No source admission is implied by this module. -/
namespace Solidity.Core

inductive OperandOrder where
  | leftFirst | rightFirst
  deriving DecidableEq, Repr

abbrev Width := Fin 32

def Width.bits (width : Width) : Nat := 8 * (width.val + 1)

theorem Width.bits_pos (width : Width) : 0 < width.bits := by
  simp [bits]

theorem Width.bits_le (width : Width) : width.bits ≤ 256 := by
  have := width.isLt
  simp only [bits]
  omega

inductive Ty where
  | uint (width : Width)
  | sint (width : Width)
  | fixedBytes (width : Width)
  | bool
  | address
  deriving DecidableEq, Repr

abbrev Ty.word : Ty := .uint 31

abbrev Ty.Value : Ty → Type
  | .uint width | .sint width | .fixedBytes width => BitVec width.bits
  | .bool => Bool
  | .address => BitVec 160

def Ty.equal : (type : Ty) → type.Value → type.Value → Bool
  | .uint _, a, b => a == b
  | .sint _, a, b => a == b
  | .fixedBytes _, a, b => a == b
  | .bool, a, b => a == b
  | .address, a, b => a == b

inductive ArithmeticMode where
  | checked | unchecked
  deriving DecidableEq, Repr

inductive Arithmetic where
  | add | sub | mul | div | mod
  deriving DecidableEq, Repr

inductive Bitwise where
  | bitand | bitor | bitxor
  deriving DecidableEq, Repr

inductive Comparison where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

abbrev Result (α : Type) := Except (List UInt8) α

def unsigned (width : Width) (mode : ArithmeticMode) (op : Arithmetic)
    (a b : BitVec width.bits) : Result (BitVec width.bits) :=
  match op with
  | .add => if mode == .unchecked || a.toNat + b.toNat < 2 ^ width.bits then
      .ok (a + b) else .error (Contract.panic 0x11)
  | .sub => if mode == .unchecked || b ≤ a then
      .ok (a - b) else .error (Contract.panic 0x11)
  | .mul => if mode == .unchecked || a.toNat * b.toNat < 2 ^ width.bits then
      .ok (a * b) else .error (Contract.panic 0x11)
  | .div => if b = 0 then .error (Contract.panic 0x12) else .ok (a / b)
  | .mod => if b = 0 then .error (Contract.panic 0x12) else .ok (a % b)

def signedResult (width : Width) (mode : ArithmeticMode) (value : Int) :
    Result (BitVec width.bits) :=
  let limit : Int := 2 ^ (width.bits - 1)
  if mode == .unchecked || (-limit ≤ value && value < limit) then
    .ok (BitVec.ofInt width.bits value)
  else .error (Contract.panic 0x11)

def signed (width : Width) (mode : ArithmeticMode) (op : Arithmetic)
    (a b : BitVec width.bits) : Result (BitVec width.bits) :=
  match op with
  | .add => signedResult width mode (a.toInt + b.toInt)
  | .sub => signedResult width mode (a.toInt - b.toInt)
  | .mul => signedResult width mode (a.toInt * b.toInt)
  | .div => if b = 0 then .error (Contract.panic 0x12)
      else signedResult width mode (a.toInt.tdiv b.toInt)
  | .mod => if b = 0 then .error (Contract.panic 0x12) else .ok (a.srem b)

def bitwise (op : Bitwise) (a b : BitVec bits) : BitVec bits :=
  match op with
  | .bitand => a &&& b
  | .bitor => a ||| b
  | .bitxor => a ^^^ b

def compareUnsigned (op : Comparison) (a b : BitVec bits) : Bool :=
  match op with
  | .eq => a == b | .ne => a != b
  | .lt => a.ult b | .le => a.ule b | .gt => b.ult a | .ge => b.ule a

def compareSigned (op : Comparison) (a b : BitVec bits) : Bool :=
  match op with
  | .eq => a == b | .ne => a != b
  | .lt => decide (a.toInt < b.toInt) | .le => decide (a.toInt ≤ b.toInt)
  | .gt => decide (b.toInt < a.toInt) | .ge => decide (b.toInt ≤ a.toInt)

inductive Unary : Ty → Ty → Type where
  | not : Unary .bool .bool
  | uintNot (width : Width) : Unary (.uint width) (.uint width)
  | sintNot (width : Width) : Unary (.sint width) (.sint width)
  | bytesNot (width : Width) : Unary (.fixedBytes width) (.fixedBytes width)
  | negate (width : Width) (mode : ArithmeticMode) : Unary (.sint width) (.sint width)
  | uintCast (src dst : Width) : Unary (.uint src) (.uint dst)
  | sintCast (src dst : Width) : Unary (.sint src) (.sint dst)
  | toSigned (width : Width) : Unary (.uint width) (.sint width)
  | toUnsigned (width : Width) : Unary (.sint width) (.uint width)
  | addressOfUint : Unary (.uint 19) .address
  | uintOfAddress : Unary .address (.uint 19)
  | boolWord : Unary .bool .word

def Unary.eval : Unary a b → a.Value → Result b.Value
  | .not, value => .ok (!value)
  | .uintNot _, value => .ok (~~~value)
  | .sintNot _, value => .ok (~~~value)
  | .bytesNot _, value => .ok (~~~value)
  | .negate width mode, value => signedResult width mode (-value.toInt)
  | .uintCast _ to, value => .ok (BitVec.ofNat to.bits value.toNat)
  | .sintCast _ to, value => .ok (BitVec.ofInt to.bits value.toInt)
  | .toSigned _, value => .ok value
  | .toUnsigned _, value => .ok value
  | .addressOfUint, value => .ok value
  | .uintOfAddress, value => .ok value
  | .boolWord, value => .ok (if value then 1 else 0)

inductive Binary : Ty → Ty → Ty → Type where
  | uintArithmetic (width : Width) (mode : ArithmeticMode) (op : Arithmetic) :
      Binary (.uint width) (.uint width) (.uint width)
  | sintArithmetic (width : Width) (mode : ArithmeticMode) (op : Arithmetic) :
      Binary (.sint width) (.sint width) (.sint width)
  | uintBits (width : Width) (op : Bitwise) : Binary (.uint width) (.uint width) (.uint width)
  | sintBits (width : Width) (op : Bitwise) : Binary (.sint width) (.sint width) (.sint width)
  | bytesBits (width : Width) (op : Bitwise) : Binary (.fixedBytes width) (.fixedBytes width) (.fixedBytes width)
  | uintCompare (width : Width) (op : Comparison) : Binary (.uint width) (.uint width) .bool
  | sintCompare (width : Width) (op : Comparison) : Binary (.sint width) (.sint width) .bool
  | equal (type : Ty) : Binary type type .bool
  | uintShl (width count : Width) : Binary (.uint width) (.uint count) (.uint width)
  | uintShr (width count : Width) : Binary (.uint width) (.uint count) (.uint width)
  | sintShl (width count : Width) : Binary (.sint width) (.uint count) (.sint width)
  | sintShr (width count : Width) : Binary (.sint width) (.uint count) (.sint width)

def Binary.eval : Binary a b c → a.Value → b.Value → Result c.Value
  | .uintArithmetic width mode op, a, b => unsigned width mode op a b
  | .sintArithmetic width mode op, a, b => signed width mode op a b
  | .uintBits _ op, a, b => .ok (bitwise op a b)
  | .sintBits _ op, a, b => .ok (bitwise op a b)
  | .bytesBits _ op, a, b => .ok (bitwise op a b)
  | .uintCompare _ op, a, b => .ok (compareUnsigned op a b)
  | .sintCompare _ op, a, b => .ok (compareSigned op a b)
  | .equal type, a, b => .ok (type.equal a b)
  | .uintShl width _, a, b => .ok (if b.toNat < width.bits then a <<< b.toNat else 0)
  | .uintShr width _, a, b => .ok (if b.toNat < width.bits then a >>> b.toNat else 0)
  | .sintShl width _, a, b => .ok (if b.toNat < width.bits then a <<< b.toNat else 0)
  | .sintShr width _, a, b => .ok (if b.toNat < width.bits then a.sshiftRight b.toNat else
      if a.toInt < 0 then -1 else 0)

/-- Division by zero is a source panic even inside unchecked blocks. -/
theorem unsigned_div_zero (width : Width) (mode : ArithmeticMode) (a : BitVec width.bits) :
    unsigned width mode .div a 0 = .error (Contract.panic 0x12) := by simp [unsigned]

theorem signed_div_zero (width : Width) (mode : ArithmeticMode) (a : BitVec width.bits) :
    signed width mode .div a 0 = .error (Contract.panic 0x12) := by simp [signed]

end Solidity.Core
