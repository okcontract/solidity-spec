/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Scalar

namespace Solidity.Core

/-- Static ABI word representation. This internal encoding is not a source
conversion permission and does not implement the general ABI decoder. -/
def Ty.abiWord : (t : Ty) → t.Value → BitVec 256
  | .uint _, value => value.setWidth 256
  | .sint _, value => BitVec.ofInt 256 value.toInt
  | .fixedBytes width, value => value.setWidth 256 <<< (256 - width.bits)
  | .bool, value => if value then 1 else 0
  | .address, value => value.setWidth 256

end Solidity.Core

namespace Solidity.Core.StaticABI

/-- Canonical single-word encodings. Dynamic values and aggregate ABI layout
are outside this interface. Signed words must be sign-extended; fixed bytes
are left-aligned and have zero padding. -/
def Canonical (type : Ty) (word : BitVec 256) : Prop :=
  match type with
  | .uint width => word.toNat < 2 ^ width.bits
  | .sint width => BitVec.ofInt 256 ((word.setWidth width.bits).toInt) = word
  | .fixedBytes width => word &&& (BitVec.ofNat 256 (2^256 - 2^(256-width.bits))) = word
  | .bool => word = 0 ∨ word = 1
  | .address => word.toNat < 2^160

instance (type : Ty) (word : BitVec 256) : Decidable (Canonical type word) := by
  cases type <;> unfold Canonical <;> infer_instance

def decodeValue : (type : Ty) → BitVec 256 → type.Value
  | .uint width, word => word.setWidth width.bits
  | .sint width, word => word.setWidth width.bits
  | .fixedBytes width, word => (word >>> (256-width.bits)).setWidth width.bits
  | .bool, word => word != 0
  | .address, word => word.setWidth 160

def decode (type : Ty) (word : BitVec 256) : Option type.Value :=
  if Canonical type word then some (decodeValue type word) else none

theorem decode_accepts (type : Ty) (word : BitVec 256) :
    (decode type word).isSome = true ↔ Canonical type word := by
  unfold decode; split <;> simp_all

end Solidity.Core.StaticABI
