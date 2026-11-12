/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Lexical

namespace Solidity.Frontend.Lexical
open Static Core

inductive StringKind where
  | ascii | unicode | hex
  deriving DecidableEq, Repr

/-- Quotes delimit a token; the body preserves raw escape spelling. Adjacent
pieces are concatenated only when their token kinds match, as in the parser. -/
structure StringPiece where
  kind : StringKind
  quote : Char
  body : String
  deriving DecidableEq, Repr

private def unicodeBMP (n : Nat) : List UInt8 :=
  if n ≤ 0x7f then [n.toUInt8]
  else if n ≤ 0x7ff then [(0xc0 + n / 64).toUInt8, (0x80 + n % 64).toUInt8]
  else [(0xe0 + n / 4096).toUInt8, (0x80 + n / 64 % 64).toUInt8, (0x80 + n % 64).toUInt8]

private def linebreak (c : Char) : Bool :=
  (0x0a ≤ c.toNat && c.toNat ≤ 0x0d) || [0x85, 0x2028, 0x2029].contains c.toNat

/-- Direction markers are checked on raw Unicode source, not on the result of
escape decoding. A backslash-u escape is not a raw direction marker. -/
def bidi : List Char → Nat → Bool
  | [], depth => depth == 0
  | c :: rest, depth =>
      if [0x202a, 0x202b, 0x202d, 0x202e].contains c.toNat then bidi rest (depth+1)
      else if c.toNat == 0x202c then depth != 0 && bidi rest (depth-1)
      else bidi rest depth

def stringBody (unicode : Bool) (quote : Char) : List Char → Option (List UInt8)
  | [] => some []
  | '\\' :: '\r' :: '\n' :: rest => stringBody unicode quote rest
  | '\\' :: '\n' :: rest | '\\' :: '\r' :: rest => stringBody unicode quote rest
  | '\\' :: 'x' :: a :: b :: rest => do
      let value ← digits 16 [a, b] 0
      return value.toUInt8 :: (← stringBody unicode quote rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest => do
      let value ← digits 16 [a, b, c, d] 0
      return unicodeBMP value ++ (← stringBody unicode quote rest)
  | '\\' :: c :: rest => do
      let escaped ← match c with
        | '\'' => some 39 | '"' => some 34 | '\\' => some 92
        | 'n' => some 10 | 'r' => some 13 | 't' => some 9
        | _ => none
      return escaped.toUInt8 :: (← stringBody unicode quote rest)
  | c :: rest =>
      if c == '\\' || c == quote || linebreak c ||
          (!unicode && (c.toNat ≤ 0x1f || c.toNat ≥ 0x7f)) then none
      else do return (String.singleton c).toUTF8.data.toList ++ (← stringBody unicode quote rest)

def hexBody : List Char → Bool → Option (List UInt8)
  | [], _ => some []
  | '_' :: rest, allow => if allow && !rest.isEmpty then hexBody rest false else none
  | a :: b :: rest, _ => do
      let value ← digits 16 [a, b] 0
      return value.toUInt8 :: (← hexBody rest true)
  | _, _ => none

def StringPiece.decodeRaw (piece : StringPiece) : Except Error (List UInt8) := do
  if piece.quote != '\'' && piece.quote != '"' then throw .malformed
  let bytes ← require (match piece.kind with
    | .hex => hexBody piece.body.toList false
    | .ascii => stringBody false piece.quote piece.body.toList
    | .unicode => stringBody true piece.quote piece.body.toList) .malformed
  if piece.kind == .unicode then
    if !bidi piece.body.toList 0 then throw .malformed
  return bytes

def StringPiece.decode (piece : StringPiece) : Except Error (List UInt8) := do
  let bytes ← piece.decodeRaw
  if piece.kind == .unicode && !ByteArray.validateUTF8 ⟨bytes.toArray⟩ then throw .invalidUTF8
  return bytes

/-- UTF-8 validation happens after concatenating adjacent Unicode tokens. Escaped
bytes can split one UTF-8 sequence across token boundaries. Raw bidi markers are
still checked separately within each token by the scanner. -/
def stringPieces (pieces : List StringPiece) : Except Error (List UInt8) := do
  let some first := pieces.head? | throw .malformed
  let bytes ← pieces.foldlM (fun acc piece => do
    if piece.kind != first.kind then throw .malformed
    return acc ++ (← piece.decodeRaw)) []
  if first.kind == .unicode && !ByteArray.validateUTF8 ⟨bytes.toArray⟩ then throw .invalidUTF8
  return bytes

/-- Literal-to-reference conversion is a typing rule only. Allocation/copying
into memory or storage uses the aggregate heap interface; calldata and storage pointers are
not permitted destinations for a string literal. -/
def StringConverts (bytes : List UInt8) : SType → Prop
  | .fixedBytes w => bytes.length ≤ w.val + 1
  | .bytes loc pointer => loc ≠ .calldata ∧ (loc ≠ .storage ∨ pointer = false)
  | .string loc pointer => loc ≠ .calldata ∧ (loc ≠ .storage ∨ pointer = false) ∧
      ByteArray.validateUTF8 ⟨bytes.toArray⟩ = true
  | _ => False

def stringConverts (bytes : List UInt8) : SType → Bool
  | .fixedBytes w => bytes.length ≤ w.val + 1
  | .bytes loc pointer => loc != .calldata && (loc != .storage || !pointer)
  | .string loc pointer => loc != .calldata && (loc != .storage || !pointer) &&
      ByteArray.validateUTF8 ⟨bytes.toArray⟩
  | _ => false

theorem stringConverts_iff (bytes : List UInt8) (type : SType) :
    stringConverts bytes type = true ↔ StringConverts bytes type := by
  cases type <;> simp [stringConverts, StringConverts, and_assoc]

def stringWord (width : Width) (bytes : List UInt8) : BitVec width.bits :=
  BitVec.ofNat width.bits ((bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0) *
    256^(width.val+1-bytes.length))

end Solidity.Frontend.Lexical
