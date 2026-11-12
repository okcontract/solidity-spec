/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Literal
import Solidity.Core.StaticTypes
import Contract.Export.Keccak

/-! Literal spellings, independent of expression parsing. Source-unit tokenization
and the connection from source bytes to these tokens are input assumptions. The
numeric precision policy is compiler admission, not runtime overflow. -/
namespace Solidity.Frontend.Lexical
open Core Static

inductive Error where
  | malformed | invalidUnit | precision | addressChecksum | invalidUTF8
  deriving DecidableEq, Repr

inductive Unit where
  | none | wei | gwei | ether | seconds | minutes | hours | days | weeks | years
  deriving DecidableEq, Repr

def Unit.factor : Unit → Option Nat
  | .none | .wei | .seconds => some 1
  | .gwei => some (10^9) | .ether => some (10^18)
  | .minutes => some 60 | .hours => some 3600 | .days => some 86400
  | .weeks => some 604800 | .years => Option.none

def digit (base : Nat) (c : Char) : Option Nat :=
  let n := if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  n.bind fun d => if d < base then some d else none

/-- Positional digits have a structural judgment, rather than being specified
by successful execution of the decoder. Leading zero policy is a separate rule. -/
inductive Digits (base : Nat) : List Char → Nat → Nat → Prop where
  | nil : Digits base [] acc acc
  | cons : digit base c = some d → Digits base rest (acc * base + d) value →
      Digits base (c :: rest) acc value

def digits (base : Nat) : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: rest, acc => (digit base c).bind fun d => digits base rest (acc * base + d)

theorem digits_iff (base : Nat) (cs : List Char) (acc value : Nat) :
    digits base cs acc = some value ↔ Digits base cs acc value := by
  induction cs generalizing acc with
  | nil => simp only [digits, Option.some.injEq]; constructor
           · intro h; subst h; exact .nil
           · intro h; cases h; rfl
  | cons c rest ih =>
      simp only [digits]
      cases h : digit base c with
      | none => simp only [Option.bind_none, reduceCtorEq, false_iff]
                intro valid; cases valid with | cons hd _ => simp [h] at hd
      | some d =>
          simp only [Option.bind_some, ih]
          constructor
          · exact .cons h
          · intro valid; cases valid with | cons hd tail => cases h.symm.trans hd; exact tail

/-- Round an exact nonnegative integer to the nearest binary64 significand,
ties to even. The input here is an exactly representable int32 exponent times
the exact stored binary64 value of log2(10), whose denominator is 2^51. -/
def round53 (n : Nat) : Nat :=
  let shift := (n.log2 + 1) - Policy.Solc0836.binary64SignificandBits
  let scale := 2^shift
  let q := n / scale
  let r := n % scale
  (q + if 2*r > scale || (2*r == scale && q % 2 == 1) then 1 else 0) * scale

def decimalExponentBits (exponent : Nat) : Nat :=
  round53 (exponent * Policy.Solc0836.decimalLog2Numerator) / Policy.Solc0836.decimalLog2Denominator

def scientificFits (mantissa exponent : Nat) : Bool :=
  mantissa == 0 || mantissa.log2 + decimalExponentBits exponent + 1 ≤ Policy.Solc0836.rationalWorkBits

structure Number where
  value : Rat
  /-- Only an original hex token has fixed-bytes compatibility. Computation
  drops this attribute even when it leaves the rational value unchanged. -/
  hexBytes : Option Width := none
  deriving DecidableEq, Repr

inductive Numeric where
  | rational : Number → Numeric
  | address : BitVec 160 → Numeric
  deriving DecidableEq, Repr

def splitChar (separator : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
      match splitChar separator rest with
      | [] => [[c]]
      | first :: tail => if c == separator then [] :: first :: tail else (c :: first) :: tail

def containsPair (first second : Char) : List Char → Bool
  | a :: b :: rest => (a == first && b == second) || containsPair first second (b :: rest)
  | _ => false

/-- Syntax-checker exclusions are case sensitive in the pinned implementation:
1E_2 and 1_E2 are accepted, while the corresponding lower-case e forms are not.
The source spelling is retained until these checks have run. -/
def separators (s : String) : Bool :=
  let cs := s.toList
  cs.getLast? != some '_' && !containsPair '_' '_' cs &&
  (['0', 'x'].isPrefixOf cs || !(Policy.Solc0836.numericSeparatorExclusions.any
    fun (a, b) => containsPair a b cs))

def decimalChars (cs : List Char) : Option Rat := do
  let (whole, frac) ← match splitChar '.' cs with
    | [w] => some (w, [])
    | [w, f] => if f.isEmpty then none else some (w, f)
    | _ => none
  if whole.isEmpty && frac.isEmpty then none else do
  if whole.length > 1 && whole.head? == some '0' then none else do
  let w ← digits 10 whole 0
  let f ← digits 10 frac 0
  pure (Rat.ofInt w + Rat.divInt f (10^frac.length))

def decimalMantissa (s : String) : Option Rat := decimalChars s.toList

def require (value : Option α) (error : Error) : Except Error α :=
  match value with | some value => .ok value | none => .error error

def scientific (mantissa : Rat) (cs : List Char) : Except Error Rat := do
  let negative := cs.head? == some '-'
  let plus := cs.head? == some '+'
  let ds := if negative || plus then cs.drop 1 else cs
  if ds.isEmpty then throw .malformed
  let _ ← require (digits 10 ds 0) .malformed
  -- Zero short-circuits value parsing, but not the exponent's lexical grammar.
  if mantissa = 0 then return 0
  if plus then throw .malformed
  -- Pinned bigint parsing interprets a leading zero as octal in the exponent.
  -- This is an implementation quirk, retained explicitly in the divergence ledger.
  let magnitude ← require (digits (Policy.Solc0836.scientificExponentRadix ds.head?) ds 0) .malformed
  if magnitude > (if negative then 2^Policy.Solc0836.scientificExponentMagnitudeBits
    else 2^Policy.Solc0836.scientificExponentMagnitudeBits-1) then throw .precision
  if magnitude = 0 then return mantissa
  if !(scientificFits (if negative then mantissa.den else mantissa.num.natAbs) magnitude) then
    throw .precision
  return if negative then mantissa / Rat.ofInt (10^magnitude) else mantissa * Rat.ofInt (10^magnitude)

def addressChecksum (hex : String) : Bool :=
  let hash := Contract.Export.Keccak.hash hex.toLower.toUTF8
  hex.toList.zipIdx.all fun (c, i) =>
    if c.isDigit then true else
    let byte := hash[i/2]!
    let nibble := if i % 2 = 0 then byte.toNat / 16 else byte.toNat % 16
    if nibble ≥ 8 then c == c.toUpper else c == c.toLower

/- A spelling must start with a decimal digit, or a dot immediately followed
by one. Check the original token before removing separators: normalization
must not turn an identifier or a broken hex prefix into a numeric literal. -/
def startsNumber : List Char → Bool
  | '.' :: c :: _ => (digit 10 c).isSome
  | c :: _ => (digit 10 c).isSome
  | [] => false

def number (spelling : String) (unit : Unit := .none) : Except Error Numeric := do
  if !separators spelling then throw .malformed
  let factor ← require unit.factor .invalidUnit
  let raw := spelling.toList
  if !startsNumber raw then throw .malformed
  let clean := raw.filter (· != '_')
  if ['0', 'x'].isPrefixOf raw then
    if unit != .none then throw .invalidUnit
    let hex := clean.drop 2
    if hex.isEmpty || raw[2]? == some '_' then throw .malformed
    let value ← require (digits 16 hex 0) .malformed
    if 39 ≤ hex.length && hex.length ≤ 41 then
      if hex.length != 40 || !addressChecksum (String.ofList hex) then throw .addressChecksum
      return .address (BitVec.ofNat 160 value)
    let bytes := hex.length / 2
    let compatible := if h : hex.length % 2 = 0 ∧ 0 < bytes ∧ bytes ≤ 32 then
      some (⟨bytes-1, by omega⟩ : Width) else none
    return .rational ⟨Rat.ofInt value, compatible⟩
  else
    if ['0', '_'].isPrefixOf raw then throw .malformed
    let parts := splitChar 'e' (clean.map fun c => if c == 'E' then 'e' else c)
    let value ← match parts with
      | [s] => require (decimalChars s) .malformed
      | [s, e] => do scientific (← require (decimalChars s) .malformed) e
      | _ => throw .malformed
    return .rational ⟨value * Rat.ofInt factor, none⟩

theorem digits_bound (base : Nat) (cs : List Char) (value : Nat)
    (decoded : Digits base cs 0 value) : value < base^cs.length := by
  have general : ∀ cs acc value, Digits base cs acc value →
      value < (acc + 1) * base^cs.length := by
    intro cs acc value derivation
    induction derivation with
    | nil => simp
    | @cons c d rest acc value hd _ ih =>
        have digitBound : d < base := by
          unfold digit at hd
          simp only [Option.bind_eq_some_iff] at hd
          obtain ⟨n, _, hn⟩ := hd
          split at hn <;> simp_all
        simp only [List.length_cons, Nat.pow_succ]
        have step : acc * base + d + 1 ≤ (acc+1)*base := by simp only [Nat.add_mul, Nat.one_mul]; omega
        exact Nat.lt_of_lt_of_le ih (by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_right (base^rest.length) step)
  simpa using general cs 0 value decoded

end Solidity.Frontend.Lexical
