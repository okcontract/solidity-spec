/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.SourceExpression
import Solidity.Frontend.Mobility

/-! Unannotated scalar expression elaboration. Cast destinations and resolved
nominal declarations are source information; binary operands require no supplied
type/operator plan. Source-unit parsing and declaration lookup are input assumptions.
This interface handles pure scalar expressions; fixed-point/reference execution
and effectful calls are outside its execution domain. -/
namespace Solidity.Frontend.Inference
open Core Static Lexical

inductive Source where
  | name : String → Source
  | number : String → Lexical.Unit → Source
  | string : List StringPiece → Source
  | bool : Bool → Source
  | unary : UnaryCode → Source → Source
  | binary : BinaryCode → Source → Source → Source
  | cast : CastKind → SType → Source → Source
  | ite : Source → Source → Source → Source
  | wrap : Nat → Elementary → Source → Source
  | unwrap : Nat → Elementary → Source → Source
  deriving Repr

inductive Term (context : Context) where
  | number : Number → Term context
  | string : List UInt8 → Term context
  | runtime : (type : SType) → SourceExpr context type → Term context

variable {context : Context}

def Term.mobile : Term context → Except StaticError SType
  | .number value => Frontend.mobile value.value
  | .string _ => .ok (.string .memory true)
  | .runtime type _ => .ok type

def Term.implicitTo (term : Term context) (type : SType) : Bool :=
  match term with
  | .number value => numberConverts .implicit value type
  | .string bytes => stringConverts bytes type
  | .runtime source _ => implicit source type

def materialize (conversion : ConversionMode) (term : Term context) (type : SType) :
    Except StaticError (SourceExpr context type) :=
  match term with
  | .number value => (convertNumber conversion value type).map .literal
  | .string bytes =>
      if stringConverts bytes type && conversion != .explicit .payable then
        match type with
        | .fixedBytes width => .ok (.literal (stringWord width bytes))
        | _ => .error .unsupported
      else .error .rejected
  | .runtime source expression =>
      if !source.scalarSupported || !type.scalarSupported then .error .unsupported
      else if valid : allows conversion source type then
        .ok (.cast conversion ((allows_iff _ _ _).mp valid) expression)
      else .error .rejected

def commonTerm (a b : Term context) : Except StaticError SType := do
  let left ← a.mobile
  if b.implicitTo left then return left
  let right ← b.mobile
  if a.implicitTo right then return right
  throw .rejected

def literalBinary : BinaryCode → Option Literal.Binary
  | .arithmetic .add => some .add | .arithmetic .sub => some .sub
  | .arithmetic .mul => some .mul | .arithmetic .div => some .div | .arithmetic .mod => some .mod
  | .bits .bitand => some .bitand | .bits .bitor => some .bitor | .bits .bitxor => some .bitxor
  | .pow => some .pow | .shl => some .shl | .shr => some .shr
  | _ => none

def runtimeBinary (code : BinaryCode) (a b : Term context) (left right : SType) :
    Except StaticError (Term context) := do
  let some ⟨result, operation⟩ := checkBinary code left right | throw .rejected
  let x ← materialize .implicit a left
  let y ← materialize .implicit b right
  return .runtime result (.binary operation x y)

def integerType : SType → Bool
  | .uint _ | .sint _ => true | _ => false

/-- Reject operators absent from a supported left category before looking for
mobile types of unrelated right operands. In particular, Boolean/address
arithmetic cannot become a request for fixed-point execution. -/
def permittedOnLeft (code : BinaryCode) : SType → Bool
  | .uint _ | .sint _ => code != .and && code != .or
  | .fixedBytes _ => match code with | .bits _ | .compare _ | .shl | .shr => true | _ => false
  | .address _ | .enumType _ _ | .contract _ _ _ => match code with | .compare _ => true | _ => false
  | .bool => match code with | .compare .eq | .compare .ne | .and | .or => true | _ => false
  | .function _ _ _ _ => match code with | .compare .eq | .compare .ne => true | _ => false
  | .valueType _ _ => false
  | _ => true -- unsupported categories are classified by the enclosing profile

/-- Numeric-literal binary typing is asymmetric in the pinned source rules.
A left literal delegates only to integer/fixed-point categories, whereas a right
literal may be implicitly convertible to a left fixed-bytes type. -/
def binary (code : BinaryCode) (a b : Term context) : Except StaticError (Term context) := do
  if code == .and || code == .or then return ← runtimeBinary code a b .bool .bool
  if let .runtime type _ := a then
    if !permittedOnLeft code type then throw .rejected
    if let .number value := b then
      if value.value.den != 1 && !integerType type then throw .rejected
  match a, b with
  | .string _, _ => throw .rejected
  | .number x, .number y =>
      if let some operation := literalBinary code then
        let value ← (operation.eval x.value y.value).mapError StaticError.literal
        return .number ⟨value, none⟩
      else
        let left ← a.mobile
        let right ← b.mobile
        let some type := common left right | throw .rejected
        runtimeBinary code a b type type
  | .number value, .runtime type _ =>
      if value.value.den != 1 then throw .rejected
      if !integerType type then
        if let .fixedPoint _ _ _ := type then throw .unsupported else throw .rejected
      else runtime a b
  | _, _ => runtime a b
where
  runtime (a b : Term context) : Except StaticError (Term context) := do
    if code.asymmetric then
      if let .number value := b then
        if value.value.den != 1 then throw .rejected
      let left ← match a with
        | .number value => do
            let _ ← a.mobile
            pure (if value.value.num < 0 then SType.sint 31 else .uint 31)
        | _ => a.mobile
      let right ← b.mobile
      runtimeBinary code a b left right
    else
      let type ← commonTerm a b
      runtimeBinary code a b type type

def unary (code : UnaryCode) (term : Term context) : Except StaticError (Term context) :=
  match term with
  | .number value => do
      let operation ← match code with
        | .neg => .ok Literal.Unary.neg
        | .bitnot => .ok Literal.Unary.bitnot
        | .not => .error StaticError.rejected
      let result ← (operation.eval value.value).mapError StaticError.literal
      return .number ⟨result, none⟩
  | .string _ => .error .rejected
  | .runtime type expression =>
      if !type.scalarSupported then .error .unsupported else
      match checkUnary code type with
      | none => .error .rejected
      | some operation => .ok (.runtime type (.unary operation expression))

/-- Both arms become mobile before selecting the conditional's common type;
this is deliberately stricter than checking each literal against a proposed
result type. The condition's value is not consulted during elaboration. -/
def conditional (condition yes no : Term context) : Except StaticError (Term context) := do
  let test ← materialize .implicit condition .bool
  let left ← yes.mobile
  let right ← no.mobile
  let some type := common left right | throw .rejected
  let a ← materialize .implicit yes type
  let b ← materialize .implicit no type
  return .runtime type (.ite test a b)

def wrapTerm (identity : Nat) (base : Elementary) (term : Term context) : Except StaticError (Term context) := do
  let arg ← materialize .implicit term base.source
  return .runtime (.valueType identity base) (.wrap identity base arg)

def unwrapTerm (identity : Nat) (base : Elementary) (term : Term context) : Except StaticError (Term context) := do
  let arg ← materialize .implicit term (.valueType identity base)
  return .runtime base.source (.unwrap identity base arg)

def numeric (spelling : String) (unit : Lexical.Unit) : Except StaticError (Term context) := do
  match ← (Lexical.number spelling unit).mapError StaticError.lexical with
  | .rational value => return .number value
  | .address value => return .runtime (.address false) (.literal value)

def named (context : Context) (name : String) : Except StaticError (Term context) :=
  match found : context name with
  | none => .error (.unknownName name)
  | some type =>
      if type.scalarSupported then .ok (.runtime type (.read ⟨name, found⟩)) else .error .unsupported

/-- Tree traversal is eager at checking time, including both conditional arms
and both logical operands. Evaluation is lazy only after this function succeeds. -/
def infer (context : Context) : Source → Except StaticError (Term context)
  | .name name => named context name
  | .number spelling unit => numeric spelling unit
  | .string pieces => ((stringPieces pieces).mapError StaticError.lexical).map Term.string
  | .bool value => .ok (.runtime .bool (.literal value))
  | .unary code arg => do unary code (← infer context arg)
  | .binary code left right => do binary code (← infer context left) (← infer context right)
  | .cast kind type arg => do return .runtime type (← materialize (.explicit kind) (← infer context arg) type)
  | .ite test yes no => do conditional (← infer context test) (← infer context yes) (← infer context no)
  | .wrap identity base arg => do wrapTerm identity base (← infer context arg)
  | .unwrap identity base arg => do unwrapTerm identity base (← infer context arg)

def check (context : Context) (source : Source) (expected : SType) : Except StaticError (SourceExpr context expected) := do
  materialize .implicit (← infer context source) expected

end Solidity.Frontend.Inference
