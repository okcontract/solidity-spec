/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Scalar
import Contract.Interaction.World

/-! Resolved source types retain information erased by machine scalars. Nominal
identities, inheritance and payable-contract facts come from resolved declarations;
construction of that declaration registry is a caller responsibility. -/
namespace Solidity.Static
open Core

inductive Mutability where
  | pure | view | nonpayable | payable
  deriving DecidableEq, Repr

inductive Visibility where
  | internal | external
  deriving DecidableEq, Repr

inductive Location where
  | storage | memory | calldata
  deriving DecidableEq, Repr

inductive Elementary where
  | scalar : Core.Ty → Elementary
  | payableAddress
  deriving DecidableEq, Repr

def Elementary.core : Elementary → Core.Ty
  | .scalar t => t | .payableAddress => .address

mutual
inductive SType where
  | uint (width : Width)
  | sint (width : Width)
  | fixedBytes (width : Width)
  | bool
  | address (payable : Bool)
  | enumType (identity : Nat) (membersMinusOne : Fin 256)
  | valueType (identity : Nat) (underlying : Elementary)
  | contract (identity : Nat) (payable : Bool) (baseIdentities : List Nat)
  | function (visibility : Visibility) (mutability : Mutability) (parameters returns : Types)
  | fixedPoint (signed : Bool) (width : Width) (decimals : Fin 81)
  | array (element : SType) (length : Option Nat) (location : Location) (pointer : Bool)
  | bytes (location : Location) (pointer : Bool)
  | string (location : Location) (pointer : Bool)
  | structType (identity : Nat) (location : Location) (pointer : Bool)
  | mapping (key value : SType)
  | tuple (components : Types)
  | metaType (type : SType)
  | superType (identity : Nat)
  | omitted
  deriving DecidableEq, Repr

inductive Types where
  | nil
  | cons : SType → Types → Types
  deriving DecidableEq, Repr
end

def Types.ofList : List SType → Types
  | [] => .nil | first :: rest => .cons first (ofList rest)


/-- Internal functions carry abstract handles, not declaration identities. A
representation proof relates handles to the chosen artifact and may map
compiler-equivalent declarations to one handle; injectivity is NOT assumed.
This matters for internal-function equality under optimizer merging. `none` is
uninitialized; invoking it must panic with code 0x51 in the call semantics. -/
abbrev FunctionValue : Visibility → Type
  | .internal => Option Nat
  | .external => BitVec 160 × BitVec 32

inductive Region where
  | storage (owner : BitVec 160)
  | transient (owner : BitVec 160)
  | memory (invocation : Nat)
  | calldata (invocation : Nat)
  deriving DecidableEq, Repr

/-- An array-derived storage reference remembers the length whose removal
would leave it dangling. The bytes flag distinguishes short/long byte headers
from ordinary dynamic-array lengths. No freshness assumption hides aliases. -/
structure ReferenceGuard where
  slot : BitVec 256
  index : Nat
  bytes : Bool := false
  generation : Nat := 0
  layoutGeneration : Option Nat := none
  /-- A raw/world replacement can destroy lifetime history without leaving a
  distinguishable current header. Such references require revalidation. -/
  historyEpoch : Nat := 0
  deriving DecidableEq, Repr

/-- Physical references are values, not copied aggregate contents. Storage
addresses use word arithmetic; memory/calldata extents use natural arithmetic
and are checked before access. Calldata slices retain their selected length. -/
structure Reference where
  region : Region
  address : BitVec 256
  byte : Fin 32 := 0
  byteCell : Bool := false
  viewLength : Option Nat := none
  /-- A calldata slice of dynamically encoded elements keeps offsets relative
  to the original element sequence, rather than its shifted first head. -/
  relativeBase : Option (BitVec 256) := none
  /-- Captured memory pointer cell for a reference-valued lvalue. The target
  address remains the data reference; assignment rebinds this cell. -/
  bindingCell : Option (BitVec 256) := none
  guards : List ReferenceGuard := []
  deriving DecidableEq, Repr

/-- Scalars retain their existing values. Aggregate values are physical
references interpreted by the fallible store; unsupported meta/fixed-point
execution still has no fabricated value. -/
abbrev SType.Value : SType → Type
  | .uint w | .sint w | .fixedBytes w => BitVec w.bits
  | .bool => Bool
  | .address _ | .contract _ _ _ => BitVec 160
  | .enumType _ members => Fin (members.val + 1)
  | .valueType _ base => base.core.Value
  | .function visibility _ _ _ => FunctionValue visibility
  | .array _ _ _ _ | .bytes _ _ | .string _ _ | .structType _ _ _ |
    .mapping _ _ => Reference
  | _ => Empty

def SType.ofCore : Core.Ty → SType
  | .uint w => .uint w | .sint w => .sint w | .fixedBytes w => .fixedBytes w
  | .bool => .bool | .address => .address false

def Elementary.source : Elementary → SType
  | .scalar t => SType.ofCore t | .payableAddress => .address true

/-- Source function conversion has invariant argument/result types and the
specified mutability weakening; it is not parameter/result variance. -/
def Mutability.Allows (source target : Mutability) : Prop :=
  source = target ∨ source = .pure ∧ (target = .view ∨ target = .nonpayable) ∨
  source = .view ∧ target = .nonpayable ∨ source = .payable ∧ target = .nonpayable

instance (source target : Mutability) : Decidable (source.Allows target) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def Mutability.allows : Mutability → Mutability → Bool
  | .pure, .pure | .pure, .view | .pure, .nonpayable => true
  | .view, .view | .view, .nonpayable => true
  | .nonpayable, .nonpayable => true
  | .payable, .payable | .payable, .nonpayable => true
  | _, _ => false

theorem Mutability.allows_iff (a b : Mutability) : a.allows b = true ↔ a.Allows b := by
  cases a <;> cases b <;> simp [allows, Allows]

/-- Declarative scalar conversion relation, independently of the checker. The
identity case preserves nominal identity. Aggregate/location conversions use the aggregate transfer interface;
they do not receive scalar conversions here. -/
def Implicit (a b : SType) : Prop :=
  a = b ∨ match a, b with
  | .uint x, .uint y | .sint x, .sint y | .fixedBytes x, .fixedBytes y => x.val ≤ y.val
  | .address x, .address y => y = false ∨ x = true
  | .contract _ _ bases, .contract id _ _ => id ∈ bases
  | .function va ma pa ra, .function vb mb pb rb =>
      va = vb ∧ pa = pb ∧ ra = rb ∧ ma.Allows mb
  | _, _ => False

def implicit (a b : SType) : Bool :=
  if a = b then true else match a, b with
  | .uint x, .uint y | .sint x, .sint y | .fixedBytes x, .fixedBytes y => x.val ≤ y.val
  | .address x, .address y => !y || x
  | .contract _ _ bases, .contract id _ _ => bases.contains id
  | .function va ma pa ra, .function vb mb pb rb =>
      va == vb && pa == pb && ra == rb && ma.allows mb
  | _, _ => false

theorem implicit_iff (a b : SType) : implicit a b = true ↔ Implicit a b := by
  unfold implicit Implicit
  by_cases same : a = b
  · simp [same]
  · simp only [same, ↓reduceIte, false_or]
    cases a <;> cases b <;> simp [Mutability.allows_iff, and_assoc]

inductive CastKind where
  | ordinary | payable
  deriving DecidableEq, Repr

/-- Function type conversion rules used internally by solc do not provide a
source cast syntax. Nominal value-type identity casts remain allowed; changing
between a value type and its underlying type uses wrap/unwrap. -/
def CastTarget : SType → Prop
  | .address pay => pay = false
  | .uint _ | .sint _ | .fixedBytes _ | .bool |
    .enumType _ _ | .valueType _ _ | .contract _ _ _ | .fixedPoint _ _ _ => True
  | _ => False

instance (type : SType) : Decidable (CastTarget type) := by cases type <;> simp [CastTarget] <;> infer_instance

def ExplicitRule (a b : SType) : Prop :=
  Implicit a b ∨ match a, b with
  | .uint _, .uint _ | .sint _, .sint _ => True
  | .uint x, .sint y | .sint x, .uint y => x = y
  | .uint x, .fixedBytes y | .fixedBytes x, .uint y => x = y
  | .uint x, .address pay | .fixedBytes x, .address pay => pay = false ∧ x.val = 19
  | .address pay, .uint x | .address pay, .fixedBytes x => pay = false ∧ x.val = 19
  | .fixedBytes _, .fixedBytes _ => True
  | .address _, .address _ => True
  | .address pay, .contract _ targetPay _ => pay = true ∨ targetPay = false
  | .contract _ pay _, .address targetPay => pay = true ∨ targetPay = false
  | .uint _, .enumType _ _ | .sint _, .enumType _ _ | .enumType _ _, .uint _ => True
  | _, _ => False

def explicitRule (a b : SType) : Bool :=
  implicit a b || match a, b with
  | .uint _, .uint _ | .sint _, .sint _ => true
  | .uint x, .sint y | .sint x, .uint y => x == y
  | .uint x, .fixedBytes y | .fixedBytes x, .uint y => x == y
  | .uint x, .address pay | .fixedBytes x, .address pay => !pay && x.val == 19
  | .address pay, .uint x | .address pay, .fixedBytes x => !pay && x.val == 19
  | .fixedBytes _, .fixedBytes _ => true
  | .address _, .address _ => true
  | .address pay, .contract _ targetPay _ => pay || !targetPay
  | .contract _ pay _, .address targetPay => pay || !targetPay
  | .uint _, .enumType _ _ | .sint _, .enumType _ _ | .enumType _ _, .uint _ => true
  | _, _ => false

theorem explicitRule_iff (a b : SType) : explicitRule a b = true ↔ ExplicitRule a b := by
  unfold explicitRule ExplicitRule
  simp only [Bool.or_eq_true, implicit_iff]
  cases a <;> cases b <;> simp

/-- Explicit surface conversion, including the special payable(...) syntax.
Literal zero is handled by the literal judgment before runtime typing. -/
def SourceCast (kind : CastKind) (a b : SType) : Prop :=
  match kind with
  | .ordinary => CastTarget b ∧ ExplicitRule a b
  | .payable => b = .address true ∧ match a with
    | .address _ => True
    | .contract _ pay _ => pay = true
    | _ => False

def castTarget : SType → Bool
  | .address pay => !pay
  | .uint _ | .sint _ | .fixedBytes _ | .bool | .enumType _ _ |
    .valueType _ _ | .contract _ _ _ | .fixedPoint _ _ _ => true
  | _ => false

theorem castTarget_iff (type : SType) : castTarget type = true ↔ CastTarget type := by
  cases type <;> simp [castTarget, CastTarget]

def sourceCast (kind : CastKind) (a b : SType) : Bool :=
  match kind with
  | .ordinary => castTarget b && explicitRule a b
  | .payable => (b == .address true) && match a with
    | .address _ => true
    | .contract _ pay _ => pay
    | _ => false

theorem sourceCast_iff (kind : CastKind) (a b : SType) : sourceCast kind a b = true ↔ SourceCast kind a b := by
  cases kind with
  | ordinary => simp [sourceCast, SourceCast, castTarget_iff, explicitRule_iff]
  | payable => cases a <;> simp [sourceCast, SourceCast]

/-- Pure static descriptors such as arrays/fixedpoint are recognized separately
from scalar execution support, never reclassified as Solidity runtime failures. -/
def SType.scalarSupported : SType → Bool
  | .uint _ | .sint _ | .fixedBytes _ | .bool | .address _ |
    .enumType _ _ | .valueType _ _ | .contract _ _ _ | .function _ _ _ _ => true
  | _ => false

end Solidity.Static
