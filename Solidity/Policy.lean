/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Target

/-! Fixed compiler-compatibility policies for the pinned IR release. Legacy
code generation is outside this compatibility profile: implicit aggregate
copies can precede later argument effects there. Operator,
conversion and source-location permissions remain in their existing judgments.
These names expose ownership; no runtime policy argument selects alternatives.
`references/policies.json` records provenance, consumers and reproduction cases.
-/
namespace Solidity.Policy.Solc0836

abbrev referenceCompiler : String := Target.referenceCompilerVersion

/-- Parent tuple stores use the pinned IR helper's reverse component order.
This does not select the order in which child expressions are evaluated. -/
abbrev tupleCommit (writes : List α) : List α := writes.reverse

theorem tupleCommit_eq_reverse (writes : List α) : tupleCommit writes = writes.reverse := rfl

/-- Phase descriptors document the existing machine transitions. They are not
an alternate evaluator, a configurable plan or a constructor implementation. -/
inductive ConstructionPhase where
  | allocateRoot
  | selectEvaluateConvertStoreElement
  | evaluateAllRawArguments
  | convertStoreMemberInDeclarationOrder
  deriving DecidableEq, Repr

abbrev inlineArrayPhases : List ConstructionPhase :=
  [.allocateRoot,.selectEvaluateConvertStoreElement]
abbrev structConstructorPhases : List ConstructionPhase :=
  [.evaluateAllRawArguments,.allocateRoot,.convertStoreMemberInDeclarationOrder]

theorem inlineArray_root_first : inlineArrayPhases.head? = some .allocateRoot := rfl
theorem structConstructor_arguments_first : structConstructorPhases.head? = some .evaluateAllRawArguments := rfl

/-- The normalized rational result uses a highest-set-bit index. Work guards
use bit lengths; the names stay distinct despite sharing the numeric limit. -/
abbrev rationalMaxBitIndex : Nat := 4096
abbrev rationalWorkBits : Nat := 4096
abbrev arithmeticExponentBits : Nat := 32
abbrev scientificExponentMagnitudeBits : Nat := 31
abbrev binary64SignificandBits : Nat := 53
abbrev decimalLog2Numerator : Nat := 7480317065143153
abbrev decimalLog2Denominator : Nat := 2251799813685248

/-- The parser's case-sensitive exclusions are pinned compatibility behavior.
General digit/token grammar remains owned by Frontend.Lexical. -/
abbrev numericSeparatorExclusions : List (Char × Char) :=
  [('.', '_'), ('_', '.'), ('_', 'e'), ('e', '_')]

abbrev scientificExponentRadix (first : Option Char) : Nat :=
  if first == some '0' then 8 else 10

theorem scientificExponentRadix_eq (first : Option Char) :
    scientificExponentRadix first = (if first == some '0' then 8 else 10) := rfl

end Solidity.Policy.Solc0836
