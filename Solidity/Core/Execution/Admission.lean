/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Syntax
import Solidity.Core.Aggregates.Mutation
import Solidity.Core.Aggregates.ReferenceCasts
import Solidity.Frontend.Assignment

/-! Whole-tree admission for resolved execution syntax. This checks lexical
binding, local reference readiness and source operation permissions before a
machine strategy selects operands or branches. It does not parse source, resolve
contract declarations, validate an external ABI, or certify emitted code. -/
namespace Solidity.Execution.Admission
open Static Core
open Aggregates (Result Failure)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def ensure (condition : Bool) : Aggregates.Result Unit :=
  if condition then .ok () else .error .rejected

structure Context where
  scopes : List (List Binder) := [[]]
  assigned : List LocalId := []
  unresolvedCalls : Bool := false
  orderIndependent : Bool := false
  deriving DecidableEq, Repr

def Context.find (context : Context) (id : LocalId) : Option Binder :=
  (context.scopes.flatten).find? (fun binder => binder.id == id)

def Context.enter (context : Context) : Context := {context with scopes := [] :: context.scopes}

def Context.leave (context : Context) : Context :=
  match context.scopes with
  | [] => context
  | scope :: rest => {context with scopes := rest, assigned := context.assigned.filter fun id => !(scope.map Binder.id).contains id}

def Context.mark (context : Context) (id : LocalId) : Context :=
  {context with assigned := if context.assigned.contains id then context.assigned else id :: context.assigned}

def Context.relax (context : Context) : Context :=
  {context with assigned := context.scopes.flatten.map Binder.id}

def Context.meet (left right : Context) : Context :=
  {left with
    assigned := left.assigned.filter right.assigned.contains
    unresolvedCalls := left.unresolvedCalls || right.unresolvedCalls}

/-- Every child of an eager group completes before its parent continues. Its
guaranteed writes may be joined afterward, never fed to another sibling. -/
def Context.join (left right : Context) : Context :=
  {left with
    assigned := (left.assigned ++ right.assigned).eraseDups
    unresolvedCalls := left.unresolvedCalls || right.unresolvedCalls}

/-- Failure to establish readiness in an unordered child is an unsupported
defined-execution profile, not a claim that Solidity rejects the source. -/
def independent (context : Context) (check : Context → Aggregates.Result Context) :
    Aggregates.Result Context := do
  let after ← check {context with orderIndependent := true}
  return {after with orderIndependent := context.orderIndependent}

def independentChildren (context : Context) (values : List α)
    (check : Context → α → Aggregates.Result Context) : Aggregates.Result Context :=
  values.foldlM (fun accumulated value => do
    let after ← independent context (fun incoming => check incoming value)
    return accumulated.join after) context

def Context.declare (context : Context) (binder : Binder) (initialized : Bool) : Aggregates.Result Context := do
  ensure (context.find binder.id).isNone
  let scope :: rest := context.scopes | throw (.invalidContext "missing admission scope")
  let next := {context with scopes := (binder :: scope) :: rest}
  return if initialized then next.mark binder.id else next

def Context.local (context : Context) (id : LocalId) (type : SType) (read : Bool) : Aggregates.Result Unit := do
  let some binder := context.find id | throw .rejected
  ensure (binder.type == type)
  if read && !context.assigned.contains id then
    if context.orderIndependent then
      throw (.unsupported "reference readiness is not established independently of operand order")
    else if context.unresolvedCalls then
      throw (.unsupported "reference readiness requires a callee reachability summary")
    else throw .rejected

def checkType (registry : Registry) (fuel : Nat) (type : SType) : Aggregates.Result Unit :=
  Aggregates.eligibleType registry fuel type

def checkTypes (registry : Registry) (fuel : Nat) (types : Types) : Aggregates.Result Unit :=
  (typesList types).forM fun type => checkType registry fuel type

def checkSignature (registry : Registry) (fuel : Nat) (signature : FunctionSignature) : Aggregates.Result Unit := do
  ensure (signature.mutability != .payable)
  checkTypes registry fuel signature.parameters
  checkTypes registry fuel signature.returns

def referenceUnset : SType → Bool
  | .mapping _ _ => true
  | .array _ _ .storage _ | .bytes .storage _ | .string .storage _ | .structType _ .storage _ |
    .array _ _ .calldata _ | .bytes .calldata _ | .string .calldata _ | .structType _ .calldata _ => true
  | _ => false

def unsignedIndex : SType → Bool
  | .uint _ => true
  | _ => false

def fixedPoint : SType → Bool
  | .fixedPoint _ _ _ => true
  | _ => false

def checkedBinaryType (code : BinaryCode) (left right : SType) : Aggregates.Result SType :=
  match Static.checkBinary code left right with
  | some ⟨result, _⟩ => return result
  | none =>
      if fixedPoint left || fixedPoint right then .error (.unsupported "fixed-point expression execution")
      else .error .rejected

def scalarBinaryType (code : BinaryCode) (left right : SType) : Aggregates.Result SType :=
  if code.asymmetric then checkedBinaryType code left right else
    match Static.common left right with
    | some type => checkedBinaryType code type type
    | none => if fixedPoint left || fixedPoint right then .error (.unsupported "fixed-point expression execution")
        else .error .rejected

def localTarget : LValue Key → Bool
  | .local _ _ => true
  | _ => false

def markTarget (context : Context) : LValue Key → Context
  | .local id _ => context.mark id
  | _ => context

def transfer (registry : Registry) (fuel : Nat) (localBinding : Bool) (source target : SType) : Aggregates.Result Unit := do
  let _ ← Aggregates.planTransfer registry fuel localBinding source target
  return ()

def tupleComponents : SType → Option Types
  | .tuple components => some components
  | _ => none

mutual
/-- An implicit grouping conversion happens after the complete raw operand has
evaluated. Tuples stay `Datum` groups; no `SType.tuple.Value` is instantiated. -/
def groupTransfer (registry : Registry) : Nat → SType → SType → Aggregates.Result Unit
  | 0, _, _ => .error .exhausted
  | fuel+1, source, target =>
      match tupleComponents source, tupleComponents target with
      | some sources, some targets => groupTransfers registry fuel sources targets
      | none, none => transfer registry (fuel+1) true source target
      | _, _ => .error .rejected

def groupTransfers (registry : Registry) : Nat → Types → Types → Aggregates.Result Unit
  | _, .nil, .nil => .ok ()
  | 0, _, _ => .error .exhausted
  | fuel+1, .cons source sources, .cons target targets => do
      groupTransfer registry fuel source target
      groupTransfers registry fuel sources targets
  | _, _, _ => .error .rejected
end

mutual
inductive GroupTransferAllowed : SType → SType → Prop where
  | leaf (sourceAtom : tupleComponents source = none) (targetAtom : tupleComponents target = none)
      (permission : Aggregates.TransferRule true source target kind) : GroupTransferAllowed source target
  | tuple (sourceGroup : tupleComponents source = some sources) (targetGroup : tupleComponents target = some targets)
      (members : GroupTransfersAllowed sources targets) : GroupTransferAllowed source target
inductive GroupTransfersAllowed : Types → Types → Prop where
  | nil : GroupTransfersAllowed .nil .nil
  | cons : GroupTransferAllowed source target → GroupTransfersAllowed sources targets →
      GroupTransfersAllowed (.cons source sources) (.cons target targets)
end

mutual
theorem groupTransfer_sound (checked : groupTransfer registry fuel source target = .ok ()) :
    GroupTransferAllowed source target := by
  cases fuel with
  | zero => simp [groupTransfer] at checked
  | succ fuel =>
      cases sources : tupleComponents source with
      | none =>
          cases targets : tupleComponents target with
          | some components => simp [groupTransfer, sources, targets] at checked
          | none =>
              simp only [groupTransfer, sources, targets, transfer] at checked
              cases planned : Aggregates.planTransfer registry (fuel+1) true source target with
              | error failure => simp [planned] at checked
              | ok kind => exact .leaf sources targets (Aggregates.planTransfer_rule planned)
      | some components =>
          cases targets : tupleComponents target with
          | none => simp [groupTransfer, sources, targets] at checked
          | some members =>
              exact .tuple sources targets (groupTransfers_sound (by simpa only [groupTransfer, sources, targets] using checked))

theorem groupTransfers_sound (checked : groupTransfers registry fuel sources targets = .ok ()) :
    GroupTransfersAllowed sources targets := by
  cases sources with
  | nil =>
      cases targets with
      | nil => exact .nil
      | cons target targets => cases fuel <;> simp [groupTransfers] at checked
  | cons source sources =>
      cases fuel with
      | zero => simp [groupTransfers] at checked
      | succ fuel =>
          cases targets with
          | nil => simp [groupTransfers] at checked
          | cons target targets =>
              simp only [groupTransfers] at checked
              cases first : groupTransfer registry fuel source target with
              | error failure => simp [first] at checked
              | ok token =>
                  cases token
                  simp only [first, Bind.bind, Except.bind] at checked
                  exact .cons (groupTransfer_sound first) (groupTransfers_sound checked)
end

/-- Runtime children already carry their resolved scalar/literal types. Native
mobile reference types retain their location while gaining a pointer marker;
the containing memory array relocates the selected common type afterward. -/
def mobileElement (type : SType) : SType :=
  match Aggregates.referenceLocation type with
  | some location => Aggregates.atLocation type location true
  | none => type

def commonElement (left right : SType) : Option SType :=
  let mobileLeft := mobileElement left
  if (Aggregates.selectTransfer true right mobileLeft).isSome then some mobileLeft else
    let mobileRight := mobileElement right
    if (Aggregates.selectTransfer true left mobileRight).isSome then some mobileRight else none

/-- Match the first mobile element and native left-to-right common-type fold.
Merely being convertible to a wider supplied annotation is insufficient. -/
def inlineElementType : List SType → Option SType
  | [] => none
  | first :: rest => (rest.foldlM commonElement (mobileElement first)).map
      (fun type => Aggregates.atLocation type .memory false)

def ElementImplicit (source target : SType) : Prop :=
  ∃ kind, Aggregates.TransferRule true source target kind

theorem elementImplicit_iff (source target : SType) :
    (Aggregates.selectTransfer true source target).isSome = true ↔ ElementImplicit source target := by
  cases selected : Aggregates.selectTransfer true source target with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, ElementImplicit, not_exists]
      intro kind allowed
      have impossible := (Aggregates.selectTransfer_iff true source target kind).mpr allowed
      simp [selected] at impossible
  | some kind =>
      constructor
      · intro _
        exact ⟨kind, (Aggregates.selectTransfer_iff true source target kind).mp selected⟩
      · intro _; rfl

def CommonElement (left right result : SType) : Prop :=
  (ElementImplicit right (mobileElement left) ∧ result = mobileElement left) ∨
    (¬ ElementImplicit right (mobileElement left) ∧ ElementImplicit left (mobileElement right) ∧
      result = mobileElement right)

theorem commonElement_iff (left right result : SType) :
    commonElement left right = some result ↔ CommonElement left right result := by
  unfold commonElement CommonElement
  dsimp only
  split
  · rename_i first
    have allowed := (elementImplicit_iff right (mobileElement left)).mp first
    simp [allowed, eq_comm]
  · rename_i first
    have denied : ¬ ElementImplicit right (mobileElement left) :=
      fun allowed => first ((elementImplicit_iff right (mobileElement left)).mpr allowed)
    split
    · rename_i second
      have allowed := (elementImplicit_iff left (mobileElement right)).mp second
      simp [denied, allowed, eq_comm]
    · rename_i second
      have no : ¬ ElementImplicit left (mobileElement right) :=
        fun allowed => second ((elementImplicit_iff left (mobileElement right)).mpr allowed)
      simp [denied, no]

inductive CommonElements : SType → List SType → SType → Prop where
  | nil : CommonElements type [] type
  | cons : CommonElement initial head middle → CommonElements middle rest result →
      CommonElements initial (head :: rest) result

theorem CommonElements.fold_iff (initial result : SType) (types : List SType) :
    types.foldlM commonElement initial = some result ↔ CommonElements initial types result := by
  induction types generalizing initial with
  | nil =>
      constructor
      · intro same; cases same; exact .nil
      · intro relation; cases relation; rfl
  | cons head rest ih =>
      change (do let middle ← commonElement initial head; rest.foldlM commonElement middle) = some result ↔ _
      cases selected : commonElement initial head with
      | none =>
          constructor
          · simp
          · intro relation
            cases relation with
            | cons first tail =>
                have selected' := (commonElement_iff _ _ _).mpr first
                simp [selected] at selected'
      | some middle =>
          simp only [Bind.bind, Option.bind_some]
          constructor
          · intro folded
            exact .cons ((commonElement_iff _ _ _).mp selected) ((ih middle).mp folded)
          · intro relation
            cases relation with
            | cons first tail =>
                have selected' := (commonElement_iff _ _ _).mpr first
                rw [selected] at selected'
                cases selected'
                exact (ih middle).mpr tail

def fieldType (registry : Registry) (base : SType) (index : Nat) : Aggregates.Result SType := do
  let .structType identity location _ := base | throw .rejected
  let some fields := registry.structFields identity |
    throw (.invalidContext "missing resolved field metadata in admission")
  let some (_, type) := fields[index]? | throw .rejected
  return Aggregates.atLocation type location false

def indexType (base : SType) (writable : Bool) : Aggregates.Result SType := do
  match base with
  | .array element _ location _ =>
      if writable then ensure (location != .calldata)
      return Aggregates.atLocation element location false
  | .bytes location _ =>
      if writable then ensure (location != .calldata)
      return .fixedBytes 0
  | .fixedBytes _ =>
      ensure (!writable)
      return .fixedBytes 0
  | _ => throw .rejected

def mappingType (base key : SType) : Aggregates.Result SType := do
  let .mapping expected value := base | throw .rejected
  let compatible := match expected, key with
    | .bytes _ _, .bytes _ _ | .string _ _, .string _ _ => true
    | _, _ => Static.implicit key expected
  ensure compatible
  return Aggregates.atLocation value .storage false

def pushType : SType → Aggregates.Result SType
  | .array element none .storage _ => .ok (Aggregates.atLocation element .storage false)
  | .bytes .storage _ => .ok (.fixedBytes 0)
  | _ => .error .rejected

def sourceWritable (type : SType) : Bool := Aggregates.referenceLocation type != some .calldata

def errorParameters : ErrorEncoding → Types
  | .empty => .nil
  | .string => .cons (.string .memory true) .nil
  | .custom _ parameters => parameters

def checkErrorArguments (registry : Registry) (fuel : Nat) (encoding : ErrorEncoding)
    (arguments : Exprs Key) : Aggregates.Result Unit := do
  let parameters := typesList (errorParameters encoding)
  ensure (arguments.length == parameters.length)
  checkTypes registry fuel (errorParameters encoding)
  (arguments.zip parameters).forM fun (argument, parameter) => transfer registry fuel true argument.type parameter

mutual
def checkExpression (registry : Registry) : Nat → Context → Expr Key → Aggregates.Result Context
  | 0, _, _ => .error .exhausted
  | fuel+1, context, expression => do
      match expression with
      | .literal value => checkType registry fuel value.type; return context
      | .bytesLiteral _ _ => return context
      | .local id type => context.local id type true; checkType registry fuel type; return context
      | .externalRead (type := type) _ => checkType registry fuel type; return context
      | .read target => checkLValue registry fuel context target false
      | .cast mode target value =>
          let context ← checkExpression registry fuel context value
          match mode with
          | .implicit => groupTransfer registry fuel value.type target
          | .explicit .ordinary =>
              ensure (tupleComponents target).isNone
              checkType registry fuel target
              if Aggregates.isReference value.type then
                ensure (Aggregates.ReferenceCasts.select value.type target).isSome
              else ensure (Static.allows mode value.type target)
          | .explicit .payable =>
              ensure (tupleComponents target).isNone
              checkType registry fuel target
              ensure (Static.allows mode value.type target)
          return context
      | .referenceCast target value =>
          let context ← checkExpression registry fuel context value
          checkType registry fuel target
          ensure (Aggregates.ReferenceCasts.select value.type target).isSome
          return context
      | .wrap identity base value =>
          let context ← checkExpression registry fuel context value
          ensure (registry.valueTypes identity == some base)
          ensure (value.type == base.source)
          return context
      | .unwrap identity base value =>
          let context ← checkExpression registry fuel context value
          ensure (registry.valueTypes identity == some base)
          ensure (value.type == .valueType identity base)
          return context
      | .functionAddress value | .functionSelector value =>
          let context ← checkExpression registry fuel context value
          ensure (match value.type with | .function .external _ _ _ => true | _ => false)
          return context
      | .arithmetic _ value => checkExpression registry fuel context value
      | .unary code value =>
          let context ← checkExpression registry fuel context value
          if fixedPoint value.type then
            if code == .neg then throw (.unsupported "fixed-point unary expression execution") else throw .rejected
          ensure (Static.checkUnary code value.type).isSome
          return context
      | .binary code result left right =>
          let after ← if code == .and || code == .or then do
              let leftContext ← checkExpression registry fuel context left
              let rightContext ← checkExpression registry fuel leftContext right
              pure (leftContext.meet rightContext)
            else checkExpressions registry fuel context [left, right]
          ensure ((← scalarBinaryType code left.type right.type) == result)
          return after
      | .conditional test yes no =>
          let context ← checkExpression registry fuel context test
          ensure (test.type == .bool)
          let a ← checkExpression registry fuel context yes
          let b ← checkExpression registry fuel context no
          ensure (yes.type == no.type)
          return a.meet b
      | .tuple values => checkExpressions registry fuel context values
      | .assign target value =>
          let right ← independent context (fun incoming => checkExpression registry fuel incoming value)
          let captured ← independent context (fun incoming => checkLValue registry fuel incoming target true)
          transfer registry fuel (localTarget target) value.type target.type
          return markTarget (right.join captured) target
      | .tupleAssign pattern value =>
          let right ← independent context (fun incoming => checkExpression registry fuel incoming value)
          let captured ← independent context (fun incoming => checkPattern registry fuel incoming pattern value.type)
          return right.join captured
      | .compound code target value =>
          ensure (Frontend.Inference.compoundToken code)
          let right ← independent context (fun incoming => checkExpression registry fuel incoming value)
          let captured ← independent context (fun incoming => do
            let captured ← checkLValue registry fuel incoming target true
            checkLValue registry fuel captured target false)
          ensure ((← scalarBinaryType code target.type value.type) == target.type)
          return markTarget (right.join captured) target
      | .update code target =>
          let context ← checkLValue registry fuel context target true
          match code with
          | .delete => ensure (Aggregates.Mutation.deletable target.type)
          | _ =>
              let _ ← checkLValue registry fuel context target false
              if fixedPoint target.type then throw (.unsupported "fixed-point update execution")
              ensure (Static.updateAllowed code target.type true)
          return markTarget context target
      | .call signature callee arguments =>
          checkSignature registry fuel signature
          ensure (Static.implicit callee.type signature.type)
          let context ← checkExpressions registry fuel context (callee :: arguments)
          let parameters := typesList signature.parameters
          ensure (arguments.length == parameters.length)
          (arguments.zip parameters).forM fun (argument, parameter) => transfer registry fuel true argument.type parameter
          return {context with unresolvedCalls := true}
      | .namedCall signature callee arguments order =>
          checkSignature registry fuel signature
          ensure (Static.implicit callee.type signature.type)
          let context ← checkExpressions registry fuel context (callee :: arguments)
          let ordered ← ArgumentOrder.select order arguments
          let parameters := typesList signature.parameters
          ensure (ordered.length == parameters.length)
          (ordered.zip parameters).forM fun (argument, parameter) => transfer registry fuel true argument.type parameter
          return {context with unresolvedCalls := true}
      | .assert_ condition =>
          let context ← checkExpression registry fuel context condition
          ensure (condition.type == .bool)
          return context
      | .require_ encoding condition arguments =>
          ensure (condition.type == .bool)
          let context ← checkExpressions registry fuel context (condition :: arguments)
          checkErrorArguments registry fuel encoding arguments
          return context
      | .revertWith encoding arguments =>
          let context ← checkExpressions registry fuel context arguments
          checkErrorArguments registry fuel encoding arguments
          return context
      | .newArray element count =>
          let context ← checkExpression registry fuel context count
          ensure (unsignedIndex count.type)
          checkType registry fuel (.array (Aggregates.atLocation element .memory false) none .memory true)
          return context
      | .newBytes _ count =>
          let context ← checkExpression registry fuel context count
          ensure (unsignedIndex count.type)
          return context
      | .inlineArray element values =>
          ensure (!values.isEmpty)
          let context ← checkExpressions registry fuel context values
          if values.any (fun value => fixedPoint value.type) then
            throw (.unsupported "fixed-point inline-array inference")
          let some inferred := inlineElementType (values.map Expr.type) | throw .rejected
          ensure (inferred == Aggregates.atLocation element .memory false)
          checkType registry fuel (.array inferred (some values.length) .memory true)
          values.forM fun value => transfer registry fuel true value.type (Aggregates.atLocation element .memory false)
          return context
      | .structConstructor identity arguments order =>
          checkType registry fuel (.structType identity .memory true)
          let some fields := registry.structFields identity |
            throw (.invalidContext "missing resolved constructor metadata")
          let context ← checkExpressions registry fuel context arguments
          let ordered ← ArgumentOrder.select order arguments
          ensure (ordered.length == fields.length)
          (ordered.zip fields).forM fun (argument, field) =>
            transfer registry fuel true argument.type (Aggregates.atLocation field.2 .memory false)
          return context
      | .length value =>
          let context ← checkExpression registry fuel context value
          ensure (match value.type with | .array _ _ _ _ | .bytes _ _ | .fixedBytes _ => true | _ => false)
          return context
      | .index result value index =>
          let context ← checkExpressions registry fuel context [value, index]
          ensure (unsignedIndex index.type)
          ensure ((← indexType value.type false) == result)
          return context
      | .slice value start stop =>
          let context ← checkExpressions registry fuel context (value :: (start.toList ++ stop.toList))
          ensure (start.all fun value => unsignedIndex value.type)
          ensure (stop.all fun value => unsignedIndex value.type)
          match value.type with
          | .bytes .calldata _ => pure ()
          | .array element none .calldata _ => ensure (!(← Aggregates.calldataDynamic registry fuel element))
          | _ => throw .rejected
          return context
      | .push value next =>
          let context ← checkExpressions registry fuel context [value, next]
          transfer registry fuel false next.type (← pushType value.type)
          return context
      | .pop value =>
          let context ← checkExpression registry fuel context value
          let _ ← pushType value.type
          return context

def checkExpressions (registry : Registry) : Nat → Context → Exprs Key → Aggregates.Result Context
  | 0, _, _ => .error .exhausted
  | fuel+1, context, values => independentChildren context values (checkExpression registry fuel)

def checkOptional (registry : Registry) : Nat → Context → Option (Expr Key) → Aggregates.Result Context
  | 0, _, _ => .error .exhausted
  | _+1, context, none => .ok context
  | fuel+1, context, some value => checkExpression registry fuel context value

def checkLValue (registry : Registry) : Nat → Context → LValue Key → Bool → Aggregates.Result Context
  | 0, _, _, _ => .error .exhausted
  | fuel+1, context, target, writable => do
      match target with
      | .local id type => context.local id type (!writable); checkType registry fuel type; return context
      | .heap place =>
          Aggregates.eligibleAt registry fuel place.reference.region place.type
          if writable then ensure (match place.reference.region with | .calldata _ => false | _ => true)
          return context
      | .external (type := type) _ => checkType registry fuel type; return context
      | .field result value index =>
          let context ← checkExpression registry fuel context value
          if writable then ensure (sourceWritable value.type)
          ensure ((← fieldType registry value.type index) == result)
          return context
      | .index result value index =>
          let context ← checkExpressions registry fuel context [value, index]
          ensure (unsignedIndex index.type)
          ensure ((← indexType value.type writable) == result)
          return context
      | .mapping result value key =>
          let context ← checkExpressions registry fuel context [value, key]
          ensure ((← mappingType value.type key.type) == result)
          return context
      | .pushZero result value =>
          let context ← checkExpression registry fuel context value
          ensure ((← pushType value.type) == result)
          return context

def checkPattern (registry : Registry) : Nat → Context → Pattern Key → SType → Aggregates.Result Context
  | 0, _, _, _ => .error .exhausted
  | fuel+1, context, pattern, source => do
      match pattern with
      | .hole => return context
      | .target target =>
          let context ← checkLValue registry fuel context target true
          transfer registry fuel (localTarget target) source target.type
          return markTarget context target
      | .tuple targets =>
          ensure (!targets.isEmpty)
          let .tuple components := source | throw .rejected
          let components := typesList components
          ensure (targets.length == components.length)
          independentChildren context (targets.zip components)
            (fun incoming (target, type) => checkPattern registry fuel incoming target type)
end

def constantBool : Expr Key → Option Bool
  | .literal ⟨.bool, value⟩ => some value
  | _ => none

mutual
/-- A structural terminal expression has no normal continuation under any
operand strategy. Unknown callee reachability is tracked separately and never
converted to a claim that the call returns. -/
def stops : Expr Key → Bool
  | .literal _ | .bytesLiteral _ _ | .local _ _ | .externalRead _ => false
  | .read target | .update _ target => targetStops target
  | .cast _ _ value | .referenceCast _ value | .arithmetic _ value | .unary _ value |
    .newArray _ value | .newBytes _ value | .length value | .pop value | .wrap _ _ value |
    .unwrap _ _ value | .functionAddress value | .functionSelector value => stops value
  | .binary code _ left right =>
      stops left || if code == .and then constantBool left == some true && stops right
        else if code == .or then constantBool left == some false && stops right else stops right
  | .conditional condition yes no => stops condition ||
      match constantBool condition with
      | some true => stops yes
      | some false => stops no
      | none => stops yes && stops no
  | .tuple values => anyStops values
  | .inlineArray _ values | .structConstructor _ values _ => anyStops values
  | .assign target value | .compound _ target value => targetStops target || stops value
  | .tupleAssign pattern value => patternStops pattern || stops value
  | .call _ callee arguments | .namedCall _ callee arguments _ => stops callee || anyStops arguments
  | .assert_ condition => stops condition || constantBool condition == some false
  | .require_ _ condition arguments => stops condition || anyStops arguments || constantBool condition == some false
  | .revertWith _ _ => true
  | .index _ value index | .push value index => stops value || stops index
  | .slice value start stop => stops value ||
      (match start with | none => false | some value => stops value) ||
      (match stop with | none => false | some value => stops value)

def anyStops : Exprs Key → Bool
  | [] => false
  | value :: rest => stops value || anyStops rest

def targetStops : LValue Key → Bool
  | .local _ _ | .heap _ | .external _ => false
  | .field _ value _ | .pushZero _ value => stops value
  | .index _ value index | .mapping _ value index => stops value || stops index

def patternStops : Pattern Key → Bool
  | .hole => false
  | .target target => targetStops target
  | .tuple targets => anyPatternStops targets

def anyPatternStops : List (Pattern Key) → Bool
  | [] => false
  | target :: rest => patternStops target || anyPatternStops rest
end

structure Flow where
  normal : Option Context
  breaks : List Context := []
  continues : List Context := []
  dead : Context

def Flow.next (context : Context) : Flow := ⟨some context, [], [], context⟩
def Flow.halt (context : Context) : Flow := ⟨none, [], [], context⟩

def mergeNormal : Option Context → Option Context → Option Context
  | none, other | other, none => other
  | some left, some right => some (left.meet right)

def meetContexts (contexts : List Context) : Option Context :=
  contexts.foldl (fun state context => mergeNormal state (some context)) none

def Flow.leave (flow : Flow) : Flow :=
  ⟨flow.normal.map Context.leave, flow.breaks.map Context.leave, flow.continues.map Context.leave, flow.dead.leave⟩

def checkReturns (context : Context) (returns : List Binder) : Aggregates.Result Unit :=
  returns.forM fun binder => context.local binder.id binder.type true

def resultComponents (type : SType) : List SType :=
  match type with | .tuple types => typesList types | type => [type]

def declareBinders (registry : Registry) (fuel : Nat) (context : Context)
    (binders : List (Option Binder)) (initializer : Option (Expr Key)) : Aggregates.Result Context := do
  match initializer with
  | some value =>
      let context ← checkExpression registry fuel context value
      let components := resultComponents value.type
      ensure (binders.length == components.length)
      (binders.zip components).foldlM (fun context (binder, type) => do
        match binder with
        | none => return context
        | some binder =>
            transfer registry fuel true type binder.type
            context.declare binder true) context
  | none =>
      ensure (binders.all Option.isSome)
      binders.foldlM (fun context binder => do
        let some binder := binder | throw .rejected
        checkType registry fuel binder.type
        ensure (match binder.type with | .mapping _ _ => false | _ => true)
        context.declare binder (!referenceUnset binder.type)) context

def checkStatement (registry : Registry) : Nat → Context → List Binder → Nat → Bool → Stmt Key → Aggregates.Result Flow
  | 0, _, _, _, _, _ => .error .exhausted
  | fuel+1, context, returns, loops, unchecked, statement => do
      match statement with
      | .skip => return Flow.next context
      | .expr expression =>
          let context ← checkExpression registry fuel context expression
          return if stops expression then Flow.halt context else Flow.next context
      | .seq first rest =>
          let a ← checkStatement registry fuel context returns loops unchecked first
          let b ← checkStatement registry fuel (a.normal.getD a.dead.relax) returns loops unchecked rest
          return if a.normal.isSome then
            ⟨b.normal, a.breaks ++ b.breaks, a.continues ++ b.continues, b.dead⟩
            else {a with dead := b.dead}
      | .block body =>
          return (← checkStatement registry fuel context.enter returns loops unchecked body).leave
      | .declare binders initializer => return Flow.next (← declareBinders registry fuel context binders initializer)
      | .if_ test yes no =>
          let context ← checkExpression registry fuel context test
          ensure (test.type == .bool)
          let a ← checkStatement registry fuel context returns loops unchecked yes
          let b ← checkStatement registry fuel context returns loops unchecked no
          ensure (a.dead.scopes == context.scopes && b.dead.scopes == context.scopes)
          return if stops test then Flow.halt context else
            ⟨mergeNormal a.normal b.normal, a.breaks ++ b.breaks, a.continues ++ b.continues, context⟩
      | .while_ test body =>
          let context ← checkExpression registry fuel context test
          ensure (test.type == .bool)
          let body ← checkStatement registry fuel context returns (loops+1) unchecked body
          ensure (body.dead.scopes == context.scopes)
          let normal := mergeNormal (some context) (meetContexts body.breaks)
          return if stops test then Flow.halt context else ⟨normal, [], [], context⟩
      | .loop test body post =>
          let context ← checkExpression registry fuel context test
          ensure (test.type == .bool)
          let body ← checkStatement registry fuel context returns (loops+1) unchecked body
          ensure (body.dead.scopes == context.scopes)
          let incoming := mergeNormal body.normal (meetContexts body.continues)
          let post ← checkStatement registry fuel (incoming.getD context.relax) returns (loops+1) unchecked post
          ensure (post.breaks.isEmpty && post.continues.isEmpty && post.dead.scopes == context.scopes)
          let normal := mergeNormal (some context) (meetContexts body.breaks)
          return if stops test then Flow.halt context else ⟨normal, [], [], context⟩
      | .doWhile body test =>
          let body ← checkStatement registry fuel context returns (loops+1) unchecked body
          ensure (body.dead.scopes == context.scopes)
          let incoming := mergeNormal body.normal (meetContexts body.continues)
          let tested ← checkExpression registry fuel (incoming.getD context.relax) test
          ensure (test.type == .bool)
          let normal := mergeNormal (if incoming.isSome && !stops test then some tested else none) (meetContexts body.breaks)
          return ⟨normal, [], [], context⟩
      | .for_ init test post body =>
          let initialized ← checkStatement registry fuel context.enter returns loops unchecked init
          ensure (initialized.breaks.isEmpty && initialized.continues.isEmpty)
          let current := initialized.normal.getD initialized.dead.relax
          let current ← checkOptional registry fuel current test
          ensure (test.all fun value => value.type == .bool)
          let body ← checkStatement registry fuel current returns (loops+1) unchecked body
          ensure (body.dead.scopes == current.scopes)
          let incoming := mergeNormal body.normal (meetContexts body.continues)
          let post ← checkStatement registry fuel (incoming.getD current.relax) returns (loops+1) unchecked post
          ensure (post.breaks.isEmpty && post.continues.isEmpty && post.dead.scopes == current.scopes)
          let normal := mergeNormal (if test.any stops then none else some current) (meetContexts body.breaks)
          return (⟨if initialized.normal.isSome then normal else none, [], [], current⟩ : Flow).leave
      | .break_ => ensure (0 < loops); return ⟨none, [context], [], context⟩
      | .continue_ => ensure (0 < loops); return ⟨none, [], [context], context⟩
      | .return_ none => checkReturns context returns; return Flow.halt context
      | .return_ (some value) =>
          let context ← checkExpression registry fuel context value
          let components := resultComponents value.type
          ensure (components.length == returns.length)
          (components.zip returns).forM fun (source, binder) => transfer registry fuel true source binder.type
          return Flow.halt context
      | .arithmetic mode body =>
          ensure (!(unchecked && mode == .unchecked))
          checkStatement registry fuel context returns loops (mode == .unchecked) body
      | .emit topics data =>
          ensure (topics.length ≤ 4)
          let context ← checkExpressions registry fuel context (topics ++ data)
          if (topics ++ data).any (fun value => Aggregates.isReference value.type) then
            throw (.unsupported "aggregate event ABI encoding")
          if (topics ++ data).any (fun value => fixedPoint value.type) then
            throw (.unsupported "fixed-point event ABI encoding")
          ensure ((topics ++ data).all fun value => value.type.scalarSupported)
          return Flow.next context
      | .revert _ => return Flow.halt context
      | .storeExternal (type := type) _ value =>
          let context ← checkExpression registry fuel context value
          checkType registry fuel type
          ensure (Static.implicit value.type type)
          return Flow.next context

def functionContext (registry : Registry) (fuel : Nat) (function : FunctionDefinition Key) : Aggregates.Result Context := do
  ensure function.distinctBindings
  checkSignature registry fuel function.signature
  let scopes := [function.parameters ++ function.returns]
  let assigned := function.parameters.map Binder.id ++
    (function.returns.filter fun binder => !referenceUnset binder.type).map Binder.id
  return ⟨scopes, assigned, false, false⟩

def checkFunction (registry : Registry) (fuel : Nat) (function : FunctionDefinition Key) : Aggregates.Result Unit := do
  let context ← functionContext registry fuel function
  let flow ← checkStatement registry fuel context function.returns 0 false function.body
  ensure (flow.breaks.isEmpty && flow.continues.isEmpty)
  if let some normal := flow.normal then checkReturns normal function.returns

def checkProgram (registry : Registry) (fuel : Nat) (program : Program Key) : Aggregates.Result Unit := do
  ensure program.valid
  program.functions.forM fun (_, function) => checkFunction registry fuel function

def Context.ofLocals (locals : Locals) : Context :=
  { scopes := locals.map fun scope => scope.map fun (id, cell) => ⟨id, cell.type, none⟩
    assigned := locals.flatten.filterMap fun (id, cell) => if cell.value.isSome then some id else none }

def admitExpression (registry : Registry) (fuel : Nat) (locals : Locals) (expression : Expr Key) : Aggregates.Result Unit := do
  let _ ← checkExpression registry fuel (Context.ofLocals locals) expression
  return ()

def admitStatement (registry : Registry) (fuel : Nat) (locals : Locals)
    (returns : List Binder) (statement : Stmt Key) : Aggregates.Result Unit := do
  let flow ← checkStatement registry fuel (Context.ofLocals locals) returns 0 false statement
  ensure (flow.breaks.isEmpty && flow.continues.isEmpty)
  if let some normal := flow.normal then checkReturns normal returns

/-- Independent source index permissions; fixed bytes permit reads only and
calldata element places remain immutable. -/
def IndexAllowed (base : SType) (writable : Bool) (result : SType) : Prop :=
  match base with
  | .array element _ location _ => (writable = true → location ≠ .calldata) ∧
      result = Aggregates.atLocation element location false
  | .bytes location _ => (writable = true → location ≠ .calldata) ∧ result = .fixedBytes 0
  | .fixedBytes _ => writable = false ∧ result = .fixedBytes 0
  | _ => False

theorem indexType_iff (base result : SType) (writable : Bool) :
    indexType base writable = .ok result ↔ IndexAllowed base writable result := by
  cases base with
  | array element length location pointer =>
      cases location <;> cases writable <;> simp [indexType, IndexAllowed, ensure] <;> exact eq_comm
  | bytes location pointer =>
      cases location <;> cases writable <;> simp [indexType, IndexAllowed, ensure] <;> exact eq_comm
  | fixedBytes width => cases writable <;> simp [indexType, IndexAllowed, ensure] <;> exact eq_comm
  | _ => simp [indexType, IndexAllowed]

inductive BinaryAllowed (code : BinaryCode) (left right : SType) : SType → Prop where
  | asymmetric (order : code.asymmetric = true) (operation : ScalarBinary code left right result) :
      BinaryAllowed code left right result
  | common (order : code.asymmetric = false) (type : SType) (selected : Static.Common left right type)
      (operation : ScalarBinary code type type result) : BinaryAllowed code left right result

theorem scalarBinaryType_complete (allowed : BinaryAllowed code left right result) :
    scalarBinaryType code left right = .ok result := by
  cases allowed with
  | asymmetric order operation =>
      simp [scalarBinaryType, checkedBinaryType, order, checkBinary_complete operation]
  | common order type selected operation =>
      simp [scalarBinaryType, checkedBinaryType, order, (Static.common_iff _ _ _).mpr selected,
        checkBinary_complete operation]

theorem checkedBinaryType_sound (checked : checkedBinaryType code left right = .ok result) :
    Nonempty (ScalarBinary code left right result) := by
  unfold checkedBinaryType at checked
  cases operation : Static.checkBinary code left right with
  | none =>
      rw [operation] at checked
      by_cases unavailable : (fixedPoint left || fixedPoint right) = true <;> simp [unavailable] at checked
  | some typed =>
      rcases typed with ⟨type, proof⟩
      rw [operation] at checked
      cases checked
      exact ⟨proof⟩

theorem scalarBinaryType_sound (checked : scalarBinaryType code left right = .ok result) :
    BinaryAllowed code left right result := by
  unfold scalarBinaryType at checked
  cases order : code.asymmetric with
  | true =>
      simp only [order, ↓reduceIte] at checked
      rcases checkedBinaryType_sound checked with ⟨operation⟩
      exact .asymmetric order operation
  | false =>
      simp only [order, Bool.false_eq_true, ↓reduceIte] at checked
      cases selected : Static.common left right with
      | none =>
          by_cases unavailable : (fixedPoint left || fixedPoint right) = true <;> simp [selected, unavailable] at checked
      | some type =>
          simp only [selected] at checked
          rcases checkedBinaryType_sound checked with ⟨operation⟩
          exact .common order type ((Static.common_iff _ _ _).mp selected) operation

theorem checkExpression_exhausted :
    checkExpression registry 0 context expression = .error .exhausted := rfl

theorem checkStatement_exhausted :
    checkStatement registry 0 context returns loops unchecked statement = .error .exhausted := rfl

end Solidity.Execution.Admission
