/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Environments
import Solidity.Core.Execution.ReadinessLaws

/-! The structural domain of the first admitted-state safety theorem. These
predicates exclude representation families, never duplicate source type
checking. All operation permissions come from the existing Admission equations.
Expressions may contain eager heap writes and aliased reads in either order.
Calls may recurse and widen function mutability; no termination premise occurs.
Lexical declarations are single initialized/defaulted prefix cells in blocks.
-/
namespace Solidity.Execution.Safety.Profile
open Static Aggregates

def scopesEnvironment (scopes : List (List Binder)) : Environment :=
  scopes.map fun scope => scope.map fun binder => (binder.id,binder.type)

def CheckedExpression (registry : Registry) (environment : Environment) (expression : Expr EmptyKey) : Prop :=
  ∃ fuel incoming after, Environment.Equivalent (scopesEnvironment incoming.scopes) environment ∧
    Admission.checkExpression registry fuel incoming expression = .ok after

def CheckedStatement (registry : Registry) (environment : Environment) (returns : List Binder)
    (loops : Nat) (statement : Stmt EmptyKey) : Prop :=
  ∃ fuel incoming unchecked after, Environment.Equivalent (scopesEnvironment incoming.scopes) environment ∧
    Admission.checkStatement registry fuel incoming returns loops unchecked statement = .ok after

def wordArray (type : SType) : Prop := ∃ pointer, type = WordArena.arrayType pointer

def PhysicalWord (place : Place) : Prop :=
  place.type = .uint 31 ∧ ∃ region address,
    (∃ owner, region = .storage owner ∨ region = .transient owner) ∧
    place.reference = {region,address}

mutual
inductive Expression (program : Program EmptyKey) : Expr EmptyKey → Prop where
  | literal (supported : value.type.scalarSupported = true)
      (closed : ScalarProgress.ClosedFunction program value) : Expression program (.literal value)
  | local (supported : Supported type) : Expression program (.local localId type)
  | read : Target program target → Expression program (.read target)
  | arithmetic : Expression program expression → Expression program (.arithmetic mode expression)
  | cast (source : Expression program expression) (scalarSource : expression.type.scalarSupported = true)
      (scalarTarget : type.scalarSupported = true) : Expression program (.cast mode type expression)
  | unary (source : Expression program expression) (scalar : expression.type.scalarSupported = true) :
      Expression program (.unary code expression)
  | binary (left : Expression program a) (right : Expression program b)
      (leftScalar : a.type.scalarSupported = true) (rightScalar : b.type.scalarSupported = true)
      (resultScalar : type.scalarSupported = true) : Expression program (.binary code type a b)
  | conditional : Expression program test → Expression program yes → Expression program no →
      Expression program (.conditional test yes no)
  | tuple : Expressions program values → Expression program (.tuple values)
  | assign : Target program target → Expression program value → Expression program (.assign target value)
  | compound (targetForm : Target program target) (valueForm : Expression program value)
      (scalarTarget : target.type.scalarSupported = true) (scalarValue : value.type.scalarSupported = true) :
      Expression program (.compound code target value)
  | update (targetForm : Target program target) (scalar : target.type.scalarSupported = true)
      (nondelete : code ≠ .delete) : Expression program (.update code target)
  | call (calleeForm : Expression program callee) (argumentsForm : Expressions program arguments)
      (parameters : ∀ type ∈ typesList signature.parameters, Supported type)
      (returns : ∀ type ∈ typesList signature.returns, Supported type) :
      Expression program (.call signature callee arguments)
  | namedCall (calleeForm : Expression program callee) (argumentsForm : Expressions program arguments)
      (parameters : ∀ type ∈ typesList signature.parameters, Supported type)
      (returns : ∀ type ∈ typesList signature.returns, Supported type) :
      Expression program (.namedCall signature callee arguments order)
  | assert_ : Expression program condition → Expression program (.assert_ condition)
  | require_ : Expression program condition → Expression program (.require_ .empty condition [])
  | revertWith : Expression program (.revertWith .empty [])
  | newArray (countForm : Expression program count) : Expression program (.newArray (.uint 31) count)
  | length (sourceForm : Expression program source) (array : wordArray source.type) :
      Expression program (.length source)
  | index (sourceForm : Expression program source) (array : wordArray source.type)
      (indexForm : Expression program index) : Expression program (.index (.uint 31) source index)

inductive Expressions (program : Program EmptyKey) : List (Expr EmptyKey) → Prop where
  | nil : Expressions program []
  | cons : Expression program value → Expressions program values → Expressions program (value :: values)

inductive Target (program : Program EmptyKey) : LValue EmptyKey → Prop where
  | local (supported : Supported type) : Target program (.local localId type)
  | heap (physical : PhysicalWord place) : Target program (.heap place)
  | index (sourceForm : Expression program source) (array : wordArray source.type)
      (indexForm : Expression program index) : Target program (.index (.uint 31) source index)
end

inductive Declaration (program : Program EmptyKey) : Stmt EmptyKey → Prop where
  | default (supported : Supported binder.type) : Declaration program (.declare [some binder] none)
  | value (supported : Supported binder.type) (source : Expression program value) :
      Declaration program (.declare [some binder] (some value))

mutual
inductive Statement (program : Program EmptyKey) : Stmt EmptyKey → Prop where
  | skip : Statement program .skip
  | expr : Expression program value → Statement program (.expr value)
  | seq : Statement program first → Statement program rest → Statement program (.seq first rest)
  | block : Body program body → Statement program (.block body)
  | if_ : Expression program test → Statement program yes → Statement program no →
      Statement program (.if_ test yes no)
  | while_ : Expression program test → Statement program body → Statement program (.while_ test body)
  | loop : Expression program test → Statement program body → Post program post →
      Statement program (.loop test body post)
  | doWhile : Statement program body → Expression program test → Statement program (.doWhile body test)
  | for_ : Initializer program init → (∀ value ∈ test, Expression program value) →
      Post program post → Statement program body → Statement program (.for_ init test post body)
  | break_ : Statement program .break_
  | continue_ : Statement program .continue_
  | return_ : (∀ expression ∈ value, Expression program expression) → Statement program (.return_ value)
  | arithmetic : Statement program body → Statement program (.arithmetic mode body)
  | revert : Statement program (.revert bytes)

inductive Body (program : Program EmptyKey) : Stmt EmptyKey → Prop where
  | statement : Statement program statement → Body program statement
  | declaration : Declaration program declaration → Body program rest → Body program (.seq declaration rest)

inductive Initializer (program : Program EmptyKey) : Stmt EmptyKey → Prop where
  | statement : Statement program statement → Initializer program statement
  | declaration : Declaration program declaration → Initializer program declaration

/-- The source for-loop post component is an optional expression. General
normalized statement posts retain their operational definition outside this
first safety profile. -/
inductive Post (program : Program EmptyKey) : Stmt EmptyKey → Prop where
  | skip : Post program .skip
  | expr : Expression program expression → Post program (.expr expression)
end

structure ClosedProgram (registry : Registry) (program : Program EmptyKey) : Prop where
  valid : program.valid = true
  admitted : ∃ fuel, Admission.checkProgram registry fuel program = .ok ()
  bodies : ∀ handle definition, program.lookup handle = .ok definition → Body program definition.body
  parameters : ∀ handle definition, program.lookup handle = .ok definition →
    ∀ binder ∈ definition.parameters, Supported binder.type
  returns : ∀ handle definition, program.lookup handle = .ok definition →
    ∀ binder ∈ definition.returns, Supported binder.type

theorem scopes_ofLocals (locals : Execution.Locals) :
    scopesEnvironment (Admission.Context.ofLocals locals).scopes = Safety.Locals.environment locals := by
  simp [scopesEnvironment,Admission.Context.ofLocals,Safety.Locals.environment,
    Safety.Scope.environment,List.map_map,Function.comp_def]

/-- The profile does not replace the public admission gate. Its initial static
evidence is extracted from that gate's actual successful equation. -/
theorem checkedExpression_of_admission
    (admitted : Admission.admitExpression registry fuel locals expression = .ok ()) :
    CheckedExpression registry (Safety.Locals.environment locals) expression := by
  unfold Admission.admitExpression at admitted
  cases checked : Admission.checkExpression registry fuel (Admission.Context.ofLocals locals) expression with
  | error failure => simp [checked,Bind.bind,Except.bind] at admitted
  | ok after => exact ⟨fuel,Admission.Context.ofLocals locals,after,.of_eq (scopes_ofLocals locals),checked⟩

end Solidity.Execution.Safety.Profile
