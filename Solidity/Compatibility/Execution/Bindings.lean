/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Primitives
import Solidity.Core.Bindings

/-! Stable resolved IDs for the old intrinsically typed environments. Adding
a local does not rename an existing cell. Even IDs hold legacy vars;
odd IDs are available for the new machine's named return bindings. -/
namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def localIndex : {types : List Core.Ty} → Core.Var types type → Nat
  | _ :: rest, .here => rest.length
  | _ :: _, .there var => localIndex var

def localId (var : Core.Var types type) : LocalId := 2 * localIndex var

theorem localIndex_lt (var : Core.Var types type) : localIndex var < types.length := by
  induction var with
  | here => simp [localIndex]
  | there var ih => simp only [localIndex, List.length_cons]; omega

theorem localId_lt (var : Core.Var types type) : localId var < 2 * types.length := by
  exact Nat.mul_lt_mul_of_pos_left (localIndex_lt var) (by decide)

@[simp] theorem localId_there (var : Core.Var types type) :
    localId (Core.Var.there (other := other) var) = localId var := rfl

def localScope : {types : List Core.Ty} → Core.Env types → Scope
  | type :: types, .cons value rest =>
      (2 * types.length, ⟨SType.ofCore type, some (scalarValue type value)⟩) :: localScope rest
  | [], .nil => []

def localEnv (environment : Core.Env types) : Locals := [localScope environment]

theorem localScope_outside (environment : Core.Env types) (id : LocalId)
    (outside : 2 * types.length ≤ id) : Scope.find (localScope environment) id = none := by
  induction environment with
  | nil => rfl
  | @cons types type value rest ih =>
      have different : 2 * types.length ≠ id := by simp only [List.length_cons] at outside; omega
      simp only [localScope, Scope.find, different, ↓reduceIte]
      exact ih (by simp only [List.length_cons] at outside; omega)

theorem localScope_odd (environment : Core.Env types) (index : Nat) :
    Scope.find (localScope environment) (2 * index + 1) = none := by
  induction environment with
  | nil => rfl
  | @cons types type value rest ih =>
      have different : 2 * types.length ≠ 2 * index + 1 := by omega
      simpa only [localScope, Scope.find, different, ↓reduceIte] using ih

theorem localScope_find (environment : Core.Env types) (var : Core.Var types type) :
    Scope.find (localScope environment) (localId var) =
      some ⟨SType.ofCore type, some (scalarValue type (environment.get var))⟩ := by
  induction var with
  | here => cases environment; simp [localScope, localId, localIndex, Scope.find, Core.Env.get]
  | @there types type other var ih =>
      cases environment with
      | cons head rest =>
          have different : 2 * types.length ≠ localId var := Nat.ne_of_gt (localId_lt var)
          simpa only [localScope, localId_there, Scope.find, different, ↓reduceIte, Core.Env.get] using ih rest

theorem localEnv_find (environment : Core.Env types) (var : Core.Var types type) :
    (localEnv environment).find (localId var) =
      some ⟨SType.ofCore type, some (scalarValue type (environment.get var))⟩ := by
  simp only [localEnv, Locals.find, localScope_find, Option.orElse_some]

theorem localEnv_read (environment : Core.Env types) (var : Core.Var types type) :
    (localEnv environment).read (localId var) (SType.ofCore type) =
      .ok ⟨SType.ofCore type, scalarValue type (environment.get var)⟩ := by
  simp [Locals.read, localEnv_find]

theorem localScope_replace (environment : Core.Env types) (var : Core.Var types type) (value : type.Value) :
    Scope.replace (localScope environment) (localId var)
      ⟨SType.ofCore type, some (scalarValue type value)⟩ = localScope (environment.set var value) := by
  induction var with
  | here => cases environment; simp [localScope, localId, localIndex, Scope.replace, Core.Env.set]
  | @there types type other var ih =>
      cases environment with
      | cons head rest =>
          have different : 2 * types.length ≠ localId var := Nat.ne_of_gt (localId_lt var)
          simpa only [localScope, localId_there, Scope.replace, different, ↓reduceIte, Core.Env.set] using
            congrArg (List.cons (2 * types.length,
              (⟨SType.ofCore other, some (scalarValue other head)⟩ : LocalCell))) (ih rest value)

theorem localEnv_write (environment : Core.Env types) (var : Core.Var types type) (value : type.Value) :
    (localEnv environment).write (localId var) (SType.ofCore type)
      ⟨SType.ofCore type, scalarValue type value⟩ = .ok (localEnv (environment.set var value)) := by
  simp only [Locals.write, localEnv_find]
  simp [localEnv, Locals.replace, localScope_find, localScope_replace]

def binder (type : Core.Ty) (index : Nat) : Binder := {id := 2 * index, type := SType.ofCore type}

theorem localEnv_declare (environment : Core.Env types) (value : type.Value) :
    (localEnv environment).declare (binder type types.length)
      (some ⟨SType.ofCore type, scalarValue type value⟩) =
        .ok (localEnv (.cons value environment)) := by
  have absent := localScope_outside environment (2 * types.length) (Nat.le_refl _)
  simp [Locals.declare, localEnv, binder, Locals.find, absent, localScope]

/-- Compatibility proofs may retain additional return cells or lexical scopes.
They need exactly the observable reads of the old vars. -/
def Represents (locals : Locals) (environment : Core.Env types) : Prop :=
  ∀ {type} (var : Core.Var types type), locals.read (localId var) (SType.ofCore type) =
    .ok ⟨SType.ofCore type, scalarValue type (environment.get var)⟩

theorem localEnv_represents (environment : Core.Env types) : Represents (localEnv environment) environment :=
  fun var => localEnv_read environment var

end Solidity.Execution.Compatibility
