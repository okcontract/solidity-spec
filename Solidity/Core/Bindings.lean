/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Expression

namespace Solidity.Core

/-- Resolved typed de Bruijn variables. Names occur only in elaboration. -/
inductive Var : List Ty → Ty → Type where
  | here : Var (type :: rest) type
  | there : Var rest type → Var (other :: rest) type

inductive Env : List Ty → Type where
  | nil : Env []
  | cons : type.Value → Env rest → Env (type :: rest)

def Env.get : Env types → Var types type → type.Value
  | .cons value _, .here => value
  | .cons _ rest, .there var => rest.get var

def Env.set : Env types → Var types type → type.Value → Env types
  | .cons _ rest, .here, value => .cons value rest
  | .cons value rest, .there var, next => .cons value (rest.set var next)

def Env.append : Env types → Env rest → Env (types ++ rest)
  | .nil, tail => tail
  | .cons value values, tail => .cons value (values.append tail)

theorem Env.get_set (env : Env types) (var : Var types type) (value : type.Value) :
    (env.set var value).get var = value := by
  induction env with
  | nil => cases var
  | cons head rest ih => cases var with
    | here => rfl
    | there var => exact ih var

/-- Local-only scalar expressions use resolved indices, not default-zero names. -/
abbrev LocalExpr (types : List Ty) (type : Ty) := Expr (Var types) type

def LocalExpr.eval (env : Env types) (order : OperandOrder) (expr : LocalExpr types type) :
    Result type.Value := Expr.eval env.get order expr

end Solidity.Core
