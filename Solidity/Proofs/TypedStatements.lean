/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Procedure
import Solidity.Proofs.TypedExpressions

namespace Solidity.Compatibility.Typed
open Core

abbrev types (ts : List Contract.Ty) := ts.map type

def localVar : Contract.Var ts t → Core.Var (types ts) (type t)
  | .here => .here
  | .there v => .there (localVar v)

def environment : Contract.Env ts → Core.Env (types ts)
  | .nil => .nil
  | .cons (t := t) v vs => .cons (value t v) (environment vs)

@[simp] theorem environment_get (env : Contract.Env ts) (v : Contract.Var ts t) :
    (environment env).get (localVar v) = value t (env.get v) := by
  induction v with
  | here => cases env; rfl
  | there v ih => cases env; exact ih _

@[simp] theorem environment_set (env : Contract.Env ts) (v : Contract.Var ts t) (x : t.Value) :
    (environment env).set (localVar v) (value t x) = environment (env.set v x) := by
  induction v with
  | here => cases env; rfl
  | there v ih =>
      cases env with
      | cons head tail => exact congrArg (Core.Env.cons (value _ head)) (ih tail x)

theorem env_cons_cast {as bs : List Core.Ty} (h : as = bs) (v : t.Value) (tail : Core.Env as) :
    (congrArg (List.cons t) h) ▸ Core.Env.cons v tail = Core.Env.cons v (h ▸ tail) := by
  cases h; rfl

@[simp] theorem environment_append (a : Contract.Env ts) (b : Contract.Env us) :
    (List.map_append (f := type) (l₁ := ts) (l₂ := us)) ▸ environment (a.append b) = (environment a).append (environment b) := by
  induction a with
  | nil => rfl
  | @cons ts t x xs ih =>
      change (congrArg (List.cons (type t)) (List.map_append (f := type) (l₁ := ts) (l₂ := us))) ▸
          Core.Env.cons (value t x) (environment (xs.append b)) =
        Core.Env.cons (value t x) ((environment xs).append (environment b))
      rw [env_cons_cast, ih]
      exact List.map_append

@[simp] theorem environment_words (env : Contract.Env ts) :
    (environment env).abiWords = env.words := by
  induction env with
  | nil => rfl
  | @cons ts t v vs ih => cases t <;> simp [environment, Core.Env.abiWords, Core.Ty.abiWord, Contract.Env.words, value, ih] <;> rfl

inductive Global (slots : Nat) : Core.Ty → Type where
  | load : Fin slots → Global slots .word
  | caller : Global slots .address
  | self : Global slots .address

inductive Slot (slots : Nat) : Core.Ty → Type where
  | word : Fin slots → Slot slots .word

def frameStore (ctx : Contract.Context) : Core.Store (Global slots) (Slot slots) (Contract.Storage slots) where
  read state := fun {t} ref => match t, ref with
    | _, .load slot => state slot
    | _, .caller => ctx.caller
    | _, .self => ctx.self
  write state := fun {t} place v => match t, place, v with
    | _, .word slot, v => some (state.write slot v)

def frameReference : Reference slots ts t → FrameRef (Global slots) (types ts) t
  | .var v => .local (localVar v)
  | .load slot => .global (.load slot)
  | .caller => .global .caller
  | .self => .global .self

def frameExpr (e : Contract.Expr slots ts t) : Core.Expr (FrameRef (Global slots) (types ts)) (type t) :=
  (embed e).rename frameReference

@[simp] theorem frameExpr_eval (e : Contract.Expr slots ts t) (state : Contract.Storage slots)
    (ctx : Contract.Context) (env : Contract.Env ts) (order : OperandOrder) :
    (frameExpr e).eval (FrameRef.read ((frameStore ctx).read state) (environment env)) order =
      .ok (value t (e.eval state ctx env)) := by
  rw [frameExpr, Core.Expr.eval_rename]
  have h : (fun {t} (ref : Reference slots ts t) =>
      FrameRef.read ((frameStore ctx).read state) (environment env) (frameReference ref)) = @read slots ts state ctx env := by
    funext t ref
    cases ref with
    | @var inner v =>
        simp only [frameReference, FrameRef.read, environment_get]
        cases inner <;> rfl
    | load => rfl
    | caller => rfl
    | self => rfl
  rw [h]
  exact eval_embed e state ctx env order

def frameExprs : Contract.Exprs slots ts rs → Core.Exprs (FrameRef (Global slots) (types ts)) (types rs)
  | .nil => .nil
  | .cons x xs => .cons (frameExpr x) (frameExprs xs)

@[simp] theorem frameExprs_eval (es : Contract.Exprs slots ts rs) (state : Contract.Storage slots)
    (ctx : Contract.Context) (env : Contract.Env ts) (order : OperandOrder) :
    (frameExprs es).eval (FrameRef.read ((frameStore ctx).read state) (environment env)) order =
      .ok (environment (es.eval state ctx env)) := by
  induction es with
  | nil => rfl
  | cons x xs ih => simp [frameExprs, Core.Exprs.eval, frameExpr_eval, ih, Contract.Exprs.eval, environment] <;> rfl

def checkedOp : Contract.CheckedOp → Core.Arithmetic
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod

@[simp] theorem checkedOp_eval (op : Contract.CheckedOp) (a b : BitVec 256) :
    Core.unsigned 31 .checked (checkedOp op) a b = op.eval a b := by
  cases op <;> simp [Core.unsigned, checkedOp, Contract.CheckedOp.eval, Core.Width.bits] <;> rfl

def procedure : Contract.Stmt slots rs ts → Core.Procedure (Global slots) (Slot slots) (types rs) (types ts)
  | .ret es => .ret (frameExprs es)
  | .revert bytes => .revert bytes
  | .let_ e next => .let_ (frameExpr e) (procedure next)
  | .assign v e next => .assign (localVar v) (frameExpr e) (procedure next)
  | .checked op a b next => .let_ (.binary (.uintArithmetic 31 .checked (checkedOp op)) (frameExpr a) (frameExpr b)) (procedure next)
  | .assert_ e next => .branch (frameExpr e) (procedure next) (.revert (Contract.panic 1))
  | .store slot e next => .store (.word slot) (frameExpr e) (procedure next)
  | .branch e yes no => .branch (frameExpr e) (procedure yes) (procedure no)
  | .call (results := results) helper args next => .call (procedure helper) (frameExprs args)
      ((List.map_append (f := type) (l₁ := results) (l₂ := ts)) ▸ procedure next)
  | .emit bound topics data next => .emit (by simpa only [types, List.length_map] using bound)
      (frameExprs topics) (frameExprs data) (procedure next)

def event (log : Contract.Log) : Contract.Interaction.Event :=
  ⟨log.emitter.setWidth 256, log.topics, log.data.flatMap Contract.Interaction.wordBytes⟩

def procedureOutcome : Contract.Outcome slots rs → Core.ProcedureOutcome (Contract.Storage slots) (types rs)
  | .success state values logs => .returned state (environment values) (logs.map event)
  | .revert bytes => .reverted bytes

@[simp] theorem procedureOutcome_prepend (logs : List Contract.Log) (result : Contract.Outcome slots rs) :
    procedureOutcome (result.prependLogs logs) = (procedureOutcome result).prepend (logs.map event) := by
  cases result <;> simp [procedureOutcome, Contract.Outcome.prependLogs, Core.ProcedureOutcome.prepend]

/-- Universal correspondence, including helper locals/returns, logs, panics and
rollback. No new source admission or external-call guarantee is inferred. -/
theorem procedure_eval (stmt : Contract.Stmt slots rs ts) (state : Contract.Storage slots)
    (ctx : Contract.Context) (env : Contract.Env ts) :
    (procedure stmt).eval (frameStore ctx) ctx.self .leftFirst state (environment env) =
      procedureOutcome (stmt.eval state ctx env) := by
  induction stmt generalizing state with
  | ret es => simp [procedure, Core.Procedure.eval, Contract.Stmt.eval, procedureOutcome]
  | revert bytes => rfl
  | let_ e next ih =>
      simp only [procedure, Core.Procedure.eval, frameExpr_eval, Contract.Stmt.eval]
      exact ih state (.cons (e.eval state ctx env) env)
  | assign v e next ih => simp [procedure, Core.Procedure.eval, Contract.Stmt.eval, ih]
  | checked op a b next ih =>
      simp only [procedure, Core.Procedure.eval, Core.Expr.eval, frameExpr_eval, Core.Binary.eval,
        checkedOp_eval, value, Contract.Stmt.eval]
      simp only [bind, Except.bind, id_eq]
      cases op.eval (a.eval state ctx env) (b.eval state ctx env) with
      | error bytes => rfl
      | ok x => exact ih state (.cons x env)
  | assert_ e next ih => simp [procedure, Core.Procedure.eval, Contract.Stmt.eval, value]; split <;> simp [ih, procedureOutcome]
  | store slot e next ih =>
      simp only [procedure, Core.Procedure.eval, frameExpr_eval, Contract.Stmt.eval]
      exact ih _ env
  | branch e yes no iy inn => simp [procedure, Core.Procedure.eval, Contract.Stmt.eval, value]; split <;> simp [iy, inn]
  | call helper args next ih inext =>
      simp only [procedure, Core.Procedure.eval, frameExprs_eval, ih, Contract.Stmt.eval]
      cases h : helper.eval state ctx (args.eval state ctx env) with
      | revert bytes => rfl
      | success after values logs =>
          simp only [procedureOutcome]
          rw [← environment_append]
          rw [Core.Procedure.eval_cast]
          rw [inext]
          exact (procedureOutcome_prepend logs _).symm
  | emit bound topics data next ih =>
      simp [procedure, Core.Procedure.eval, Contract.Stmt.eval, ih, procedureOutcome_prepend,
        environment_words, event]

end Solidity.Compatibility.Typed
