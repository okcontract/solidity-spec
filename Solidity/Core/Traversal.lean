/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Expression

/-! Checked substitution of typed expression leaves. Traversal checks every
branch at elaboration time, independently of runtime short-circuiting. -/
namespace Solidity.Core
variable {Ref Other : Ty → Type} {Error : Type}

/-- Replace each reference by a checked expression, preserving all operators. -/
def Expr.traverse (leaf : ∀ {type}, Ref type → Except Error (Expr Other type)) :
    Expr Ref type → Except Error (Expr Other type)
  | .literal value => .ok (.literal value)
  | .read ref => leaf ref
  | .unary op arg => do return .unary op (← arg.traverse leaf)
  | .binary op a b => do return .binary op (← a.traverse leaf) (← b.traverse leaf)
  | .ite test yes no => do return .ite (← test.traverse leaf) (← yes.traverse leaf) (← no.traverse leaf)
  | .and a b => do return .and (← a.traverse leaf) (← b.traverse leaf)
  | .or a b => do return .or (← a.traverse leaf) (← b.traverse leaf)

/-- Structural specification, parameterized by an independently stated relation
at leaves. This relation does not mention the traversal algorithm. -/
inductive Expr.Traverses (leaf : ∀ {type}, Ref type → Expr Other type → Prop) :
    Expr Ref type → Expr Other type → Prop where
  | literal : Traverses leaf (.literal value) (.literal value)
  | read : leaf ref target → Traverses leaf (.read ref) target
  | unary : Traverses leaf a x → Traverses leaf (.unary op a) (.unary op x)
  | binary : Traverses leaf a x → Traverses leaf b y →
      Traverses leaf (.binary op a b) (.binary op x y)
  | ite : Traverses leaf test check → Traverses leaf yes a → Traverses leaf no b →
      Traverses leaf (.ite test yes no) (.ite check a b)
  | and : Traverses leaf a x → Traverses leaf b y → Traverses leaf (.and a b) (.and x y)
  | or : Traverses leaf a x → Traverses leaf b y → Traverses leaf (.or a b) (.or x y)

theorem Expr.traverse_sound
    (f : ∀ {type}, Ref type → Except Error (Expr Other type))
    (leaf : ∀ {type}, Ref type → Expr Other type → Prop)
    (sound : ∀ {type} (ref : Ref type) target, f ref = .ok target → leaf ref target)
    (source : Expr Ref type) (target : Expr Other type)
    (h : source.traverse f = .ok target) : Traverses leaf source target := by
  induction source with
  | literal value => cases h; exact .literal
  | read ref => exact .read (sound ref target h)
  | unary op arg ih =>
      simp only [traverse] at h
      cases hr : arg.traverse f with
      | error error => simp [hr] at h <;> cases h
      | ok next => simp [hr] at h; cases h; exact .unary (ih next hr)
  | binary op a b ia ib =>
      simp only [traverse] at h
      cases ha : a.traverse f with
      | error error => simp [ha] at h <;> cases h
      | ok x => cases hb : b.traverse f with
        | error error => simp [ha, hb] at h <;> cases h
        | ok y => simp [ha, hb] at h; cases h; exact .binary (ia x ha) (ib y hb)
  | ite test yes no it iy ino =>
      simp only [traverse] at h
      cases ht : test.traverse f with
      | error error => simp [ht] at h <;> cases h
      | ok check => cases hy : yes.traverse f with
        | error error => simp [ht, hy] at h <;> cases h
        | ok a => cases hn : no.traverse f with
          | error error => simp [ht, hy, hn] at h <;> cases h
          | ok b => simp [ht, hy, hn] at h; cases h; exact .ite (it check ht) (iy a hy) (ino b hn)
  | and a b ia ib =>
      simp only [traverse] at h
      cases ha : a.traverse f with
      | error error => simp [ha] at h <;> cases h
      | ok x => cases hb : b.traverse f with
        | error error => simp [ha, hb] at h <;> cases h
        | ok y => simp [ha, hb] at h; cases h; exact .and (ia x ha) (ib y hb)
  | or a b ia ib =>
      simp only [traverse] at h
      cases ha : a.traverse f with
      | error error => simp [ha] at h <;> cases h
      | ok x => cases hb : b.traverse f with
        | error error => simp [ha, hb] at h <;> cases h
        | ok y => simp [ha, hb] at h; cases h; exact .or (ia x ha) (ib y hb)

theorem Expr.traverse_complete
    (f : ∀ {type}, Ref type → Except Error (Expr Other type))
    (leaf : ∀ {type}, Ref type → Expr Other type → Prop)
    (complete : ∀ {type} (ref : Ref type) target, leaf ref target → f ref = .ok target)
    (h : Traverses leaf source target) : source.traverse f = .ok target := by
  induction h with
  | literal => rfl
  | read h => exact complete _ _ h
  | unary _ ih => simp [traverse, ih] <;> rfl
  | binary _ _ ia ib => simp [traverse, ia, ib] <;> rfl
  | ite _ _ _ it iy ino => simp [traverse, it, iy, ino] <;> rfl
  | and _ _ ia ib => simp [traverse, ia, ib] <;> rfl
  | or _ _ ia ib => simp [traverse, ia, ib] <;> rfl

/-- Successful leaf elaboration preserves evaluation under any environments
that give those leaves their specified values. -/
theorem Expr.Traverses.eval
    (leaf : ∀ {type}, Ref type → Expr Other type → Prop)
    (readSource : ∀ {type}, Ref type → type.Value)
    (readTarget : ∀ {type}, Other type → type.Value) (order : OperandOrder)
    (preserves : ∀ {type} (ref : Ref type) target, leaf ref target →
      target.eval readTarget order = .ok (readSource ref))
    (h : Traverses leaf source target) :
    target.eval readTarget order = source.eval readSource order := by
  induction h with
  | literal => rfl
  | read h => exact preserves _ _ h
  | unary _ ih => simp only [Expr.eval, ih]
  | binary _ _ ia ib => cases order <;> simp only [Expr.eval, ia, ib]
  | ite _ _ _ it iy ino => simp only [Expr.eval, it, iy, ino]
  | and _ _ ia ib => simp only [Expr.eval, ia, ib]
  | or _ _ ia ib => simp only [Expr.eval, ia, ib]

end Solidity.Core
