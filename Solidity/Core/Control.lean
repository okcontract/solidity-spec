/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Statement

/-! Structured loop control over the shared scalar statement core. Fuel belongs
to the executable interpreter, not the Solidity observation. The relational
semantics has no fuel parameter. This is not an EVM gas model. -/
namespace Solidity.Core.Control

variable {Ref Place : Ty → Type} {State : Type}

inductive Command (Ref Place : Ty → Type) where
  | block : Block Ref Place → Command Ref Place
  | seq : Command Ref Place → Command Ref Place → Command Ref Place
  | branch : Expr Ref .bool → Command Ref Place → Command Ref Place → Command Ref Place
  /-- The post block runs on ordinary iteration and continue, but not break.
  A while loop uses skip; a for loop uses its increment block. -/
  | loop : Expr Ref .bool → Command Ref Place → Block Ref Place → Command Ref Place
  | break_
  | continue_

inductive Frame (Ref Place : Ty → Type) where
  | next : Command Ref Place → Frame Ref Place
  | loop : Expr Ref .bool → Command Ref Place → Block Ref Place → Frame Ref Place

inductive Signal (State : Type) where
  | next | break_ | continue_
  | halt : Outcome State → Signal State

inductive Config (Ref Place : Ty → Type) (State : Type) where
  | exec : Command Ref Place → List (Frame Ref Place) → State → Config Ref Place State
  | resume : Signal State → List (Frame Ref Place) → State → Config Ref Place State

/-- An escaping break/continue is malformed resolved control, not an EVM fault.
The frontend must prove this case unreachable for admitted source. -/
inductive Observation (State : Type) where
  | completed : Flow State → Observation State
  | invalidControl : Observation State

inductive Progress (Ref Place : Ty → Type) (State : Type) where
  | next : Config Ref Place State → Progress Ref Place State
  | done : Observation State → Progress Ref Place State

def step (store : Store Ref Place State) (order : OperandOrder) :
    Config Ref Place State → Progress Ref Place State
  | .exec (.block body) stack state =>
      match body.eval store order state with
      | .next after => .next (.resume .next stack after)
      | .halt result => .next (.resume (.halt result) stack state)
  | .exec (.seq first rest) stack state => .next (.exec first (.next rest :: stack) state)
  | .exec (.branch test yes no) stack state =>
      match test.eval (store.read state) order with
      | .error bytes => .next (.resume (.halt (.reverted bytes)) stack state)
      | .ok choice => .next (.exec (if choice then yes else no) stack state)
  | .exec (.loop test body post) stack state =>
      match test.eval (store.read state) order with
      | .error bytes => .next (.resume (.halt (.reverted bytes)) stack state)
      | .ok false => .next (.resume .next stack state)
      | .ok true => .next (.exec body (.loop test body post :: stack) state)
  | .exec .break_ stack state => .next (.resume .break_ stack state)
  | .exec .continue_ stack state => .next (.resume .continue_ stack state)
  | .resume .next [] state => .done (.completed (.next state))
  | .resume (.halt result) _ _ => .done (.completed (.halt result))
  | .resume .break_ [] _ | .resume .continue_ [] _ => .done .invalidControl
  | .resume .next (.next rest :: stack) state => .next (.exec rest stack state)
  | .resume .break_ (.next _ :: stack) state => .next (.resume .break_ stack state)
  | .resume .continue_ (.next _ :: stack) state => .next (.resume .continue_ stack state)
  | .resume .break_ (.loop _ _ _ :: stack) state => .next (.resume .next stack state)
  | .resume .next (.loop test body post :: stack) state
  | .resume .continue_ (.loop test body post :: stack) state =>
      .next (.exec (.seq (.block post) (.loop test body post)) stack state)

inductive Execution (Ref Place : Ty → Type) (State : Type) where
  | finished : Observation State → Execution Ref Place State
  | exhausted : Config Ref Place State → Execution Ref Place State

def run (store : Store Ref Place State) (order : OperandOrder) :
    Nat → Config Ref Place State → Execution Ref Place State
  | fuel, config => match step store order config with
    | .done result => .finished result
    | .next after => match fuel with
      | 0 => .exhausted config
      | remaining + 1 => run store order remaining after

/-- Finite execution in the transition semantics, independent of fuel. -/
inductive Executes (store : Store Ref Place State) (order : OperandOrder) :
    Config Ref Place State → Observation State → Prop where
  | done : step store order config = .done result → Executes store order config result
  | next : step store order config = .next after → Executes store order after result →
      Executes store order config result

theorem run_sound (store : Store Ref Place State) (order : OperandOrder)
    (fuel : Nat) (config : Config Ref Place State) (result : Observation State)
    (h : run store order fuel config = .finished result) : Executes store order config result := by
  induction fuel generalizing config with
  | zero =>
      cases hs : step store order config with
      | done observed => simp [run, hs] at h; cases h; exact .done hs
      | next after => simp [run, hs] at h
  | succ fuel ih =>
      cases hs : step store order config with
      | done observed => simp [run, hs] at h; cases h; exact .done hs
      | next after =>
          rw [run, hs] at h
          exact .next hs (ih after h)

theorem run_complete (store : Store Ref Place State) (order : OperandOrder)
    (h : Executes store order config result) :
    ∃ fuel, run store order fuel config = .finished result := by
  induction h with
  | done hs => exact ⟨0, by simp [run, hs]⟩
  | next hs _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simp [run, hs, h]⟩

theorem run_more (store : Store Ref Place State) (order : OperandOrder)
    (fuel extra : Nat) (config : Config Ref Place State) (result : Observation State)
    (h : run store order fuel config = .finished result) :
    run store order (fuel + extra) config = .finished result := by
  induction fuel generalizing config with
  | zero =>
      cases hs : step store order config with
      | done observed => simpa [run, hs] using h
      | next after => simp [run, hs] at h
  | succ fuel ih =>
      cases hs : step store order config with
      | done observed => simpa [run, hs] using h
      | next after =>
          rw [run, hs] at h
          rw [Nat.succ_add, run, hs]
          exact ih after h

/-- Different sufficient fuel budgets cannot change the source observation. -/
theorem executes_deterministic (store : Store Ref Place State) (order : OperandOrder)
    (a : Executes store order config first) (b : Executes store order config second) :
    first = second := by
  induction a with
  | done ha => cases b with
    | done hb => simpa [ha] using hb
    | next hb _ => simp [ha] at hb
  | next ha _ ih => cases b with
    | done hb => simp [ha] at hb
    | next hb tail =>
        have same := Progress.next.inj (ha.symm.trans hb)
        cases same
        exact ih tail

end Solidity.Core.Control
