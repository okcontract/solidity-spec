/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Init

/-! The finite runner consumes an independent choice at every transition.
Its budget and suspension are host observations, separate from source failure.
The transition relation has no fuel and does not require termination. -/
namespace Solidity.Execution

inductive Progress (Config Observation : Type) where
  | next : Config → Progress Config Observation
  | done : Observation → Progress Config Observation
  | suspended : Config → Progress Config Observation

inductive Execution (Config Observation : Type) where
  | finished : Observation → Execution Config Observation
  | exhausted : Config → List Nat → Execution Config Observation

def run (step : Nat → Config → Progress Config Observation) :
    Nat → List Nat → Config → Execution Config Observation
  | fuel, choices, config => match step (choices.headD 0) config with
    | .done result => .finished result
    | .suspended after => .exhausted after choices
    | .next after => match fuel with
      | 0 => .exhausted config choices
      | remaining + 1 => run step remaining choices.tail after

inductive Executes (step : Nat → Config → Progress Config Observation) :
    Config → Observation → Prop where
  | done : step choice config = .done result → Executes step config result
  | next : step choice config = .next after → Executes step after result →
      Executes step config result

theorem run_sound (step : Nat → Config → Progress Config Observation)
    (fuel : Nat) (choices : List Nat) (config : Config) (result : Observation)
    (h : run step fuel choices config = .finished result) : Executes step config result := by
  induction fuel generalizing config choices with
  | zero =>
      cases hs : step (choices.headD 0) config with
      | done observed => rw [run, hs] at h; cases h; exact .done hs
      | next after => rw [run, hs] at h; cases h
      | suspended after => rw [run, hs] at h; cases h
  | succ fuel ih =>
      cases hs : step (choices.headD 0) config with
      | done observed => rw [run, hs] at h; cases h; exact .done hs
      | next after =>
          rw [run, hs] at h
          exact .next hs (ih _ _ h)
      | suspended after => rw [run, hs] at h; cases h

theorem run_complete (step : Nat → Config → Progress Config Observation)
    (h : Executes step config result) :
    ∃ fuel choices, run step fuel choices config = .finished result := by
  induction h with
  | @done choice config result hs => exact ⟨0, [choice], by simp [run, hs]⟩
  | @next choice config after result hs _ ih =>
      obtain ⟨fuel, choices, h⟩ := ih
      exact ⟨fuel + 1, choice :: choices, by simp [run, hs, h]⟩

theorem run_more (step : Nat → Config → Progress Config Observation)
    (fuel extra : Nat) (choices : List Nat) (config : Config) (result : Observation)
    (h : run step fuel choices config = .finished result) :
    run step (fuel + extra) choices config = .finished result := by
  induction fuel generalizing config choices with
  | zero =>
      cases hs : step (choices.headD 0) config with
      | done observed => rw [run, hs] at h ⊢; exact h
      | next after => rw [run, hs] at h; cases h
      | suspended after => rw [run, hs] at h; cases h
  | succ fuel ih =>
      cases hs : step (choices.headD 0) config with
      | done observed => rw [run, hs] at h ⊢; exact h
      | next after =>
          rw [run, hs] at h
          rw [Nat.succ_add, run, hs]
          exact ih _ _ h
      | suspended after => rw [run, hs] at h; cases h

/-- A possible infinite source execution. Nondeterministic programs may also
have finite executions under different choices; neither possibility is erased. -/
def Diverges (step : Nat → Config → Progress Config Observation) (initial : Config) : Prop :=
  ∃ (states : Nat → Config) (choices : Nat → Nat), states 0 = initial ∧
    ∀ index, step (choices index) (states index) = .next (states (index + 1))

theorem self_loop_diverges (step : Nat → Config → Progress Config Observation)
    (config : Config) (h : step choice config = .next config) : Diverges step config := by
  exact ⟨fun _ => config, fun _ => choice, rfl, fun _ => h⟩

end Solidity.Execution
