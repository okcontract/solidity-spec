/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Transition

/-! Finite transition prefixes and simulations for semantic clients. A source step can
expand to several shared-machine steps, so neither equal fuel budgets nor
equal transition counts are assumed. Suspensions are not successful prefixes. -/
namespace Solidity.Execution

inductive Reaches (step : Nat → Config → Progress Config Observation) : Config → Config → Prop where
  | refl (config : Config) : Reaches step config config
  | next : step choice before = .next middle → Reaches step middle after → Reaches step before after

theorem Reaches.single (moved : step choice before = .next after) : Reaches step before after :=
  .next moved (.refl _)

theorem Reaches.trans (first : Reaches step before middle) (last : Reaches step middle after) :
    Reaches step before after := by
  induction first with
  | refl => exact last
  | next moved _ ih => exact .next moved (ih last)

theorem Reaches.executes (path : Reaches step before middle) (tail : Executes step middle observed) :
    Executes step before observed := by
  induction path with
  | refl => exact tail
  | next moved _ ih => exact .next moved (ih tail)

/-- The bridge owner must prove concrete initial/step/terminal correspondence.
These fields mention individual machine transitions and observations, never an
opaque old-interpreter invocation in the new machine. -/
structure FiniteSimulation
    (source : Nat → SourceConfig → Progress SourceConfig SourceObservation)
    (target : Nat → TargetConfig → Progress TargetConfig TargetObservation)
    (related : SourceConfig → TargetConfig → Prop)
    (observes : SourceObservation → TargetObservation → Prop) : Prop where
  terminal : ∀ before after result choice, related before after → source choice before = .done result →
    ∃ observed, Executes target after observed ∧ observes result observed
  advance : ∀ before after middle choice, related before after → source choice before = .next middle →
    ∃ next, Reaches target after next ∧ related middle next

theorem FiniteSimulation.executes
    (simulation : FiniteSimulation source target related observes)
    (matched : related initial start) (finished : Executes source initial result) :
    ∃ observed, Executes target start observed ∧ observes result observed := by
  induction finished generalizing start with
  | done terminal => exact simulation.terminal _ _ _ _ matched terminal
  | next moved _ ih =>
      obtain ⟨next, path, matched⟩ := simulation.advance _ _ _ _ matched moved
      obtain ⟨observed, tail, same⟩ := ih matched
      exact ⟨observed, path.executes tail, same⟩

/-- Finite source executions have sufficient target fuel and choices. No
termination claim is made about other source executions or strategies. -/
theorem FiniteSimulation.run_complete
    (simulation : FiniteSimulation source target related observes)
    (matched : related initial start) (finished : Executes source initial result) :
    ∃ fuel choices observed, run target fuel choices start = .finished observed ∧ observes result observed := by
  obtain ⟨observed, targetExecution, same⟩ := simulation.executes matched finished
  obtain ⟨fuel, choices, runFinished⟩ := Solidity.Execution.run_complete target targetExecution
  exact ⟨fuel, choices, observed, runFinished, same⟩

end Solidity.Execution
