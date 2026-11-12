/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Pilots.OrderAliasRollbackTarget

namespace Solidity.Pilots.OrderAliasRollback
open Static Aggregates Execution Execution.Safety
open Contract.Interaction (Word wordBytes)
open AliasCallRollback (Related)

def targetObservation (world : Contract.Evm.World) (transaction : Contract.Evm.Stateful.Transaction)
    (context : Contract.Context) (memory : Contract.Interaction.Memory) (value : Word)
    (writeFirst fail : Bool) (gas : Nat) : Contract.Evm.Stateful.Frame :=
  Contract.Evm.Stateful.observe world transaction context (Target.input value fail)
    (Contract.Evm.Stateful.runMetered (Target.code writeFirst) (Target.input value fail)
      ⟨transaction.original context.self,false⟩ 60 gas
      (Target.initial (world.storage context.self) memory (transaction.warm context.self) transaction.refund))

def Observes (source : Observation Unit) (target : Contract.Evm.Stateful.Frame) : Prop :=
  match source with
  | .returned [.atom ⟨.uint 31,value⟩] after =>
      target.status = .returned ∧ target.bytes = wordBytes value ∧ Related after.heap target.world
  | .failed (.panic code) before =>
      target.status = .reverted ∧ target.bytes = Contract.panic code ∧ Related before.heap target.world
  | .failed (.revert bytes) before =>
      target.status = .reverted ∧ target.bytes = bytes ∧ Related before.heap target.world
  | _ => False

/-- Each artifact has an actual permitted source execution for all words,
failure flags and related entry worlds. The source needs no materialization
allowance. The target has an exact consumption equation and a gas threshold;
overflow, explicit revert and insufficient gas restore its complete snapshot. -/
theorem refines (represented : WordArena.Represents heap AliasCallRollback.object)
    (zero : heap.execution.memory.read 160 32 = wordBytes 0)
    (writable : heap.execution.context.readOnly = false) (related : Related heap world)
    (transaction : Contract.Evm.Stateful.Transaction) (context : Contract.Context) (value : Word)
    (writeFirst fail : Bool) (budget : Nat) :
    ∃ observed used needed,
      source heap context.self value writeFirst fail budget = .finished observed ∧ used ≤ needed ∧
      (∀ gas, needed ≤ gas →
        Observes observed (targetObservation world transaction context heap.execution.memory value writeFirst fail gas) ∧
        (targetObservation world transaction context heap.execution.memory value writeFirst fail gas).gasRemaining = gas-used) ∧
      (∀ gas, gas < needed → targetObservation world transaction context heap.execution.memory value writeFirst fail gas =
        ⟨⟨.exceptional,[],world,0⟩,transaction⟩) ∧
      (∀ gas, needed ≤ gas → overflows writeFirst value || fail = true →
        (targetObservation world transaction context heap.execution.memory value writeFirst fail gas).world = world ∧
        (targetObservation world transaction context heap.execution.memory value writeFirst fail gas).transaction = transaction) := by
  obtain ⟨used,needed,final,trace,exit,storage⟩ := Target.target_trace
    (world.storage context.self) (transaction.original context.self) heap.execution.memory
    (transaction.warm context.self) transaction.refund value writeFirst fail
  have bounded := Contract.Evm.Guarded.used_le_needed _ _ _ _ _ _ trace
  have metered (gas : Nat) := Contract.Evm.Guarded.metered_of_run _ _ _ _ _ _ gas trace
  have execution := source_execution represented zero writable context.self value writeFirst fail budget
  refine ⟨_,used,needed,execution,bounded,?_,?_,?_⟩
  · intro gas enough
    unfold targetObservation Contract.Evm.Stateful.runMetered
    rw [metered gas,if_pos enough]
    rcases final with ⟨exitValue,finalState⟩
    dsimp only at exit storage
    subst exitValue
    cases overflow : overflows writeFirst value <;> cases fail
    all_goals
      simp [Target.halt,observation,Observes,after,state,overflow,storage,
        Contract.Evm.Stateful.observe,Contract.Evm.World.transfer,Target.input,AliasCallRollback.Target.input]
      first | exact related | exact related.updated context.self value
  · intro gas insufficient
    unfold targetObservation Contract.Evm.Stateful.runMetered
    rw [metered gas,if_neg (by omega)]
    rfl
  · intro gas enough failed
    unfold targetObservation Contract.Evm.Stateful.runMetered
    rw [metered gas,if_pos enough]
    rcases final with ⟨exitValue,finalState⟩
    dsimp only at exit
    subst exitValue
    cases overflow : overflows writeFirst value <;> cases fail
    all_goals simp_all [Target.halt,Contract.Evm.Stateful.observe]

end Solidity.Pilots.OrderAliasRollback
