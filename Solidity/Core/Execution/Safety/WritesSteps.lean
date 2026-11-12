/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.StepLaws
import Solidity.Core.Execution.Safety.TargetWrites

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

/-- Sequential result/tuple commits retain every still-pending represented
operand. The write order is the actual machine list order, including its
separate tuple and function-result policies. -/
theorem writes_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (.tuple .nil)))
    (represented : WritesRep registry program state.heap objects environment writes) :
    StepRep registry program ⟨.writes writes,stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.writes writes,stack,state,entry⟩) := by
  cases represented with
  | nil =>
      apply stepRep_next (after := ⟨.value (.tuple []),stack,state,entry⟩)
      · rfl
      · exact context.value (.tuple .nil)
      · rfl
      · dsimp; omega
  | @cons destination destinationType value restWrites target source transfer rest =>
      rcases TargetWrites.writeTarget_total physicalBackend context.stateRep target source transfer fuel with
        failed | ⟨after,written,stateRep,invocation,budget⟩
      · apply stepRep_source (failure := .exceptional) _ rfl
        simp [Machine.transition,failed]
      · apply stepRep_next (after := ⟨.writes restWrites,stack,after,entry⟩)
        · apply step_of_transition
          simp [Machine.transition,written,Machine.next]
        · exact (context.replace_state stateRep invocation).configuration
            (.writes (rest.extend invocation (fun _ member => member)))
        · rfl
        · dsimp; omega

end Solidity.Execution.Safety
