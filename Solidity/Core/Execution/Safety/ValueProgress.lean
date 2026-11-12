/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.ValueAssignments
import Solidity.Core.Execution.Safety.ValueControlSteps
import Solidity.Core.Execution.Safety.ReturnSteps

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

/-- Value results cannot escape into a statement-only frame. Every compatible
saved operand/alias is represented by the independently indexed continuation. -/
theorem value_progress (witness : ConfigurationWitness registry program config)
    (taskEq : config.task = .value datum) :
    StepRep registry program config (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice config) := by
  rcases config with ⟨task,stack,state,entry⟩
  change task = .value datum at taskEq
  subst task
  rcases witness with ⟨closed,objects,environment,resultEnvironment,kind,stateRep,taskRep,stackRep,checkpoint⟩
  cases taskRep with
  | value represented =>
      cases stackRep with
      | value =>
          obtain ⟨stepped,observation⟩ := returned_value_progress (registry := registry) (fuel := fuel+2) (choice := choice) stateRep represented
          rw [stepped]
          exact observation
      | cons frame continuation =>
          cases frame with
          | mode => exact value_mode_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented
          | discard => exact value_discard_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented
          | returnValue allowed => exact value_returnValue_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented allowed
          | collect active completion =>
              exact stepRep_of_unchanged
                (collected_value_progress closed stateRep represented active completion continuation checkpoint)
          | select yes no same => exact value_select_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented yes no same
          | branch yes no => exact value_branch_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented yes no
          | lazy right boolean => exact value_lazy_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented right boolean
          | assignRight target allowed => exact value_assignRight_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented target allowed
          | commitTarget target allowed => exact value_commit_progress ⟨closed,stateRep,continuation,checkpoint⟩ target represented allowed
          | compoundRight target leftSupport rightSupport token allowed =>
              exact value_compoundRight_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented target leftSupport rightSupport token allowed
          | compoundTarget target leftSupport rightSupport token allowed =>
              exact value_compoundCommit_progress ⟨closed,stateRep,continuation,checkpoint⟩ target represented leftSupport rightSupport token allowed
          | commitOld target old oldType leftSupport rightSupport token allowed =>
              exact value_commitOld_progress ⟨closed,stateRep,continuation,checkpoint⟩ target oldType represented leftSupport rightSupport token allowed
          | declare ready allowed fresh =>
              exact value_declare_progress closed stateRep represented allowed fresh continuation checkpoint
          | loopCondition test boolean body post =>
              exact value_loopCondition_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented test boolean body post
          | doCondition body test boolean =>
              exact value_doCondition_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented body test boolean
          | resultTransfer caller callerShape callerNonempty returnCells returnReady =>
              obtain ⟨after,finished,afterRep,entryEq,_,_,_,remaining⟩ := finishCall_progress _ closed stateRep caller
                callerShape callerNonempty returnCells continuation checkpoint
              apply stepRep_next (after := after)
              · apply step_of_transition
                exact finished
              · exact afterRep
              · exact entryEq
              · dsimp at remaining ⊢;omega

end Solidity.Execution.Safety
