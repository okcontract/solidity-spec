/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Configuration
import Solidity.Core.Execution.Safety.SourceTyping

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem scope_environment_find (scope : Scope) (key : LocalId) :
    ((Safety.Scope.environment scope).find? fun entry => entry.1 == key).map Prod.snd =
      (scope.find key).map LocalCell.type := by
  induction scope with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨localId,cell⟩
      by_cases same : localId = key
      · subst localId; simp [Safety.Scope.environment,Execution.Scope.find]
      · simpa [Safety.Scope.environment,Execution.Scope.find,same] using ih

theorem environment_find (locals : Execution.Locals) (key : LocalId) :
    Environment.find (Safety.Locals.environment locals) key = (locals.find key).map LocalCell.type := by
  induction locals with
  | nil => rfl
  | cons scope rest ih =>
      simp only [Environment.find,Safety.Locals.environment,List.map_cons,List.flatten_cons,List.find?_append]
      have first := scope_environment_find scope key
      cases selected : (Safety.Scope.environment scope).find? fun entry => entry.1 == key with
      | some entry =>
          cases runtime : scope.find key with
          | none => simp [selected,runtime] at first
          | some cell =>
              simp only [selected,Option.map_some,runtime,Option.some.injEq] at first
              simp [Execution.Locals.find,runtime,first]
      | none =>
          cases runtime : scope.find key with
          | some cell => simp [selected,runtime] at first
          | none =>
              simpa [Environment.find,Safety.Locals.environment,Execution.Locals.find,selected,runtime] using ih

theorem StateRep.locals (represented : StateRep program objects environment state) :
    LocalsRep program state.heap objects environment state.locals :=
  ⟨represented.shape,represented.nonempty,fun _ _ bound => represented.cells.find bound⟩

theorem StateRep.nonempty_environment (represented : StateRep program objects environment state) :
    environment ≠ [] := by
  intro empty
  have shape := represented.shape
  rw [empty] at shape
  cases current : state.locals with
  | nil => exact represented.nonempty current
  | cons scope rest => rw [current] at shape; cases shape

theorem StateRep.local_read {localId : LocalId} (represented : StateRep program objects environment state)
    (bound : Environment.find environment localId = some type) :
    ∃ value, state.locals.read localId type = .ok value ∧ ValueRep program state.heap objects value := by
  rw [← represented.shape,environment_find] at bound
  cases found : state.locals.find localId with
  | none => simp [found] at bound
  | some cell =>
      simp only [found,Option.map_some,Option.some.injEq] at bound
      cases bound
      exact represented.locals.read found

theorem StateRep.enter (represented : StateRep program objects environment state) :
    StateRep program objects (Environment.enter environment) {state with locals := state.locals.enter} := by
  exact ⟨represented.heap,represented.cells.enter,congrArg (List.cons []) represented.shape,by simp [Execution.Locals.enter]⟩

theorem StateRep.leave (represented : StateRep program objects (inner :: outer) state) (nonempty : outer ≠ []) :
    ∃ after, state.locals.leave = .ok after ∧
      StateRep program objects outer {state with locals := after} := by
  cases current : state.locals with
  | nil => exact False.elim (represented.nonempty current)
  | cons scope rest =>
      have shape := represented.shape
      simp only [current,Safety.Locals.environment,List.map_cons,List.cons.injEq] at shape
      refine ⟨rest,rfl,represented.heap,?_,shape.2,?_⟩
      · exact CellsRep.leave (by simpa only [current] using represented.cells)
      · intro empty
        change rest = [] at empty
        rw [empty] at shape
        exact nonempty shape.2.symm

theorem configuration_expression (closed : Profile.ClosedProgram registry program)
    (represented : StateRep program objects environment state)
    (form : Profile.Expression program expression)
    (admitted : Admission.admitExpression registry fuel state.locals expression = .ok ()) :
    ConfigurationRep registry program (Config.expression state expression) := by
  have checked := Profile.checkedExpression_of_admission admitted
  rw [represented.shape] at checked
  exact ⟨⟨closed,objects,environment,environment,.value expression.type,represented,
    .eval ⟨form,checked⟩,.value,objects,environment,represented⟩⟩

theorem configuration_statement (closed : Profile.ClosedProgram registry program)
    (represented : StateRep program objects environment state)
    (form : Profile.Body program statement)
    (admitted : Admission.admitStatement registry fuel state.locals [] statement = .ok ()) :
    ConfigurationRep registry program (Config.start state statement) := by
  unfold Admission.admitStatement at admitted
  obtain ⟨flow,checked,_⟩ := SourceTyping.bind_checked admitted
  have code : BodyCode registry program environment ⟨[],false⟩ statement :=
    ⟨form,⟨fuel,Admission.Context.ofLocals state.locals,false,flow,
      .of_eq ((Profile.scopes_ofLocals state.locals).trans represented.shape),checked⟩,by simp⟩
  exact ⟨⟨closed,objects,environment,prefixEnvironment environment statement,.signal ⟨[],false⟩,
    represented,.body code,.signal,objects,environment,represented⟩⟩

end Solidity.Execution.Safety
