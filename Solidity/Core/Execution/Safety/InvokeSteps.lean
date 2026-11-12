/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.StepLaws
import Solidity.Core.Execution.Safety.CallSetup
import Solidity.Core.Execution.Safety.ReturnSteps
import Solidity.Core.Execution.Safety.EnvironmentLaws
import Solidity.Core.Execution.Safety.PrefixBindings

/-! Constructive internal dispatch from represented operands and actual closed
program checks. Parameter preparation precedes null dispatch; nonnull handles
enter their real checked body with freshly initialized invocation-local cells. -/
namespace Solidity.Execution.Safety
open Static Aggregates
open SourceTyping (bind_checked)
open SupportedTransfers
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem invoke_forM_member (items : List α) (action : α → Aggregates.Result Unit)
    (checked : items.forM action = .ok ()) (member : item ∈ items) : action item = .ok () := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      obtain ⟨done,first,rest⟩ := bind_checked checked
      cases done
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · exact ih rest member

private theorem invoke_typesList (types : List SType) : typesList (Types.ofList types) = types := by
  induction types with
  | nil => rfl
  | cons type types ih => simp [Types.ofList,typesList,ih]

theorem callee_conversion_total (represented : ValueRep program heap objects callee)
    (ready : TypeReady registry callee.type)
    (allowed : Static.Allowed .implicit callee.type signature.type) :
    ∃ handle, Effects.scalarCast .implicit signature.type callee = .ok ⟨signature.type,handle⟩ ∧
      ScalarProgress.ClosedHandle program signature handle := by
  have supported : callee.type.scalarSupported = true := by
    rcases ready.1 with supported | ⟨pointer,equal⟩
    · exact supported
    · rw [equal] at allowed
      simp [Static.Allowed,Static.Implicit,WordArena.arrayType,FunctionSignature.type] at allowed
  obtain ⟨handle,converted⟩ := implicit_convert_total callee.type signature.type callee.value supported rfl allowed
  exact ⟨handle,scalar_cast_of_conversion converted,
    conversion_closed program callee signature.type handle (scalar_closed represented supported) allowed converted⟩

theorem lookup_function_checked (closed : Profile.ClosedProgram registry program)
    (lookup : program.lookup handle = .ok definition) :
    ∃ fuel, Admission.checkFunction registry fuel definition = .ok () := by
  obtain ⟨fuel,checked⟩ := closed.admitted
  unfold Admission.checkProgram at checked
  obtain ⟨done,_,all⟩ := bind_checked checked
  cases done
  unfold Program.lookup at lookup
  simp only [closed.valid,Bool.not_true,Bool.false_eq_true,↓reduceIte] at lookup
  cases selected : program.functions.find? (fun entry => entry.1 == handle) with
  | none => simp [selected] at lookup
  | some entry =>
      simp only [selected] at lookup
      have same : entry.2 = definition := Except.ok.inj lookup
      have checked := invoke_forM_member program.functions (fun entry => Admission.checkFunction registry fuel entry.2)
        all (List.mem_of_find?_eq_some selected)
      exact ⟨fuel,same ▸ checked⟩

theorem function_body_metadata (closed : Profile.ClosedProgram registry program)
    (lookup : program.lookup handle = .ok definition) :
    ∃ fuel incoming flow,
      Admission.checkStatement registry fuel incoming definition.returns 0 false definition.body = .ok flow ∧
      Profile.scopesEnvironment incoming.scopes =
        [((definition.parameters ++ definition.returns).map fun binder => (binder.id,binder.type))] ∧
      (∀ binder ∈ definition.parameters ++ definition.returns,TypeReady registry binder.type) := by
  obtain ⟨fuel,checked⟩ := lookup_function_checked closed lookup
  unfold Admission.checkFunction at checked
  obtain ⟨incoming,contextChecked,rest⟩ := bind_checked checked
  obtain ⟨flow,bodyChecked,_⟩ := bind_checked rest
  unfold Admission.functionContext at contextChecked
  obtain ⟨done,_,contextChecked⟩ := bind_checked contextChecked
  cases done
  obtain ⟨done,signatureChecked,contextChecked⟩ := bind_checked contextChecked
  cases done
  have shape : Profile.scopesEnvironment incoming.scopes =
      [((definition.parameters ++ definition.returns).map fun binder => (binder.id,binder.type))] := by
    rw [← Except.ok.inj contextChecked]
    rfl
  unfold Admission.checkSignature at signatureChecked
  obtain ⟨done,_,signatureChecked⟩ := bind_checked signatureChecked
  cases done
  obtain ⟨done,parametersChecked,returnsChecked⟩ := bind_checked signatureChecked
  cases done
  simp only [Admission.checkTypes,FunctionDefinition.signature,invoke_typesList] at parametersChecked returnsChecked
  refine ⟨fuel,incoming,flow,bodyChecked,shape,?_⟩
  intro binder member
  rcases List.mem_append.mp member with member | member
  · exact ⟨closed.parameters _ _ lookup binder member,SupportedEligibility.checkType_wellFormed
      (invoke_forM_member _ _ parametersChecked (List.mem_map.mpr ⟨binder,member,rfl⟩))⟩
  · exact ⟨closed.returns _ _ lookup binder member,SupportedEligibility.checkType_wellFormed
      (invoke_forM_member _ _ returnsChecked (List.mem_map.mpr ⟨binder,member,rfl⟩))⟩

private theorem binder_lookup (binders : List Binder) (distinct : (binders.map Binder.id).Nodup)
    (member : binder ∈ binders) :
    Environment.find [binders.map fun binder => (binder.id,binder.type)] binder.id = some binder.type := by
  induction binders with
  | nil => cases member
  | cons head rest ih =>
      obtain ⟨absent,tail⟩ := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with rfl | member
      · simp [Environment.find]
      · have different : head.id ≠ binder.id := by
          intro same
          exact absent (List.mem_map.mpr ⟨binder,member,same.symm⟩)
        simpa [Environment.find,different] using ih tail member

theorem function_runtime_environment (closed : Profile.ClosedProgram registry program)
    (lookup : program.lookup handle = .ok definition) :
    Environment.Equivalent
      [((definition.parameters ++ definition.returns).map fun binder => (binder.id,binder.type))]
      [((definition.parameters ++ definition.returns).map fun binder => (binder.id,binder.type)).reverse] ∧
    (∀ binder ∈ definition.returns,Environment.find
      [((definition.parameters ++ definition.returns).map fun binder => (binder.id,binder.type)).reverse]
      binder.id = some binder.type) := by
  have distinct := lookup_distinct closed.valid lookup
  have equivalent := Environment.Equivalent.single_permutation
    (List.reverse_perm ((definition.parameters ++ definition.returns).map fun binder => (binder.id,binder.type))).symm
    (by simpa only [List.map_map,Function.comp_def] using distinct)
  refine ⟨equivalent,?_⟩
  intro binder member
  rw [← equivalent.find]
  exact binder_lookup _ distinct (List.mem_append_right _ member)

private theorem invoke_prepared_none (config : Config Unit EmptyKey)
    (casted : Effects.scalarCast .implicit signature.type callee = .ok ⟨signature.type,none⟩)
    (prepared : Machine.prepareArguments registry limits config.state (typesList signature.parameters) arguments =
      .ok (values,config.state)) :
    Machine.invoke physicalBackend registry limits program config signature callee arguments = .error (.panic 0x51) := by
  unfold Machine.invoke
  rw [casted]
  cases signature
  simp [FunctionSignature.type,prepared]
  rfl

private theorem invoke_prepared_some (config : Config Unit EmptyKey)
    (casted : Effects.scalarCast .implicit signature.type callee = .ok ⟨signature.type,some handle⟩)
    (prepared : Machine.prepareArguments registry limits config.state (typesList signature.parameters) arguments =
      .ok (values,config.state))
    (lookup : program.lookup handle = .ok definition) (accepted : definition.signature.accepts signature = true)
    (bound : Machine.bindArguments physicalBackend registry limits
      {config.state with locals := Locals.empty,mode := .checked} definition.parameters values = .ok boundState)
    (returned : definition.returns.foldlM (Machine.declareReturn registry limits) boundState = .ok entered) :
    Machine.invoke physicalBackend registry limits program config signature callee arguments =
      .ok (.next ⟨.exec definition.body,
        .call config.state.locals config.state.mode definition.returns :: config.stack,entered,config.entry⟩) := by
  unfold Machine.invoke
  rw [casted]
  cases signature
  simp [FunctionSignature.type,prepared,lookup,accepted,bound,returned,Machine.next]

/-- Actual dispatch, shared by ordinary and named call completions after their
argument-order resolution. Successful setup and body admission are conclusions. -/
theorem invoke_total (config : Config Unit EmptyKey)
    (context : EvaluationContext registry program objects environment config.state config.entry config.stack
      (.value signature.resultType))
    (calleeRep : ValueRep program config.state.heap objects callee)
    (argsPacketRep : PacketRep program config.state.heap objects arguments (Types.ofList sourceTypes))
    (functionReady : TypeReady registry callee.type)
    (allowed : Static.Allowed .implicit callee.type signature.type)
    (argsReady : ArgumentsReady registry sourceTypes (typesList signature.parameters)) :
    Machine.invoke physicalBackend registry ⟨fuel+2,none⟩ program config signature callee arguments =
        .error (.panic 0x51) ∨
    ∃ after, Machine.invoke physicalBackend registry ⟨fuel+2,none⟩ program config signature callee arguments =
        .ok (.next after) ∧ ConfigurationRep registry program after ∧ after.entry = config.entry ∧
      after.state.materializationRemaining = config.state.materializationRemaining := by
  obtain ⟨handle,casted,handleClosed⟩ := callee_conversion_total calleeRep functionReady allowed
  obtain ⟨values,prepared,preparedRep⟩ := CallSetup.prepareArguments_total program registry fuel config.state objects
    arguments argsReady context.stateRep.heap argsPacketRep
  cases handle with
  | none => exact Or.inl (invoke_prepared_none config casted prepared)
  | some handle =>
      obtain ⟨definition,lookup,accepted⟩ := handleClosed handle rfl
      obtain ⟨sourceFuel,incoming,flow,bodyChecked,forwardShape,ready⟩ := function_body_metadata context.closed lookup
      have distinct := lookup_distinct context.closed.valid lookup
      obtain ⟨environmentSame,baseReturnCells⟩ := function_runtime_environment context.closed lookup
      have acceptedShapes := (FunctionSignature.accepts_iff _ _).mp accepted
      have parameterShape : definition.parameters.map Binder.type = typesList signature.parameters := by
        have same := congrArg typesList acceptedShapes.1
        simpa only [FunctionDefinition.signature,invoke_typesList] using same
      have preparedDefinition : PacketRep program config.state.heap objects values
          (Types.ofList (definition.parameters.map Binder.type)) := by
        rw [parameterShape]
        exact preparedRep
      obtain ⟨boundState,entered,bound,returned,enteredRep,_,heapSame,_,budgetSame⟩ :=
        CallSetup.initializeFunction_total physicalBackend program registry fuel config.state objects definition.parameters
          definition.returns values ready context.stateRep.heap preparedDefinition distinct
      let runtimeEnvironment :=
        [((definition.parameters ++ definition.returns).map fun binder => (binder.id,binder.type)).reverse]
      have incomingShape : Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) runtimeEnvironment :=
        (Environment.Equivalent.of_eq forwardShape).trans environmentSame
      have returnReady : ∀ binder ∈ definition.returns,TypeReady registry binder.type :=
        fun binder member => ready binder (List.mem_append_right _ member)
      have bodyForm := context.closed.bodies _ _ lookup
      have bodyCode : BodyCode registry program runtimeEnvironment ⟨definition.returns,false⟩ definition.body :=
        ⟨bodyForm,⟨sourceFuel,incoming,false,flow,incomingShape,bodyChecked⟩,returnReady⟩
      have returnCells : ∀ binder ∈ definition.returns,Environment.find
          (prefixEnvironment runtimeEnvironment definition.body) binder.id = some binder.type := by
        intro binder member
        exact body_prefix_preserves_bound definition.body bodyForm bodyChecked incomingShape (baseReturnCells binder member)
      have resultSame : Control.resultType ⟨definition.returns,false⟩ = signature.resultType := by
        rw [← return_packet_type]
        change packetResultType definition.signature.returns = packetResultType signature.returns
        exact congrArg packetResultType acceptedShapes.2.1
      have continuation : StackRep registry program entered.heap objects environment
          (.value (Control.resultType ⟨definition.returns,false⟩)) config.stack := by
        rw [heapSame,resultSame]
        exact context.continuation
      have caller : CellsRep program entered.heap objects config.state.locals := by
        rw [heapSame]
        exact context.stateRep.cells
      let after : Config Unit EmptyKey := ⟨.exec definition.body,
        .call config.state.locals config.state.mode definition.returns :: config.stack,entered,config.entry⟩
      refine Or.inr ⟨after,invoke_prepared_some config casted prepared lookup accepted bound returned,?_,rfl,budgetSame⟩
      exact ⟨⟨context.closed,objects,runtimeEnvironment,prefixEnvironment runtimeEnvironment definition.body,
        .signal ⟨definition.returns,false⟩,enteredRep,.body bodyCode,
        .cons (.call caller context.stateRep.shape context.stateRep.nonempty returnCells returnReady)
          continuation,context.checkpoint⟩⟩

theorem invoke_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value signature.resultType))
    (calleeRep : ValueRep program state.heap objects callee)
    (argsPacketRep : PacketRep program state.heap objects arguments (Types.ofList sourceTypes))
    (functionReady : TypeReady registry callee.type)
    (allowed : Static.Allowed .implicit callee.type signature.type)
    (argsReady : ArgumentsReady registry sourceTypes (typesList signature.parameters)) :
    StepRep registry program ⟨.apply (.call signature) (.atom callee :: arguments),stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.call signature) (.atom callee :: arguments),stack,state,entry⟩) := by
  let config : Config Unit EmptyKey := ⟨.apply (.call signature) (.atom callee :: arguments),stack,state,entry⟩
  rcases invoke_total config context calleeRep argsPacketRep functionReady allowed argsReady with
    failed | ⟨after,invoked,represented,sameEntry,sameBudget⟩
  · apply stepRep_source (failure := .panic 0x51)
    · simpa only [Machine.transition,Machine.apply,Datum.asAtom,Bind.bind,Except.bind] using failed
    · rfl
  · apply stepRep_next (after := after)
    · apply step_of_transition
      simpa only [Machine.transition,Machine.apply,Datum.asAtom,Bind.bind,Except.bind] using invoked
    · exact represented
    · exact sameEntry
    · change config.state.materializationRemaining ≤ after.state.materializationRemaining+materializationStepBound
      rw [sameBudget]
      omega

end Solidity.Execution.Safety
