/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.SupportedTransfers
import Solidity.Core.Execution.Safety.ConfigurationLaws

/-! Constructive setup of initialized parameters and named results. These
leaves execute the actual conversion/declaration primitives and preserve all
cells, including shadowed cells. No callee behavior or success oracle occurs. -/
namespace Solidity.Execution.Safety.CallSetup
open Static Aggregates
open SupportedTransfers
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem bind_assoc (first : Aggregates.Result α) (second : α → Aggregates.Result β)
    (third : β → Aggregates.Result γ) :
    ((first >>= second) >>= third) = (first >>= fun value => second value >>= third) := by
  cases first <;> rfl

theorem supported_atom (represented : DatumRep program heap objects datum type) (supported : Supported type) :
    ∃ value, datum = .atom value ∧ ValueRep program heap objects value ∧ value.type = type := by
  cases represented with
  | atom value => exact ⟨_,rfl,value,rfl⟩
  | tuple members =>
      rcases supported with scalar | ⟨pointer,equal⟩
      · cases scalar
      · cases equal

theorem prepareArguments_total (program : Program Key) (registry : Registry) (fuel : Nat)
    (state : MachineState σ) (objects : List WordArena.Object) (sources : Packet)
    (ready : ArgumentsReady registry sourceTypes targetTypes)
    (physical : HeapRep state.heap objects)
    (represented : PacketRep program state.heap objects sources (Types.ofList sourceTypes)) :
    ∃ values,
      Machine.prepareArguments registry ⟨fuel+2,none⟩ state targetTypes sources = .ok (values,state) ∧
      PacketRep program state.heap objects values (Types.ofList targetTypes) := by
  induction ready generalizing sources with
  | nil => cases represented; exact ⟨[],rfl,.nil⟩
  | @cons source target sourceTypes targetTypes first rest ih =>
      cases represented with
      | cons head tail =>
          obtain ⟨value,rfl,valueRep,typeEq⟩ := supported_atom head first.1.1
          have permission : TransferReady registry value.type target := by rw [typeEq]; exact first
          obtain ⟨converted,written,convertedRep,convertedType⟩ :=
            bind_total program registry fuel state.materializationRemaining state.heap objects value target
              permission physical valueRep
          obtain ⟨values,convertedTail,tailRep⟩ := ih _ tail
          refine ⟨.atom converted :: values,?_,?_⟩
          · simp [Machine.prepareArguments,Datum.asAtom,Effects.convert,written,convertedTail]
          · exact .cons (by simpa only [convertedType] using DatumRep.atom convertedRep) tailRep

/-- Fresh declaration followed by an actual local assignment fills its
temporary unset cell before returning a machine state. -/
theorem declare_write_total (backend : Backend σ Key) (program : Program Key) (registry : Registry) (fuel : Nat)
    (state : MachineState σ) (objects : List WordArena.Object) (scope : Scope) (outer : Locals)
    (binder : Binder) (source : Value) (shape : state.locals = scope :: outer)
    (fresh : state.locals.find binder.id = none) (ready : TransferReady registry source.type binder.type)
    (physical : HeapRep state.heap objects) (represented : CellsRep program state.heap objects state.locals)
    (sourceRep : ValueRep program state.heap objects source) :
    ∃ value : binder.type.Value,
      (do
        let entered ← Machine.declareUnset state binder
        Machine.writeTarget backend registry ⟨fuel+2,none⟩ entered (.captured (.local binder.id binder.type)) source) =
        .ok {state with locals := ((binder.id,⟨binder.type,some value⟩) :: scope) :: outer} ∧
      CellsRep program state.heap objects (((binder.id,⟨binder.type,some value⟩) :: scope) :: outer) := by
  obtain ⟨value,bound,valueRep,typeEq⟩ :=
    bind_total program registry fuel state.materializationRemaining state.heap objects source binder.type ready physical sourceRep
  rcases value with ⟨type,value⟩
  dsimp only at typeEq
  cases typeEq
  have unset : state.locals.declare binder = .ok (((binder.id,⟨binder.type,none⟩) :: scope) :: outer) := by
    simp only [Locals.declare,fresh,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
      Bind.bind,Except.bind,Pure.pure,Except.pure]
    rw [shape]
  have filled : state.locals.declare binder (some ⟨binder.type,value⟩) =
      .ok (((binder.id,⟨binder.type,some value⟩) :: scope) :: outer) := by
    simp only [Locals.declare,fresh,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
      Bind.bind,Except.bind,Pure.pure,Except.pure]
    rw [shape]
    simp
  refine ⟨value,?_,represented.declare valueRep filled⟩
  simp [Machine.declareUnset,unset,Machine.writeTarget,Effects.writeCaptured,
    Locals.typeOf,Locals.find,Scope.find,bound,Locals.write,Locals.replace,Scope.replace]

theorem bindArguments_total (backend : Backend σ Key) (program : Program Key) (registry : Registry) (fuel : Nat)
    (state : MachineState σ) (objects : List WordArena.Object) (binders : List Binder) (sources : Packet)
    (ready : ArgumentsReady registry sourceTypes (binders.map Binder.type))
    (physical : HeapRep state.heap objects)
    (packet : PacketRep program state.heap objects sources (Types.ofList sourceTypes))
    (represented : CellsRep program state.heap objects state.locals)
    (scope : Scope) (outer : Locals) (shape : state.locals = scope :: outer)
    (fresh : ∀ binder ∈ binders,state.locals.find binder.id = none)
    (distinct : (binders.map Binder.id).Nodup) :
    ∃ locals,
      Machine.bindArguments backend registry ⟨fuel+2,none⟩ state binders sources = .ok {state with locals} ∧
      CellsRep program state.heap objects locals ∧
      Locals.environment locals =
        ((binders.map fun binder => (binder.id,binder.type)).reverse ++ Scope.environment scope) :: Locals.environment outer := by
  induction binders generalizing sourceTypes sources state scope with
  | nil =>
      cases ready
      cases packet
      exact ⟨state.locals,rfl,represented,by simp [shape,Locals.environment]⟩
  | cons binder binders ih =>
      cases ready with
      | cons first rest =>
          cases packet with
          | cons head tail =>
              obtain ⟨value,rfl,valueRep,typeEq⟩ := supported_atom head first.1.1
              have permission : TransferReady registry value.type binder.type := by rw [typeEq]; exact first
              obtain ⟨result,headWrite,headRep⟩ := declare_write_total backend program registry fuel state objects
                scope outer binder value shape (fresh binder (by simp)) permission physical represented valueRep
              let middle : MachineState σ := {state with locals := ((binder.id,⟨binder.type,some result⟩) :: scope) :: outer}
              obtain ⟨absent,tailDistinct⟩ := List.nodup_cons.mp distinct
              have freshTail : ∀ next ∈ binders,middle.locals.find next.id = none := by
                intro next member
                have different : binder.id ≠ next.id := by
                  intro same
                  exact absent (List.mem_map.mpr ⟨next,member,same.symm⟩)
                simp only [middle,Locals.find,Scope.find,different,↓reduceIte]
                simpa only [shape,Locals.find] using fresh next (List.mem_cons_of_mem binder member)
              obtain ⟨locals,bound,cells,environment⟩ := ih middle _ rest physical tail headRep _ rfl freshTail tailDistinct
              refine ⟨locals,?_,cells,?_⟩
              · change (do
                  let entered ← Machine.declareUnset state binder
                  let entered ← Machine.writeTarget backend registry ⟨fuel+2,none⟩ entered
                    (.captured (.local binder.id binder.type)) value
                  Machine.bindArguments backend registry ⟨fuel+2,none⟩ entered binders _) = _
                rw [← bind_assoc,headWrite]
                exact bound
              · simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
                  Scope.environment,List.map_cons] using environment

theorem declareReturn_supported (registry : Registry) (fuel budget : Nat) (locals : Locals)
    (heap : Heap) (binder : Binder) (supported : Supported binder.type) :
    Effects.declareReturn registry fuel budget locals heap binder =
      Effects.declareLocal registry fuel budget locals heap binder none := by
  rcases supported with scalar | ⟨pointer,equal⟩
  · cases binder with
    | mk id type =>
        cases type <;> try rfl
        cases scalar
  · cases binder with
    | mk id type =>
        dsimp only at equal
        subst type
        rfl

/-- A supported named result is initialized through the real default-value
path. Memory arrays use the admitted shared zero slot; no allocation occurs. -/
theorem declareReturn_total (program : Program Key) (registry : Registry) (fuel : Nat)
    (state : MachineState σ) (objects : List WordArena.Object) (scope : Scope) (outer : Locals)
    (binder : Binder) (shape : state.locals = scope :: outer)
    (fresh : state.locals.find binder.id = none) (ready : TypeReady registry binder.type)
    (physical : HeapRep state.heap objects) (represented : CellsRep program state.heap objects state.locals) :
    ∃ value : binder.type.Value,
      Machine.declareReturn registry ⟨fuel+2,none⟩ state binder =
        .ok {state with locals := ((binder.id,⟨binder.type,some value⟩) :: scope) :: outer} ∧
      CellsRep program state.heap objects (((binder.id,⟨binder.type,some value⟩) :: scope) :: outer) := by
  obtain ⟨value,defaulted,valueRep⟩ :=
    defaultLocal_total program registry fuel state.materializationRemaining state.heap objects binder.type ready physical
  have filled : state.locals.declare binder (some ⟨binder.type,value⟩) =
      .ok (((binder.id,⟨binder.type,some value⟩) :: scope) :: outer) := by
    simp only [Locals.declare,fresh,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
      Bind.bind,Except.bind,Pure.pure,Except.pure]
    rw [shape]
    simp
  refine ⟨value,?_,represented.declare valueRep filled⟩
  simp [Machine.declareReturn,declareReturn_supported registry (fuel+2) state.materializationRemaining
    state.locals state.heap binder ready.1,Effects.declareLocal,defaulted,filled]

theorem declareReturns_total (program : Program Key) (registry : Registry) (fuel : Nat)
    (state : MachineState σ) (objects : List WordArena.Object) (binders : List Binder)
    (ready : ∀ binder ∈ binders,TypeReady registry binder.type)
    (physical : HeapRep state.heap objects)
    (represented : CellsRep program state.heap objects state.locals)
    (scope : Scope) (outer : Locals) (shape : state.locals = scope :: outer)
    (fresh : ∀ binder ∈ binders,state.locals.find binder.id = none)
    (distinct : (binders.map Binder.id).Nodup) :
    ∃ locals,
      binders.foldlM (Machine.declareReturn registry ⟨fuel+2,none⟩) state = .ok {state with locals} ∧
      CellsRep program state.heap objects locals ∧
      Locals.environment locals =
        ((binders.map fun binder => (binder.id,binder.type)).reverse ++ Scope.environment scope) :: Locals.environment outer := by
  induction binders generalizing state scope with
  | nil => exact ⟨state.locals,rfl,represented,by simp [shape,Locals.environment]⟩
  | cons binder binders ih =>
      obtain ⟨result,headWrite,headRep⟩ := declareReturn_total program registry fuel state objects scope outer binder
        shape (fresh binder (by simp)) (ready binder (by simp)) physical represented
      let middle : MachineState σ := {state with locals := ((binder.id,⟨binder.type,some result⟩) :: scope) :: outer}
      obtain ⟨absent,tailDistinct⟩ := List.nodup_cons.mp distinct
      have freshTail : ∀ next ∈ binders,middle.locals.find next.id = none := by
        intro next member
        have different : binder.id ≠ next.id := by
          intro same
          exact absent (List.mem_map.mpr ⟨next,member,same.symm⟩)
        simp only [middle,Locals.find,Scope.find,different,↓reduceIte]
        simpa only [shape,Locals.find] using fresh next (List.mem_cons_of_mem binder member)
      obtain ⟨locals,bound,cells,environment⟩ := ih middle
        (fun next member => ready next (by simp [member])) physical headRep _ rfl freshTail tailDistinct
      refine ⟨locals,?_,cells,?_⟩
      · rw [List.foldlM_cons,headWrite]
        exact bound
      · simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
          Scope.environment,List.map_cons] using environment

theorem argumentsReady_self (registry : Registry) (types : List SType)
    (ready : ∀ type ∈ types,TypeReady registry type) : ArgumentsReady registry types types := by
  induction types with
  | nil => exact .nil
  | cons type types ih =>
      exact .cons (self_ready (ready type (by simp)))
        (ih (fun next member => ready next (by simp [member])))

theorem fresh_of_environment (locals : Locals) (scope : List (LocalId × SType)) (key : LocalId)
    (environment : Locals.environment locals = [scope]) (absent : key ∉ scope.map Prod.fst) :
    locals.find key = none := by
  have missing : scope.find? (fun entry => entry.1 == key) = none := by
    apply List.find?_eq_none.mpr
    intro entry member selected
    exact absent (List.mem_map.mpr ⟨entry,member,by simpa using selected⟩)
  have erased := environment_find locals key
  rw [environment] at erased
  simp only [Environment.find,List.flatten_cons,List.flatten_nil,List.append_nil,missing,Option.map_none] at erased
  cases selected : locals.find key with
  | none => rfl
  | some cell => simp [selected] at erased

/-- Concrete parameter and named-result setup from represented arguments.
The returned environment records the physical prepend order. Static function
contexts may use its proved permutation equivalence for distinct binder IDs. -/
theorem initializeFunction_total (backend : Backend Unit EmptyKey) (program : Program EmptyKey) (registry : Registry)
    (fuel : Nat) (state : MachineState Unit) (objects : List WordArena.Object)
    (parameters returns : List Binder) (arguments : Packet)
    (ready : ∀ binder ∈ parameters ++ returns,TypeReady registry binder.type)
    (physical : HeapRep state.heap objects)
    (packet : PacketRep program state.heap objects arguments (Types.ofList (parameters.map Binder.type)))
    (distinct : ((parameters ++ returns).map Binder.id).Nodup) :
    ∃ bound entered,
      Machine.bindArguments backend registry ⟨fuel+2,none⟩
        {state with locals := Locals.empty, mode := .checked} parameters arguments = .ok bound ∧
      returns.foldlM (Machine.declareReturn registry ⟨fuel+2,none⟩) bound = .ok entered ∧
      StateRep program objects [((parameters ++ returns).map fun binder => (binder.id,binder.type)).reverse] entered ∧
      entered.external = state.external ∧ entered.heap = state.heap ∧ entered.mode = .checked ∧
      entered.materializationRemaining = state.materializationRemaining := by
  let initial : MachineState Unit := {state with locals := Locals.empty, mode := .checked}
  have parameterTypes : ∀ type ∈ parameters.map Binder.type,TypeReady registry type := by
    intro type member
    obtain ⟨binder,binderMember,rfl⟩ := List.mem_map.mp member
    exact ready binder (List.mem_append_left _ binderMember)
  have initialCells : CellsRep program initial.heap objects initial.locals := by
    intro scope member entry found
    simp only [initial,Locals.empty,List.mem_singleton] at member
    subst scope
    cases found
  have splitDistinct := distinct
  simp only [List.map_append,List.nodup_append] at splitDistinct
  obtain ⟨locals,bound,cells,environment⟩ := bindArguments_total backend program registry fuel initial objects parameters arguments
    (argumentsReady_self registry _ parameterTypes) physical packet initialCells [] [] rfl
    (by intros; rfl) splitDistinct.1
  let middle : MachineState Unit := {initial with locals}
  have freshReturns : ∀ binder ∈ returns,middle.locals.find binder.id = none := by
    intro binder member
    apply fresh_of_environment locals ((parameters.map fun binder => (binder.id,binder.type)).reverse) binder.id
    · simpa only [Scope.environment,List.map_nil,List.append_nil,Locals.environment] using environment
    · intro selected
      have selected : binder.id ∈ parameters.map Binder.id := by
        simpa only [List.map_reverse,List.mem_reverse,List.map_map,Function.comp_def] using selected
      exact splitDistinct.2.2 binder.id selected binder.id (List.mem_map.mpr ⟨binder,member,rfl⟩) rfl
  cases current : locals with
  | nil =>
      simp only [current,Locals.environment,List.map_nil] at environment
      cases environment
  | cons scope outer =>
      obtain ⟨finished,returned,finishedCells,finishedEnvironment⟩ := declareReturns_total program registry fuel middle objects returns
        (fun binder member => ready binder (by simp [member])) physical cells scope outer
        (by simp only [middle,current]) freshReturns splitDistinct.2.1
      refine ⟨middle,{middle with locals := finished},bound,returned,?_,rfl,rfl,rfl,rfl⟩
      refine ⟨physical,finishedCells,?_,?_⟩
      · have startEnvironment := environment
        rw [current] at startEnvironment
        simp only [Locals.environment,List.map_cons] at startEnvironment
        have outerEmpty : outer = [] := by
          have rest := congrArg List.tail startEnvironment
          simp only [List.tail_cons] at rest
          cases outer with
          | nil => rfl
          | cons first rest => cases rest
        subst outer
        simp only [List.map_nil,List.cons.injEq] at startEnvironment
        have scopeEnvironment : Scope.environment scope =
            (parameters.map fun binder => (binder.id,binder.type)).reverse := by
          simpa only [Scope.environment,List.map_nil,List.append_nil] using startEnvironment.1
        rw [scopeEnvironment] at finishedEnvironment
        simpa only [List.map_append,List.reverse_append,Locals.environment,List.map_nil] using finishedEnvironment
      · intro empty
        change finished = [] at empty
        have bad := congrArg List.length finishedEnvironment
        rw [empty] at bad
        simp only [Locals.environment,List.map_nil,List.length_nil,List.length_cons] at bad
        omega

end Solidity.Execution.Safety.CallSetup
