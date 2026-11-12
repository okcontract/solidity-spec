/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Blocks
import Solidity.Proofs.Initialization
import Solidity.Proofs.Clients

/-! Existing statement, initializer and pure-client certificates consume actual
shared-machine executions. Source admission/dispatch remains the existing
explicit wrapper; these bridges do not assert a new ABI or lowering theorem. -/
namespace Solidity.Execution.Compatibility
open Core Static

def flowResult (fallthrough : List UInt8) : Core.Flow State → Core.Outcome State
  | .next after => .returned fallthrough after
  | .halt result => result

def blockResultObservation (fallthrough : List UInt8) (observed : Observation State) : Option (Core.Outcome State) :=
  (blockObservation observed).map (flowResult fallthrough)

theorem block_result_machine (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (body : Core.Block Ref Place)
    (fallthrough : List UInt8) :
    ∃ observed, Executes (transition (Compatibility.backend store) registry program)
      (Config.start state (blockBody body)) observed ∧
      blockResultObservation fallthrough observed = some (body.result store .leftFirst state.external fallthrough) := by
  obtain ⟨observed, executed, represented⟩ := block_machine store registry program state body
  refine ⟨observed, executed, ?_⟩
  rw [blockResultObservation, represented]
  simp only [Core.Block.result]
  cases body.eval store .leftFirst state.external <;> rfl

theorem block_result_run (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (body : Core.Block Ref Place)
    (fallthrough : List UInt8) :
    ∃ fuel choices observed, Machine.execute (Compatibility.backend store) registry legacyLimits program fuel choices
      (Config.start state (blockBody body)) = .finished observed ∧
      blockResultObservation fallthrough observed = some (body.result store .leftFirst state.external fallthrough) := by
  obtain ⟨observed, executed, represented⟩ := block_result_machine store registry program state body fallthrough
  obtain ⟨fuel, choices, completed⟩ := Solidity.Execution.run_complete _ executed
  exact ⟨fuel, choices, observed, completed, represented⟩

end Solidity.Execution.Compatibility

namespace Solidity.Compatibility.Storage
open Core Execution Static Compiler.Validation SolidityStorage
open Execution.Compatibility

/-- All existing checked/unchecked storage statements use the same machine,
including forbidden static writes, which remain exceptional halts. -/
theorem body_machine (body : List Statement) (variables : Layout) (source : SolidityFunction.Source)
    (input : Contract.Evm.Input) (isStatic : Bool) (state : MachineState Contract.Evm.Stateful.Slots)
    (registry : Registry) (program : Program (Key Word.Reference Place)) (fallthrough : List UInt8) :
    ∃ observed, Executes (transition (backend (store variables source input isStatic)) registry program)
      (Config.start state (blockBody (embedList source.checked body))) observed ∧
      blockResultObservation fallthrough observed =
        some (outcome (bodyResult variables source body fallthrough input state.external isStatic)) := by
  obtain ⟨observed, executed, represented⟩ := block_result_machine (store variables source input isStatic)
    registry program state (embedList source.checked body) fallthrough
  exact ⟨observed, executed, represented.trans (congrArg some (body_result body variables source input isStatic state.external fallthrough))⟩

theorem function_machine (variables : Layout) (function : SolidityStorage.Function)
    (input : Contract.Evm.Input) (isStatic : Bool) (state : MachineState Contract.Evm.Stateful.Slots)
    (registry : Registry) (program : Program (Key Word.Reference Place)) :
    ∃ observed, Executes (transition (backend (store variables function.abi input isStatic)) registry program)
      (Config.start state (blockBody (embedList function.abi.checked function.body))) observed ∧
      blockResultObservation (if function.returnsWord then Contract.Interaction.wordBytes 0 else []) observed =
        some (functionResult variables function input state.external isStatic) :=
  block_result_machine _ registry program state _ _

/-- The exact trace's gas, frame, warmth and refund observations remain in the
original certificate; the extra conjunct supplies an actual shared execution. -/
theorem certified_body_machine (body : List Statement) (variables : Layout) (source : SolidityFunction.Source)
    (input : Contract.Evm.Input) (isStatic : Bool) (state : MachineState Contract.Evm.Stateful.Slots)
    (registry : Registry) (program : Program (Key Word.Reference Place)) (fallthrough : List UInt8)
    (trace : Contract.Evm.Guarded.Trace Contract.Evm.Stateful.Effects)
    (checked : Conforms (bodyResult variables source body fallthrough input state.external isStatic) trace) :
    ∃ observed, Executes (transition (backend (store variables source input isStatic)) registry program)
      (Config.start state (blockBody (embedList source.checked body))) observed ∧
      blockResultObservation fallthrough observed =
        some (outcome (bodyResult variables source body fallthrough input state.external isStatic)) ∧
      Conforms (bodyResult variables source body fallthrough input state.external isStatic) trace := by
  obtain ⟨observed, executed, represented⟩ := body_machine body variables source input isStatic state registry program fallthrough
  exact ⟨observed, executed, represented, checked⟩

theorem initializers_machine (variables : Layout) (initializers : List Initialization.Initializer)
    (state : MachineState Contract.Evm.Stateful.Slots) (registry : Registry)
    (program : Program (Key Word.Reference Place)) :
    ∃ observed, Executes (transition (backend (store variables
        {name := "constructor", parameters := [], body := .literal 0, checked := true} {} false)) registry program)
      (Config.start state (blockBody (initializerBlock initializers))) observed ∧
      (blockObservation observed).map initializerResult = some (Initialization.evaluate variables initializers state.external) := by
  obtain ⟨observed, executed, represented⟩ := block_machine (store variables
      {name := "constructor", parameters := [], body := .literal 0, checked := true} {} false)
    registry program state (initializerBlock initializers)
  refine ⟨observed, executed, ?_⟩
  rw [represented, ← initializers_eval]
  rfl

theorem certified_contract_machine (source : ContractSource) (code : List UInt8) (steps : Nat)
    (certificate : CallsPreserves source code steps) (registry : Registry)
    (program : Program (Key Word.Reference Place)) :
    TracePreservesCore source code steps ∧
      ∀ function ∈ source.functions, ∀ input isStatic (state : MachineState Contract.Evm.Stateful.Slots),
        ∃ observed, Executes (transition (backend (store source.variables function.abi input isStatic)) registry program)
          (Config.start state (blockBody (embedList function.abi.checked function.body))) observed ∧
          blockResultObservation (if function.returnsWord then Contract.Interaction.wordBytes 0 else []) observed =
            some (functionResult source.variables function input state.external isStatic) :=
  ⟨certified_contract certificate, fun function _ input isStatic state =>
    function_machine source.variables function input isStatic state registry program⟩

theorem certified_initialization_machine (source : ContractSource) (initializers : List Initialization.Initializer)
    (certificate : Initialization.Preserves source initializers creation runtime creationSteps runtimeSteps)
    (registry : Registry) (program : Program (Key Word.Reference Place)) :
    InitializationPreservesCore source initializers creation runtime creationSteps runtimeSteps ∧
      ∀ state : MachineState Contract.Evm.Stateful.Slots,
        ∃ observed, Executes (transition (backend (store source.variables
            {name := "constructor", parameters := [], body := .literal 0, checked := true} {} false)) registry program)
          (Config.start state (blockBody (initializerBlock initializers))) observed ∧
          (blockObservation observed).map initializerResult = some (Initialization.evaluate source.variables initializers state.external) :=
  ⟨certified_initialization certificate, fun state => initializers_machine source.variables initializers state registry program⟩

/-- Constructor certificate composition retains the admission, initializer,
installation and runtime-call conjuncts. Its actual statement body executes in
the same shared machine after the separately checked initializer phase. -/
theorem certified_constructor_machine (source : ContractSource) (initializers : List Initialization.Initializer)
    (body : Constructor.Body)
    (certificate : Constructor.Preserves source initializers body creation runtime creationSteps runtimeSteps)
    (registry : Registry) (program : Program (Key Word.Reference Place)) :
    ConstructorPreservesCore source initializers body creation runtime creationSteps runtimeSteps ∧
      (∀ state : MachineState Contract.Evm.Stateful.Slots,
        ∃ observed, Executes (transition (backend (store source.variables
            {name := "constructor", parameters := [], body := .literal 0, checked := true} {} false)) registry program)
          (Config.start state (blockBody (initializerBlock initializers))) observed ∧
          (blockObservation observed).map initializerResult = some (Initialization.evaluate source.variables initializers state.external)) ∧
      (∀ input (state : MachineState Contract.Evm.Stateful.Slots),
        ∃ observed, Executes (transition (backend (store source.variables
            {name := "constructor", parameters := [], body := .literal 0, checked := body.checked} input false)) registry program)
          (Config.start state (blockBody (embedList body.checked body.statements))) observed ∧
          blockResultObservation [] observed = some (outcome (bodyResult source.variables
            {name := "constructor", parameters := [], body := .literal 0, checked := body.checked}
            body.statements [] input state.external false))) :=
  ⟨certified_constructor certificate,
    (fun state => initializers_machine source.variables initializers state registry program),
    (fun input state => body_machine body.statements source.variables
      {name := "constructor", parameters := [], body := .literal 0, checked := body.checked}
      input false state registry program [])⟩

end Solidity.Compatibility.Storage

namespace Solidity.Compatibility.Clients
open Core Execution Static Compiler.Validation
open Execution.Compatibility

def expressionStore (source : SolidityFunction.Source) (input : Contract.Evm.Input) :
    Core.Store Word.Reference (fun _ => Empty) Unit where
  read _ := Word.read (source.locals input)
  write _ := fun {_} place _ => nomatch place

def callBlock (source : SolidityFunction.Source) (input : Contract.Evm.Input) :
    Core.Block Word.Reference (fun _ => Empty) :=
  if SolidityCall.Accepts source input then .ret (Word.embed (Conditions.mode source.checked) source.body)
  else .revert []

theorem callBlock_result (source : SolidityFunction.Source) (input : Contract.Evm.Input) :
    (callBlock source input).result (expressionStore source input) .leftFirst () [] = coreHalt (SolidityCall.outcome source input) := by
  rw [← call_outcome]
  simp only [callBlock, callOutcome]
  split
  · simp only [Core.Block.result, Core.Block.eval, expressionStore, functionResult]
    cases (Word.embed (Conditions.mode source.checked) source.body).eval (Word.read (source.locals input)) .leftFirst <;> rfl
  · rfl

/-- The existing ABI guard selects either the translated return expression or
an explicit empty revert. The target never invokes the compatibility evaluator. -/
theorem call_machine (source : SolidityFunction.Source) (input : Contract.Evm.Input)
    (state : MachineState Unit) (registry : Registry)
    (program : Program (Key Word.Reference (fun _ => Empty))) :
    ∃ observed, Executes (transition (backend (expressionStore source input)) registry program)
      (Config.start state (blockBody (callBlock source input))) observed ∧
      blockResultObservation [] observed = some (coreHalt (SolidityCall.outcome source input)) := by
  obtain ⟨observed, executed, represented⟩ := block_result_machine (expressionStore source input) registry program state (callBlock source input) []
  have unit : state.external = () := rfl
  rw [unit, callBlock_result] at represented
  exact ⟨observed, executed, represented⟩

theorem certified_call_machine (source : SolidityFunction.Source) (code : List UInt8) (steps : Nat)
    (certificate : SolidityCall.Preserves source code steps) (registry : Registry)
    (program : Program (Key Word.Reference (fun _ => Empty))) :
    CallPreservesCore source code steps ∧ ∀ input (state : MachineState Unit),
      ∃ observed, Executes (transition (backend (expressionStore source input)) registry program)
        (Config.start state (blockBody (callBlock source input))) observed ∧
        blockResultObservation [] observed = some (coreHalt (SolidityCall.outcome source input)) :=
  ⟨certified_call certificate, fun input state => call_machine source input state registry program⟩

def terminalBlock (word : Option (BitVec 256)) : Core.Block Word.Reference (fun _ => Empty) :=
  match word with | none => .stop | some value => .ret (.literal value)

def terminalStore : Core.Store Word.Reference (fun _ => Empty) Unit :=
  expressionStore {name := "terminal", parameters := [], body := .literal 0} {}

theorem terminalBlock_result (word : Option (BitVec 256)) :
    (terminalBlock word).result terminalStore .leftFirst () [] = .returned (terminalBytes word) () := by
  cases word <;> rfl

theorem terminal_machine (word : Option (BitVec 256)) (state : MachineState Unit) (registry : Registry)
    (program : Program (Key Word.Reference (fun _ => Empty))) :
    ∃ observed, Executes (transition (backend terminalStore) registry program)
      (Config.start state (blockBody (terminalBlock word))) observed ∧
      blockResultObservation [] observed = some (terminal word) := by
  obtain ⟨observed, executed, represented⟩ := block_result_machine terminalStore registry program state (terminalBlock word) []
  have unit : state.external = () := rfl
  rw [unit, terminalBlock_result, ← terminal_result] at represented
  exact ⟨observed, executed, represented⟩

def deploymentBlock (input : Contract.Evm.Input) : Core.Block Word.Reference (fun _ => Empty) :=
  if input.value = 0#256 then .skip else .revert []

theorem deploymentBlock_result (runtime : List UInt8) (input : Contract.Evm.Input) :
    (deploymentBlock input).result terminalStore .leftFirst () runtime =
      coreHalt (SolidityDeployment.outcome runtime input) := by
  simp only [deploymentBlock, SolidityDeployment.outcome]
  split <;> rfl

theorem deployment_machine (runtime : List UInt8) (input : Contract.Evm.Input)
    (state : MachineState Unit) (registry : Registry) (program : Program (Key Word.Reference (fun _ => Empty))) :
    ∃ observed, Executes (transition (backend terminalStore) registry program)
      (Config.start state (blockBody (deploymentBlock input))) observed ∧
      blockResultObservation runtime observed = some (coreHalt (SolidityDeployment.outcome runtime input)) := by
  obtain ⟨observed, executed, represented⟩ := block_result_machine terminalStore registry program state (deploymentBlock input) runtime
  have unit : state.external = () := rfl
  rw [unit, deploymentBlock_result] at represented
  exact ⟨observed, executed, represented⟩

theorem certified_contract_machine (sources : List SolidityFunction.Source)
    (certificate : SolidityContract.Preserves sources creation runtime creationSteps runtimeSteps)
    (registry : Registry) (program : Program (Key Word.Reference (fun _ => Empty))) :
    ContractPreservesCore sources creation runtime creationSteps runtimeSteps ∧
      (∀ source ∈ sources, ∀ input (state : MachineState Unit),
        ∃ observed, Executes (transition (backend (expressionStore source input)) registry program)
          (Config.start state (blockBody (callBlock source input))) observed ∧
          blockResultObservation [] observed = some (coreHalt (SolidityCall.outcome source input))) ∧
      (∀ input (state : MachineState Unit),
        ∃ observed, Executes (transition (backend terminalStore) registry program)
          (Config.start state (blockBody (deploymentBlock input))) observed ∧
          blockResultObservation runtime observed = some (coreHalt (SolidityDeployment.outcome runtime input))) :=
  ⟨certified_contract certificate, (fun source _ input state => call_machine source input state registry program),
    (fun input state => deployment_machine runtime input state registry program)⟩

def methodStore (method : SolidityMethodContract.Method) (input : Contract.Evm.Input) :
    Core.Store Word.Reference (fun _ => Empty) Unit :=
  match method with | .expression source => expressionStore source input | _ => terminalStore

def methodBlock (method : SolidityMethodContract.Method) (input : Contract.Evm.Input) :
    Core.Block Word.Reference (fun _ => Empty) :=
  match method with
  | .expression source => callBlock source input
  | .empty source => if source.Accepts input then terminalBlock none else .revert []
  | .rawWord source value => if source.Accepts input then terminalBlock (some value) else .revert []

theorem methodBlock_result (method : SolidityMethodContract.Method) (input : Contract.Evm.Input) :
    (methodBlock method input).result (methodStore method input) .leftFirst () [] =
      coreHalt (method.outcome input) := by
  cases method with
  | expression source => exact callBlock_result source input
  | empty source =>
      rw [← method_outcome]
      simp only [methodBlock, methodStore, methodOutcome]
      split <;> rfl
  | rawWord source value =>
      rw [← method_outcome]
      simp only [methodBlock, methodStore, methodOutcome]
      split <;> rfl

theorem method_machine (method : SolidityMethodContract.Method) (input : Contract.Evm.Input)
    (state : MachineState Unit) (registry : Registry) (program : Program (Key Word.Reference (fun _ => Empty))) :
    ∃ observed, Executes (transition (backend (methodStore method input)) registry program)
      (Config.start state (blockBody (methodBlock method input))) observed ∧
      blockResultObservation [] observed = some (coreHalt (method.outcome input)) := by
  obtain ⟨observed, executed, represented⟩ := block_result_machine (methodStore method input)
    registry program state (methodBlock method input) []
  have unit : state.external = () := rfl
  rw [unit, methodBlock_result] at represented
  exact ⟨observed, executed, represented⟩

theorem certified_methods_machine (methods : List SolidityMethodContract.Method)
    (certificate : SolidityMethodContract.Preserves methods creation runtime creationSteps runtimeSteps)
    (registry : Registry) (program : Program (Key Word.Reference (fun _ => Empty))) :
    MethodsPreservesCore methods creation runtime creationSteps runtimeSteps ∧
      ∀ method ∈ methods, ∀ input (state : MachineState Unit),
        ∃ observed, Executes (transition (backend (methodStore method input)) registry program)
          (Config.start state (blockBody (methodBlock method input))) observed ∧
          blockResultObservation [] observed = some (coreHalt (method.outcome input)) :=
  ⟨certified_methods certificate, fun method _ input state => method_machine method input state registry program⟩

end Solidity.Compatibility.Clients
