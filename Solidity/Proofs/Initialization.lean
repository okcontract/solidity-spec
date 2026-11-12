/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Proofs.Storage
import Solidity.StorageConstructor

namespace Solidity.Compatibility.Storage
open Core Compiler.Validation SolidityStorage Contract.Evm

private def initializerABI : SolidityFunction.Source :=
  { name := "constructor", parameters := [], body := .literal 0, checked := true }

def initializerBlock : List Initialization.Initializer → Core.Block Word.Reference Place
  | [] => .skip
  | (slot, expr) :: rest => .seq
      (.assign (.wordField slot) (Word.embed .checked expr)) (initializerBlock rest)

/-- The compatibility initializer model rejects an invalid declaration index with
empty revert data. Normalize only this interface's write rejection; ordinary
static write faults retain their exceptional-halt meaning. -/
def initializerResult : Core.Flow Stateful.Slots → Except (List UInt8) Stateful.Slots
  | .next cells => .ok cells
  | .halt (.reverted bytes) => .error bytes
  | .halt .fault => .error []
  | .halt (.returned _ cells) => .ok cells

def runInitializers (variables : Layout) (initializers : List Initialization.Initializer)
    (cells : Stateful.Slots) : Except (List UInt8) Stateful.Slots :=
  initializerResult ((initializerBlock initializers).eval
    (store variables initializerABI {} false) .leftFirst cells)

theorem initializers_eval (variables : Layout) (initializers : List Initialization.Initializer)
    (cells : Stateful.Slots) :
    runInitializers variables initializers cells = Initialization.evaluate variables initializers cells := by
  induction initializers generalizing cells with
  | nil => rfl
  | cons first rest ih =>
      rcases first with ⟨slot, expr⟩
      simp only [runInitializers, initializerBlock, Core.Block.eval, store, Word.checked,
        Initialization.evaluate, initializerABI]
      cases h : expr.evalChecked (locals variables
        { name := "constructor", parameters := [], body := .literal 0, checked := true } {} cells) with
      | error bytes => rfl
      | ok value =>
          simp only [bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
          cases variables.write slot value cells with
          | none => rfl
          | some after => exact ih after

def initializationOutcome (variables : Layout) (initializers : List Initialization.Initializer)
    (input : Input) : Core.Outcome Stateful.Slots :=
  if input.value = 0#256 then
    match runInitializers variables initializers (fun _ => 0) with
    | .ok cells => .returned [] cells
    | .error bytes => .reverted bytes
  else .reverted []

theorem initialization_outcome (variables : Layout) (initializers : List Initialization.Initializer)
    (input : Input) : initializationOutcome variables initializers input =
      outcome (Initialization.source variables initializers input) := by
  simp only [initializationOutcome, initializers_eval, Initialization.source,
    Initialization.result]
  split
  · cases Initialization.evaluate variables initializers (fun _ => 0) <;> rfl
  · rfl

def constructorOutcome (variables : Layout) (initializers : List Initialization.Initializer)
    (body : Constructor.Body) (input : Input) : Core.Outcome Stateful.Slots :=
  if !body.payable && input.value != 0#256 then .reverted [] else
    match runInitializers variables initializers (fun _ => 0) with
    | .error bytes => .reverted bytes
    | .ok cells =>
      match (embedList body.checked body.statements).eval (store variables
          { name := "constructor", parameters := [], body := .literal 0, checked := body.checked }
          input false) .leftFirst cells with
      | .next after | .halt (.returned _ after) => .returned [] after
      | .halt result => result

theorem constructor_outcome (variables : Layout) (initializers : List Initialization.Initializer)
    (body : Constructor.Body) (input : Input) : constructorOutcome variables initializers body input =
      outcome (Constructor.result variables initializers body input) := by
  simp only [constructorOutcome, Constructor.result, initializers_eval]
  split
  · rfl
  · cases Initialization.evaluate variables initializers (fun _ => 0) with
    | error bytes => rfl
    | ok cells =>
        dsimp only
        rw [eval_list body.statements variables
          { name := "constructor", parameters := [], body := .literal 0, checked := body.checked }
          input false cells]
        cases statements variables
          { name := "constructor", parameters := [], body := .literal 0, checked := body.checked }
          input false body.statements cells with
        | next after => rfl
        | halt result => cases result <;> rfl

/-- Inverse projection lets the existing complete creation/frame/gas certificate
consume the new core evaluator without weakening any of its conjuncts. -/
def legacyOutcome : Core.Outcome Stateful.Slots → SolidityStorage.Outcome
  | .returned bytes cells => .returned bytes cells
  | .reverted bytes => .reverted bytes
  | .fault => .fault

@[simp] theorem legacy_outcome (result : SolidityStorage.Outcome) : legacyOutcome (outcome result) = result := by
  cases result <;> rfl

def ConstructorPreservesCore (source : ContractSource) (initializers : List Initialization.Initializer)
    (body : Constructor.Body) :=
  Creation.Preserves source (fun input => legacyOutcome (constructorOutcome source.variables initializers body input))

theorem certified_constructor (certificate : Constructor.Preserves source initializers body creation runtime creationSteps runtimeSteps) :
    ConstructorPreservesCore source initializers body creation runtime creationSteps runtimeSteps := by
  simpa only [ConstructorPreservesCore, Constructor.Preserves, constructor_outcome, legacy_outcome] using certificate

def InitializationPreservesCore (source : ContractSource) (initializers : List Initialization.Initializer) :=
  Creation.Preserves source (fun input => legacyOutcome (initializationOutcome source.variables initializers input))

theorem certified_initialization (certificate : Initialization.Preserves source initializers creation runtime creationSteps runtimeSteps) :
    InitializationPreservesCore source initializers creation runtime creationSteps runtimeSteps := by
  simpa only [InitializationPreservesCore, Initialization.Preserves, initialization_outcome, legacy_outcome] using certificate

end Solidity.Compatibility.Storage
