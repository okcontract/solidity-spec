/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Statement
import Solidity.Proofs.Conditions
import Solidity.Storage

namespace Solidity.Compatibility.Storage
open Core Compiler.Validation
open SolidityStorage

inductive Place : Core.Ty → Type where
  | wordField : Nat → Place .word
  | boolField : Nat → Place .bool

def store (variables : Layout) (source : SolidityFunction.Source)
    (input : Contract.Evm.Input) (isStatic : Bool) :
    Core.Store Word.Reference Place Contract.Evm.Stateful.Slots where
  read cells := Word.read (locals variables source input cells)
  write cells := fun {type} place value => if isStatic then none else
    match type, place, value with
    | _, .wordField slot, value => variables.write slot value cells
    | _, .boolField field, value => variables.write field (PackedBool.encode value) cells

mutual
def embedList (checked : Bool) : List Statement → Block Word.Reference Place
  | [] => .skip
  | first :: rest => .seq (embed checked first) (embedList checked rest)
termination_by body => sizeOf body

def embed (checked : Bool) : Statement → Block Word.Reference Place
  | .assign slot value => .assign (.wordField slot) (Word.embed (Conditions.mode checked) value)
  | .assignBool field value => .assign (.boolField field) (Conditions.embed checked value)
  | .ret value => .ret (Word.embed (Conditions.mode checked) value)
  | .stop => .stop
  | .revert => .revert []
  | .branch test yes no => .branch (Conditions.embed checked test)
      (embedList checked yes) (embedList checked no)
termination_by stmt => sizeOf stmt
end

def outcome : SolidityStorage.Outcome → Core.Outcome Contract.Evm.Stateful.Slots
  | .returned bytes cells => .returned bytes cells
  | .reverted bytes => .reverted bytes
  | .fault => .fault

def flow : SolidityStorage.Flow → Core.Flow Contract.Evm.Stateful.Slots
  | .next cells => .next cells
  | .halt result => .halt (outcome result)

mutual
theorem eval_list (body : List Statement) (variables : Layout) (source : SolidityFunction.Source)
    (input : Contract.Evm.Input) (isStatic : Bool) (cells : Contract.Evm.Stateful.Slots) :
    (embedList source.checked body).eval (store variables source input isStatic) .leftFirst cells =
      flow (statements variables source input isStatic body cells) := by
  cases body with
  | nil => simp [embedList, Block.eval, statements, flow]
  | cons first rest =>
      rw [embedList, Block.eval, eval_statement first variables source input isStatic cells, statements]
      cases h : statement variables source input isStatic first cells with
      | next after => exact eval_list rest variables source input isStatic after
      | halt result => rfl
termination_by sizeOf body

theorem eval_statement (stmt : Statement) (variables : Layout) (source : SolidityFunction.Source)
    (input : Contract.Evm.Input) (isStatic : Bool) (cells : Contract.Evm.Stateful.Slots) :
    (embed source.checked stmt).eval (store variables source input isStatic) .leftFirst cells =
      flow (statement variables source input isStatic stmt cells) := by
  cases stmt with
  | assign slot value =>
      simp only [embed, Block.eval, store, Conditions.expression, statement]
      cases SolidityStorage.expression variables source input cells value <;> simp only [flow, outcome]
      case ok word =>
        cases isStatic <;> simp only [Bool.false_eq_true, ↓reduceIte]
        cases variables.write slot word cells <;> rfl
  | assignBool field value =>
      simp only [embed, Block.eval, store, Conditions.eval_embed, statement]
      cases value.eval variables source input cells <;> simp only [flow, outcome]
      case ok word =>
        cases isStatic <;> simp only [Bool.false_eq_true, ↓reduceIte]
        cases variables.write field (PackedBool.encode word) cells <;> rfl
  | ret value =>
      simp only [embed, Block.eval, store, Conditions.expression, statement]
      cases SolidityStorage.expression variables source input cells value <;> rfl
  | stop => simp [embed, Block.eval, statement, flow, outcome]
  | revert => simp [embed, Block.eval, statement, flow, outcome]
  | branch test yes no =>
      simp only [embed, Block.eval, store, Conditions.eval_embed, statement]
      cases test.eval variables source input cells with
      | error bytes => rfl
      | ok value => cases value with
        | false => exact eval_list no variables source input isStatic cells
        | true => exact eval_list yes variables source input isStatic cells
termination_by sizeOf stmt
end

theorem body_result (body : List Statement) (variables : Layout) (source : SolidityFunction.Source)
    (input : Contract.Evm.Input) (isStatic : Bool) (cells : Contract.Evm.Stateful.Slots)
    (fallthrough : List UInt8) :
    (embedList source.checked body).result (store variables source input isStatic)
      .leftFirst cells fallthrough =
      outcome (bodyResult variables source body fallthrough input cells isStatic) := by
  simp only [Block.result, eval_list, bodyResult]
  cases statements variables source input isStatic body cells <;> rfl

/-- Existing exact-artifact trace certificates now have a shared-core consumer.
This transfers the functional observation; gas still comes from that same exact
trace via SolidityStorage.metered, never a source-side gas estimate. -/
theorem certified_body (body : List Statement) (variables : Layout) (source : SolidityFunction.Source)
    (input : Contract.Evm.Input) (isStatic : Bool) (cells : Contract.Evm.Stateful.Slots)
    (fallthrough : List UInt8) (trace : Contract.Evm.Guarded.Trace Contract.Evm.Stateful.Effects)
    (checked : Conforms (bodyResult variables source body fallthrough input cells isStatic) trace) :
    ∃ result, (embedList source.checked body).result (store variables source input isStatic)
      .leftFirst cells fallthrough = outcome result ∧ Conforms result trace :=
  ⟨_, body_result body variables source input isStatic cells fallthrough, checked⟩

/-- The shared-core function evaluator retains the existing ABI guard and
source-derived layout; only its statement interpreter is replaced. -/
def functionResult (variables : Layout) (function : SolidityStorage.Function)
    (input : Contract.Evm.Input) (cells : Contract.Evm.Stateful.Slots) (isStatic : Bool) :
    Core.Outcome Contract.Evm.Stateful.Slots :=
  (embedList function.abi.checked function.body).result
    (store variables function.abi input isStatic) .leftFirst cells
    (if function.returnsWord then Contract.Interaction.wordBytes 0 else [])

def contractOutcome (source : ContractSource) (input : Contract.Evm.Input)
    (cells : Contract.Evm.Stateful.Slots) (isStatic : Bool) : Core.Outcome Contract.Evm.Stateful.Slots :=
  if input.calldata.length = 0 then
    match source.receive with
    | none => .reverted []
    | some receiver =>
      let abi : SolidityFunction.Source :=
        { name := "receive", parameters := [], body := .literal 0, checked := receiver.checked, payable := true }
      (embedList receiver.checked receiver.body).result
        (store source.variables abi input isStatic) .leftFirst cells []
  else if input.calldata.length < 4 then .reverted []
  else match select source input with
    | none => .reverted []
    | some function => if function.call.Accepts input then
        functionResult source.variables function input cells isStatic else .reverted []

theorem contract_outcome (source : ContractSource) (input : Contract.Evm.Input)
    (cells : Contract.Evm.Stateful.Slots) (isStatic : Bool) :
    contractOutcome source input cells isStatic =
      outcome (SolidityStorage.outcome source input cells isStatic) := by
  simp only [contractOutcome, SolidityStorage.outcome]
  split
  · cases h : source.receive with
    | none => simp [emptyOutcome, h, outcome]
    | some receiver =>
        simp only [emptyOutcome, h, Receive.result]
        exact body_result _ _ _ _ _ _ _
  · split
    · rfl
    · cases select source input with
      | none => rfl
      | some function =>
          simp only [SolidityStorage.Function.outcome]
          split
          · exact body_result _ _ _ _ _ _ _
          · rfl

def ConformsCore (expected : Core.Outcome Contract.Evm.Stateful.Slots)
    (trace : Contract.Evm.Guarded.Trace Contract.Evm.Stateful.Effects) : Prop :=
  match expected with
  | .fault => trace = .fault
  | .returned bytes cells => ∃ used needed warm refund,
      trace = .finished used needed ⟨.returned bytes, cells, warm, refund⟩
  | .reverted bytes => ∃ used needed cells warm refund,
      trace = .finished used needed ⟨.reverted bytes, cells, warm, refund⟩

theorem conforms_outcome (expected : SolidityStorage.Outcome)
    (trace : Contract.Evm.Guarded.Trace Contract.Evm.Stateful.Effects) :
    ConformsCore (outcome expected) trace ↔ Conforms expected trace := by cases expected <;> rfl

def TracePreservesCore (source : ContractSource) (code : List UInt8) (steps : Nat) : Prop :=
  ∀ input, SolidityCall.Sized input → ∀ (state : Contract.Evm.Stateful.State)
    (env : Contract.Evm.Stateful.Environment),
    ConformsCore (contractOutcome source input state.storage env.isStatic)
      ((Contract.Evm.Stateful.run code input env steps { state with machine := {} }).map
        Contract.Evm.Stateful.Result.effects)

/-- A complete existing call certificate proves preservation against the shared
core for every sized calldata, persistent store, and static-mode setting. -/
theorem certified_contract (certificate : CallsPreserves source code steps) :
    TracePreservesCore source code steps := by
  intro input sized state env
  rw [contract_outcome, conforms_outcome]
  exact certificate.trace input sized state env

end Solidity.Compatibility.Storage
