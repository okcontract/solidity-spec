/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.StaticABI
import Solidity.Core.Statement
import Solidity.Proofs.Word
import Solidity.Proofs.Conditions
import Solidity.MethodContract
import Solidity.BoolLiteral
import Solidity.AddressLiteral
import Solidity.Bytes32Literal
import Solidity.EmptyContract

namespace Solidity.Compatibility.Clients
open Core Compiler.Validation Contract.Evm

/-- These are source ABI types; padding checks are shared with the typed core. -/
def parameterType : SolidityABI.Parameter → Core.Ty
  | .word => .word | .bytes4 => .fixedBytes 3 | .boolean => .bool

theorem parameter_accepts (parameter : SolidityABI.Parameter) (word : BitVec 256) :
    StaticABI.Canonical (parameterType parameter) word ↔ parameter.Accepts word := by
  cases parameter with
  | word => exact iff_true_intro word.isLt
  | bytes4 => rfl
  | boolean => rfl

theorem parameter_decode (parameter : SolidityABI.Parameter) (word : BitVec 256) :
    (StaticABI.decode (parameterType parameter) word).isSome = true ↔ parameter.Accepts word := by
  rw [StaticABI.decode_accepts, parameter_accepts]

/-- Evaluate the expression in the shared core before applying its ABI return
encoding. Failure carries the original panic bytes. -/
def functionResult (source : SolidityFunction.Source) (input : Input) : Halt :=
  match (Word.embed (Conditions.mode source.checked) source.body).eval
      (Word.read (source.locals input)) .leftFirst with
  | .ok value => .returned (Contract.Interaction.wordBytes value)
  | .error bytes => .reverted bytes

theorem function_result (source : SolidityFunction.Source) (input : Input) :
    functionResult source input = source.result input := by
  unfold functionResult SolidityFunction.Source.result Conditions.mode
  cases source.checked <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [Word.unchecked]; rfl
  · rw [Word.checked]; rfl

def callOutcome (source : SolidityFunction.Source) (input : Input) : Halt :=
  if SolidityCall.Accepts source input then functionResult source input else .reverted []

theorem call_outcome (source : SolidityFunction.Source) (input : Input) :
    callOutcome source input = SolidityCall.outcome source input := by
  simp only [callOutcome, function_result, SolidityCall.outcome]

private def emptyStore : Core.Store (fun _ => Empty) (fun _ => Empty) Unit where
  read _ := fun {_type} ref => nomatch ref
  write _ := fun {_type} ref _ => nomatch ref

/-- Terminal empty/raw-word bodies also execute a core block. `none` denotes
an impossible fault here; it is never equated with source reversion. -/
def terminal (word : Option (BitVec 256)) : Core.Outcome Unit :=
  (match word with
    | none => Core.Block.stop
    | some value => Core.Block.ret (.literal value)).result emptyStore .leftFirst () []

def terminalBytes (word : Option (BitVec 256)) : List UInt8 :=
  match word with | none => [] | some value => Contract.Interaction.wordBytes value

theorem terminal_result (word : Option (BitVec 256)) :
    terminal word = .returned (terminalBytes word) () := by cases word <;> rfl

def typedTerminal (source : SolidityABI.Source) (word : Option (BitVec 256)) (input : Input) : Core.Outcome Unit :=
  if source.Accepts input then terminal word else .reverted []

def coreHalt : Halt → Core.Outcome Unit
  | .returned bytes => .returned bytes ()
  | .reverted bytes => .reverted bytes

theorem empty_result (source : SolidityABI.Source) (input : Input) :
    typedTerminal source none input = coreHalt (SolidityNoReturn.outcome source input) := by
  simp only [typedTerminal, terminal_result, terminalBytes, SolidityNoReturn.outcome]
  split <;> rfl

theorem raw_result (source : SolidityABI.Source) (value : BitVec 256) (input : Input) :
    typedTerminal source (some value) input = coreHalt (SolidityRawReturn.outcome source value input) := by
  simp only [typedTerminal, terminal_result, terminalBytes, SolidityRawReturn.outcome,
    SolidityRawReturn.bytes_eq, SolidityNoReturn.returning]
  split <;> rfl

/-- Independent core-derived body results, with exactly the existing admission.
All literal-return specializations use `functionResult`; raw and empty methods
have the block correspondence above. -/
def methodOutcome : SolidityMethodContract.Method → Input → Halt
  | .expression source, input => callOutcome source input
  | .empty source, input => if source.Accepts input then .returned (terminalBytes none) else .reverted []
  | .rawWord source value, input => if source.Accepts input then .returned (terminalBytes (some value)) else .reverted []

theorem method_outcome (method : SolidityMethodContract.Method) (input : Input) :
    methodOutcome method input = method.outcome input := by
  cases method with
  | expression source => exact call_outcome source input
  | empty source => rfl
  | rawWord source value => simp only [methodOutcome, SolidityMethodContract.Method.outcome,
      SolidityRawReturn.outcome, SolidityNoReturn.returning, SolidityRawReturn.bytes_eq, terminalBytes]

abbrev MethodsPreservesCore := SolidityDispatch.Preserves
  SolidityMethodContract.Method.selector methodOutcome SolidityMethodContract.Method.ValidCall

theorem certified_methods (certificate : SolidityMethodContract.Preserves methods creation runtime creationSteps runtimeSteps) :
    MethodsPreservesCore methods creation runtime creationSteps runtimeSteps := by
  have same : methodOutcome = SolidityMethodContract.Method.outcome := funext fun method => funext (method_outcome method)
  simpa only [MethodsPreservesCore, same] using certificate

/-- Retain the complete original single-call certificate, together with the
core-derived outcome equality for all inputs. Gas/frame conjuncts are retained. -/
def CallPreservesCore (source : SolidityFunction.Source) (code : List UInt8) (steps : Nat) : Prop :=
  SolidityCall.Preserves source code steps ∧ ∀ input, callOutcome source input = SolidityCall.outcome source input

theorem certified_call (certificate : SolidityCall.Preserves source code steps) : CallPreservesCore source code steps :=
  ⟨certificate, call_outcome source⟩

/-- Complete pure-contract dispatch uses the same core-evaluated functions. -/
def contractOutcome (sources : List SolidityFunction.Source) (input : Input) : Halt :=
  if input.calldata.length < 4 then .reverted [] else
    match SolidityContract.select sources input with
    | none => .reverted []
    | some source => callOutcome source input

theorem contract_outcome (sources : List SolidityFunction.Source) (input : Input) :
    contractOutcome sources input = SolidityContract.outcome sources input := by
  simp only [contractOutcome, SolidityContract.outcome]
  split
  · rfl
  · cases SolidityContract.select sources input with
    | none => rfl
    | some source => exact call_outcome source input

def deploymentOutcome (runtime : List UInt8) (input : Input) : Core.Outcome Unit :=
  if input.value = 0#256 then
    Core.Block.skip.result emptyStore .leftFirst () runtime
  else (Core.Block.revert []).result emptyStore .leftFirst () []

theorem deployment_outcome (runtime : List UInt8) (input : Input) :
    deploymentOutcome runtime input = coreHalt (SolidityDeployment.outcome runtime input) := by
  simp only [deploymentOutcome, SolidityDeployment.outcome]
  split <;> rfl

theorem empty_contract_outcome (input : Input) :
    coreHalt (contractOutcome [] input) =
      (Core.Block.revert []).result emptyStore .leftFirst () [] := by
  rw [contract_outcome, SolidityEmptyContract.outcome_empty]
  rfl

/-- These adapters retain every old certificate conjunct. The additional
universal correspondence binds its source outcomes to the shared core. -/
def ContractPreservesCore (sources : List SolidityFunction.Source) (creation runtime : List UInt8)
    (creationSteps runtimeSteps : Nat) : Prop :=
  SolidityContract.Preserves sources creation runtime creationSteps runtimeSteps ∧
  (∀ input, contractOutcome sources input = SolidityContract.outcome sources input) ∧
  (∀ input, deploymentOutcome runtime input = coreHalt (SolidityDeployment.outcome runtime input))

theorem certified_contract (certificate : SolidityContract.Preserves sources creation runtime creationSteps runtimeSteps) :
    ContractPreservesCore sources creation runtime creationSteps runtimeSteps :=
  ⟨certificate, contract_outcome sources, deployment_outcome runtime⟩

theorem certified_empty (certificate : SolidityEmptyContract.Preserves creation runtime creationSteps runtimeSteps) :
    SolidityEmptyContract.Preserves creation runtime creationSteps runtimeSteps ∧
    (∀ input, coreHalt (contractOutcome [] input) =
      (Core.Block.revert []).result emptyStore .leftFirst () []) ∧
    (∀ input, deploymentOutcome runtime input = coreHalt (SolidityDeployment.outcome runtime input)) :=
  ⟨certificate, empty_contract_outcome, deployment_outcome runtime⟩

end Solidity.Compatibility.Clients
