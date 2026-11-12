/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Bindings
import Solidity.Core.Execution.Transition

namespace Solidity.Execution
open Static
open Aggregates (Heap Result Failure)

/-- Primitive codecs for closed, typed external keys. These hooks do not
execute syntax or calls. Production programs use the physical Heap; the
parametric state preserves existing logical-store certificates exactly. -/
structure Backend (σ : Type) (Key : SType → Type) where
  read : σ → {type : SType} → Key type → Result type.Value
  write : σ → {type : SType} → Key type → type.Value → Result σ

abbrev EmptyKey (_ : SType) := Empty

def physicalBackend : Backend Unit EmptyKey where
  read _ _ key := nomatch key
  write _ _ key := nomatch key

structure MachineState (σ : Type) where
  external : σ
  heap : Heap := {}
  locals : Locals := Locals.empty
  mode : Core.ArithmeticMode := .checked
  materializationRemaining : Nat := 4096

/-- Both bounds are host limits, never EVM operand-stack estimates. Internal
source calls do not increment the EVM message depth. -/
structure Limits where
  aggregateFuel : Nat := 128
  hostContinuationLimit : Option Nat := none

inductive TargetResource where
  | stack
  deriving DecidableEq, Repr

inductive Observation (σ : Type) where
  | returned : Packet → MachineState σ → Observation σ
  | failed : Failure → MachineState σ → Observation σ
  | inconclusive : Failure → MachineState σ → Observation σ
  | resourceLimit : TargetResource → MachineState σ → Observation σ

def Observation.state : Observation σ → MachineState σ
  | .returned _ state | .failed _ state | .inconclusive _ state | .resourceLimit _ state => state

def isSourceFailure : Failure → Bool
  | .revert _ | .panic _ | .exceptional => true
  | _ => false

/-- An actual invocation failure restores the complete entry checkpoint, including
transient storage, logs and reference-history metadata. Host suspension never
uses this operation; inconclusive/model failures do not claim rollback either.
Transaction admission and fees are outside this invocation snapshot. -/
def fail (entry : MachineState σ) (failure : Failure) : Observation σ := .failed failure entry

theorem fail_restores (entry : MachineState σ) (failure : Failure) :
    (fail entry failure).state = entry := rfl

end Solidity.Execution
