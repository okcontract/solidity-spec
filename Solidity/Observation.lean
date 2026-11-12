/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Interaction.World
import Solidity.Target

/-! Versioned observation contract. These definitions specify what
execution/refinement theorems must observe; they do not assert that a compiler,
foreign executor, or capability analysis satisfies the contract. -/
namespace Solidity.Observation
open Contract.Interaction

inductive Halt where
  | returned (bytes : List UInt8)
  | reverted (bytes : List UInt8)
  | exceptional
  deriving DecidableEq, Repr

/-- Panic is observed through its revert bytes, just like a user-authored
revert with identical bytes. A failed compiler/interpreter is not a Halt. -/
def panic (code : UInt8) : Halt := .reverted (Contract.panic code)

structure PublicState where
  accounts : Address → Account
  storage : Address → Word → Word
  logs : List Event
  present : Address → Bool

/-- These facts cannot be recovered from balance/code alone. Cancun deletion
depends on creation in this transaction (EIP-6780). The executing machine must update
them; the legacy account projection is deliberately insufficient. -/
structure Lifecycle where
  present : Address → Bool
  created : Address → Bool
  touched : Address → Bool
  pendingDeletion : Address → Bool

/-- Observe canonical account addresses. The legacy `other` projection has no
source meaning: callers must establish that all relevant effects are in these
named fields, not hide foreign effects there. -/
def publicState (world : World) (lifecycle : Lifecycle) : PublicState where
  accounts := world.accounts
  storage := fun address slot => world.storage (address.setWidth 256) slot
  logs := world.logs
  present := lifecycle.present

structure Invocation where
  halt : Halt
  state : PublicState
  transient : Address → Word → Word
  lifecycle : Lifecycle

inductive Action where
  | enterCall (kind : CallKind) (caller owner codeAddress : Address)
      (value : Word) (input : List UInt8)
  | leaveCall (halt : Halt)
  | enterCreation (creator : Address) (value : Word) (initCode : List UInt8)
      (salt : Option Word)
  | leaveCreation (address : Option Address) (halt : Halt)
  | emitLog (event : Event)
  deriving DecidableEq, Repr

/-- Resource observations come from proved execution, never a free gas oracle.
Access/refund state is invocation-local bookkeeping at this boundary; the
transaction settlement contract is separate. -/
structure Resources where
  gasRemaining : Nat
  refund : Int
  gasReadings : List Word
  warmAccounts : Address → Bool
  warmSlots : Address → Word → Bool

structure Representation where
  executingCode : List UInt8
  creationCode : List UInt8
  immutableValues : List Word
  deriving DecidableEq, Repr

structure Record where
  invocation : Invocation
  actions : List Action
  resources : Resources
  representation : Representation

inductive Profile where
  | functional | metered | representation
  deriving DecidableEq, Repr

/-- Every profile observes return/revert bytes, state and interaction order.
The functional projection erases resource bookkeeping, never returned data
that happened to be computed by a gas/code-sensitive program. Such programs
require the stronger profile and a justified capability/environment judgment. -/
def Rel (profile : Profile) (source target : Record) : Prop :=
  source.invocation = target.invocation ∧ source.actions = target.actions ∧
  (profile ≠ .functional → source.resources = target.resources) ∧
  (profile = .representation → source.representation = target.representation)

inductive TraceRel (profile : Profile) : List Record → List Record → Prop where
  | nil : TraceRel profile [] []
  | cons : Rel profile source target → TraceRel profile sources targets →
      TraceRel profile (source :: sources) (target :: targets)

structure Capabilities where
  gasSensitive : Bool
  codeSensitive : Bool
  rawRepresentation : Bool
  unknownContext : Bool
  deriving DecidableEq, Repr

/-- This is a restriction on a *proved* capability summary, not an analyzer.
Unknown foreign contexts cannot be claimed gas/representation insensitive. -/
def Admissible (profile : Profile) (uses : Capabilities) : Prop :=
  match profile with
  | .functional => uses.gasSensitive = false ∧ uses.codeSensitive = false ∧
      uses.rawRepresentation = false ∧ uses.unknownContext = false
  | .metered => uses.codeSensitive = false ∧ uses.rawRepresentation = false ∧ uses.unknownContext = false
  | .representation => True

inductive Attempt where
  | completed : Record → Attempt
  | exhausted : Attempt
  | unsupported : String → Attempt
  | invalidContext : String → Attempt

/-- Inconclusive runs have no correspondence witness, even when both sides
exhausted or rejected. Completion and support are independent proof obligations. -/
def Corresponds (profile : Profile) : Attempt → Attempt → Prop
  | .completed a, .completed b => Rel profile a b
  | _, _ => False

theorem rel_refl (profile : Profile) (value : Record) : Rel profile value value :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem rel_symm (h : Rel profile a b) : Rel profile b a :=
  ⟨h.1.symm, h.2.1.symm, fun hp => (h.2.2.1 hp).symm, fun hp => (h.2.2.2 hp).symm⟩

theorem rel_trans (ab : Rel profile a b) (bc : Rel profile b c) : Rel profile a c :=
  ⟨ab.1.trans bc.1, ab.2.1.trans bc.2.1,
   fun hp => (ab.2.2.1 hp).trans (bc.2.2.1 hp),
   fun hp => (ab.2.2.2 hp).trans (bc.2.2.2 hp)⟩

theorem representation_metered (h : Rel .representation a b) : Rel .metered a b :=
  ⟨h.1, h.2.1, fun _ => h.2.2.1 (by decide), fun impossible => by cases impossible⟩

theorem metered_functional (h : Rel .metered a b) : Rel .functional a b :=
  ⟨h.1, h.2.1, fun impossible => False.elim (impossible rfl), fun impossible => by cases impossible⟩

theorem corresponds_completed (h : Corresponds profile a b) :
    ∃ source target, a = .completed source ∧ b = .completed target ∧ Rel profile source target := by
  cases a <;> cases b <;> simp [Corresponds] at h
  exact ⟨_, _, rfl, rfl, h⟩

theorem exhausted_never_corresponds (profile : Profile) (other : Attempt) :
    ¬ Corresponds profile .exhausted other := by cases other <;> simp [Corresponds]

/-- Invocation rollback restores the shared-world snapshot. This operation
has no gas, transaction-nonce, access-list or fee-settlement claim. -/
def failedInvocation (before : World) (lifecycle : Lifecycle) (halt : Halt) : Invocation :=
  ⟨halt, publicState before lifecycle, before.transient, lifecycle⟩

theorem failedInvocation_restores (before : World) (lifecycle : Lifecycle) (halt : Halt) :
    (failedInvocation before lifecycle halt).state = publicState before lifecycle ∧
    (failedInvocation before lifecycle halt).transient = before.transient ∧
    (failedInvocation before lifecycle halt).lifecycle = lifecycle := ⟨rfl, rfl, rfl⟩

theorem transaction_transient_cleared (world : World) (owner : Address) (slot : Word) :
    world.clearTransient.transient owner slot = 0 := rfl

end Solidity.Observation
