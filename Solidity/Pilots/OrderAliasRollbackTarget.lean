/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Pilots.OrderAliasRollback

/-! Two hand-authored Cancun artifacts for the prepared order-sensitive body.
Both receive the original word and failure flag. The write-first artifact
checks the high-half bound before doubling; the read-first artifact uses the
entry relation's zero word. Both perform the storage write before the check. -/
namespace Solidity.Pilots.OrderAliasRollback.Target
open Contract Evm
open Contract.Interaction (Word Memory wordBytes bytesWord)

abbrev input := AliasCallRollback.Target.input
abbrev initial := AliasCallRollback.Target.initial

def code (writeFirst : Bool) : List UInt8 :=
  if writeFirst then
    [0x5f,0x35,0x80,0x5f,0x55,0x80,0x60,0xa0,0x52,0x80,0x7f,0x80,0x0,0x0,0x0,0x0,
     0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,
     0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x11,0x15,0x60,0x42,0x57,
     0x80,0x1,0x60,0x20,0x35,0x60,0x3e,0x57,0x5f,0x52,0x60,0x20,0x5f,0xf3,0x5b,0x5f,
     0x5f,0xfd,0x5b,0x7f,0x4e,0x48,0x7b,0x71,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,
     0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,
     0x0,0x0,0x0,0x0,0x5f,0x52,0x60,0x11,0x60,0x4,0x52,0x60,0x24,0x5f,0xfd]
  else
    [0x5f,0x35,0x80,0x5f,0x55,0x80,0x60,0xa0,0x52,0x60,0x20,0x35,0x60,0x15,0x57,0x5f,0x52,0x60,0x20,0x5f,0xf3,0x5b,0x5f,0x5f,0xfd]

def halt (writeFirst fail : Bool) (value : Word) : Halt :=
  if overflows writeFirst value then .reverted (Contract.panic 0x11)
  else if fail then .reverted [] else .returned (wordBytes (result writeFirst value))

theorem return_read (memory : Memory) (value answer : Word) :
    ((memory.write 160 (wordBytes value)).write 0 (wordBytes answer)).read 0 32 = wordBytes answer := by
  rw [← Contract.Interaction.wordBytes_length answer]
  exact Memory.read_write _ _ _

set_option maxRecDepth 10000 in
theorem panic_read (memory : Memory) (value : Word) :
    (((memory.write 160 (wordBytes value)).write 0 (wordBytes (0x4e487b71*2^224))).write 4 (wordBytes 0x11)).read 0 36 =
      Contract.panic 0x11 := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
set_option linter.unusedSimpArgs false in
theorem target_trace (storage original : Stateful.Slots) (memory : Memory) (warm : Word → Bool)
    (refund : Int) (value : Word) (writeFirst fail : Bool) :
    ∃ used needed final,
      Stateful.run (code writeFirst) (input value fail) ⟨original,false⟩ 60
        (initial storage memory warm refund) = .finished used needed final ∧
      final.halt = halt writeFirst fail value ∧ final.state.storage = Stateful.write storage 0 value := by
  have threshold : bytesWord (Evm.padded (code true) 11 32) = BitVec.ofNat 256 (2^255) := by decide +kernel
  have selector : bytesWord (Evm.padded (code true) 68 32) = BitVec.ofNat 256 (0x4e487b71*2^224) := by decide +kernel
  have thresholdNat : (bytesWord (Evm.padded (code true) 11 32)).toNat = 2^255 := by
    rw [threshold]
    rfl
  simp only [code,ite_true,Evm.padded,Memory.read,bytesWord,BitVec.toNat_ofNat] at threshold selector thresholdNat
  cases writeFirst <;> cases fail <;> by_cases small : value.toNat < 2^255
  all_goals simp only [show (2 : Nat)^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 from rfl] at small
  all_goals unfold Stateful.run
  all_goals repeat
    rw [Guarded.run]
    simp [Stateful.step,Stateful.coreStep,Evm.step,Evm.push,Evm.unary,Evm.binary,
      code,initial,AliasCallRollback.Target.initial,AliasCallRollback.Target.input_value,
      AliasCallRollback.Target.input_flag,Guarded.Trace.charge,Evm.pushWidth,Evm.padded,
      Evm.scanJumps,Evm.jumpDestinations,Memory.read,bytesWord,Evm.expansionCost,Evm.expandedWords,Evm.memoryCost,
      halt,overflows,result,return_read,panic_read,small,threshold,selector,thresholdNat]
  all_goals first
    | refine ⟨_,_,_,⟨rfl,rfl,rfl⟩,?_,rfl⟩
    | refine ⟨_,_,_,rfl,?_,rfl⟩
  all_goals try (split <;> try omega)
  all_goals first
    | exact congrArg Halt.returned (return_read memory value _)
    | exact congrArg Halt.reverted (panic_read memory value)
    | rfl

end Solidity.Pilots.OrderAliasRollback.Target
