/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Power
import Contract.Interaction.WordPower

namespace Solidity.Compatibility

private theorem power_nat (base : BitVec bits) (exponent : Nat) :
    (base ^ exponent).toNat = base.toNat ^ exponent % 2^bits := by
  induction exponent with
  | zero => simp [BitVec.pow_zero]
  | succ n ih => simp [BitVec.pow_succ, BitVec.toNat_mul, ih, Nat.pow_succ]

/-- The source and independent target power algorithms agree through their
mathematical specifications. Neither checker delegates to the other's runner. -/
theorem power_target (base : BitVec 256) (exponent : Nat) :
    Core.wordPow base exponent = Contract.Interaction.WordPower.pow base exponent := by
  apply BitVec.eq_of_toNat_eq
  rw [Core.wordPow_spec, Contract.Interaction.WordPower.toNat_pow, power_nat]

end Solidity.Compatibility
