/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
import all Curve25519.Basic
public import Curve25519.Proofs.Edwards.BasepointTableData
public import Curve25519.Proofs.Edwards.MultiplesCheck
public section

/-! # Kernel check of `basepointTableCoords`, rows `0` to `15` (not audited) -/

namespace curve25519.Proofs

open TwistedEdwardsModel

/-- The kernel check of `basepointTableCoords`, rows `0` to `15`. -/
theorem basepointTableCoords_check0 : ∀ k, 0 ≤ k → k < 128 →
    edwards.Equation ((basepointTableCoords[k]!.1 : ℕ) : ZMod p) (basepointTableCoords[k]!.2 : ℕ) ∧
    (Extended.nsmul ((k % 8 + 1) * 2 ^ (8 * (k / 8))) (basepointExt edwards)).ProjEq ⟨(basepointTableCoords[k]!.1 : ℕ),
      (basepointTableCoords[k]!.2 : ℕ), 1, ((basepointTableCoords[k]!.1 : ℕ) : ZMod p) * (basepointTableCoords[k]!.2 : ℕ)⟩ := by
  rw [edwards_eq']
  decide +kernel

end curve25519.Proofs
