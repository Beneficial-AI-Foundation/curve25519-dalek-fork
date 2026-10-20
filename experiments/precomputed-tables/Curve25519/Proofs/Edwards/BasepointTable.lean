/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519.Proofs.Edwards.BasepointTableData
import Curve25519.Proofs.Edwards.BasepointTableCheck0
import Curve25519.Proofs.Edwards.BasepointTableCheck1
import Curve25519.Proofs.Edwards.BasepointTableCheck2
import Curve25519.Proofs.Edwards.MultiplesCheck
public section

/-! # The multiples of `B` in dalek's radix-16 basepoint table (not audited)

The affine coordinates of `(j + 1) • 2^(8 i) • B` (`i < 32`, `j < 8`), the points of dalek's
`ED25519_BASEPOINT_TABLE`, from the kernel checks of `BasepointTableCheck0`–`2`. -/

namespace curve25519.Proofs

open TwistedEdwardsModel

/-- The coordinates of `(j + 1) • 2^(8 i) • B` for `i < 32`, `j < 8` (dalek's
`ED25519_BASEPOINT_TABLE`). -/
theorem basepointTableCoords_spec (i j : ℕ) (hi : i < 32) (hj : j < 8) :
    ((j + 1) • 2 ^ (8 * i) • basepoint).x = (basepointTableCoords[8 * i + j]!.1 : ℕ) ∧
      ((j + 1) • 2 ^ (8 * i) • basepoint).y = (basepointTableCoords[8 * i + j]!.2 : ℕ) := by
  have h8 : (8 * i + j) % 8 + 1 = j + 1 := by omega
  have h8' : (8 * i + j) / 8 = i := by omega
  have hc := (show ∀ k < 256, edwards.Equation ((basepointTableCoords[k]!.1 : ℕ) : ZMod p)
      (basepointTableCoords[k]!.2 : ℕ) ∧
      (Extended.nsmul ((k % 8 + 1) * 2 ^ (8 * (k / 8))) (basepointExt edwards)).ProjEq
        ⟨(basepointTableCoords[k]!.1 : ℕ), (basepointTableCoords[k]!.2 : ℕ), 1,
          ((basepointTableCoords[k]!.1 : ℕ) : ZMod p) * (basepointTableCoords[k]!.2 : ℕ)⟩ from
    fun k hk => by
      rcases Nat.lt_or_ge k 128 with h0 | h0
      · exact basepointTableCoords_check0 _ (Nat.zero_le _) h0
      rcases Nat.lt_or_ge k 192 with h1 | h1
      · exact basepointTableCoords_check1 _ h0 h1
      · exact basepointTableCoords_check2 _ h1 hk) (8 * i + j) (by omega)
  rw [h8, h8'] at hc
  rw [smul_smul]
  exact nsmul_basepoint_of_check hc

end curve25519.Proofs
