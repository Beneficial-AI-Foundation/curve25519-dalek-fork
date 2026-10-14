/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Pow2k
import Proofs.Field.Pow22501
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.field.FieldElement51

private theorem two_pow_sub_one_mul_four_add_one (a c : ℕ) (hc : a + 2 = c) :
    (2 ^ a - 1) * 2 ^ 2 + 1 = 2 ^ c - 3 := by
  subst hc
  have ha : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hc : 3 ≤ 2 ^ (a + 2) := by rw [pow_add]; omega
  zify [ha, hc]
  ring

@[step]
theorem pow_p58_spec (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow_p58 self ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ (2 ^ 252 - 3) % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold pow_p58
  step as ⟨t19, t3, h19, h3, h19b, h3b⟩
  generalize hn : 2 ^ 250 - 1 = n at h19
  step as ⟨t20, h20, h20b⟩
  step as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  subst hn
  have h : r.asNat ≡ self.asNat * (self.asNat ^ (2 ^ 250 - 1)) ^ 2 ^ 2 [MOD p] :=
    Nat.ModEq.trans hr (Nat.ModEq.mul_left _ (Nat.ModEq.trans h20 (Nat.ModEq.pow _ h19)))
  rwa [← pow_mul, ← pow_succ', two_pow_sub_one_mul_four_add_one 250 252 rfl] at h

end Curve25519Dalek.field.FieldElement51
