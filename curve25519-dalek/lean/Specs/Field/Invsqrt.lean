/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Field.SqrtRatioI
public import Specs.Backend.Serial.U64.Field.One
public import Specs.Field.Lemmas
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.field.FieldElement51

@[step]
theorem invsqrt_spec (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    invsqrt self ⦃ (c : subtle.Choice) (r : FieldElement51) =>
      c.IsValid ∧ (self.asNat % p = 0 → c = 0#u8 ∧ r.asNat % p = 0) ∧
      (self.asNat % p ≠ 0 → (∃ x : ℕ, x ^ 2 * self.asNat % p = 1) →
        c = 1#u8 ∧ r.asNat ^ 2 * self.asNat % p = 1) ∧
      (self.asNat % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * self.asNat % p = 1) →
        c = 0#u8 ∧ r.asNat ^ 2 * self.asNat % p = sqrtM1) ∧
      r.asNat % p % 2 = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold invsqrt
  step as ⟨one, hone, honeb⟩
  have h1 : one.asNat % p = 1 := by
    rw [hone, one_mod_p]
  step as ⟨c, r, hcv, hu0, hv0, hsq, hnsq, hpar, hrb⟩
  rw [h1] at hv0 hsq hnsq
  refine ⟨hcv, fun h => hv0 one_ne_zero h, hsq, fun h hx => ?_, hpar, hrb⟩
  obtain ⟨hc, hr⟩ := hnsq h hx
  rw [hr, hone, mul_one, Nat.mod_eq_of_lt sqrtM1_lt]
  exact ⟨hc, rfl⟩

end Curve25519Dalek.field.FieldElement51
