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
import Proofs.Backend.Serial.U64.Field.Square
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.field.FieldElement51

private theorem two_pow_sub_one_mul_add (a b : ℕ) :
    (2 ^ a - 1) * 2 ^ b + (2 ^ b - 1) = 2 ^ (a + b) - 1 := by
  have ha : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hb : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hab : 1 ≤ 2 ^ (a + b) := Nat.one_le_two_pow
  zify [ha, hb, hab]
  ring

/-- `x ^ 2 ^ k`, kept opaque so that large exponents are never expanded. -/
@[irreducible] private def powTwoPow (x k : ℕ) : ℕ := x ^ 2 ^ k

/-- `pow2k_spec` with the power hidden behind `powTwoPow`. -/
private theorem pow2k_spec' (self : FieldElement51) (k : U32) (hk : 0 < k.val)
    (hself : self.LimbsLt 54) :
    self.pow2k k ⦃ (r : FieldElement51) =>
      r.asNat % p = powTwoPow self.asNat k.val % p ∧ r.LimbsLt 52 ⦄ := by
  unfold powTwoPow
  exact backend.serial.u64.field.FieldElement51.pow2k_spec self k hk hself

/-- One step of the addition chain: from `x ^ (2^a - 1)` and `x ^ (2^b - 1)` to
`x ^ (2^(a+b) - 1)`, via `b` squarings and a multiplication. -/
private theorem pow_step {x y z u w : ℕ} (a b c : ℕ) (hc : a + b = c)
    (hy : y % p = x ^ (2 ^ a - 1) % p) (hz : z % p = powTwoPow y b % p)
    (hu : u % p = x ^ (2 ^ b - 1) % p) (hw : w % p = z * u % p) :
    w % p = x ^ (2 ^ c - 1) % p := by
  have h : z * u ≡ (x ^ (2 ^ a - 1)) ^ 2 ^ b * x ^ (2 ^ b - 1) [MOD p] :=
    Nat.ModEq.mul (Nat.ModEq.trans (by unfold powTwoPow at hz; exact hz) (Nat.ModEq.pow _ hy)) hu
  rw [← pow_mul, ← pow_add, two_pow_sub_one_mul_add, hc] at h
  exact hw.trans h

@[step]
theorem pow22501_spec (self : FieldElement51) (hself : self.LimbsLt 54) :
    pow22501 self ⦃ (t19 t3 : FieldElement51) =>
      t19.asNat % p = self.asNat ^ (2 ^ 250 - 1) % p ∧ t3.asNat % p = self.asNat ^ 11 % p ∧
      t19.LimbsLt 52 ∧ t3.LimbsLt 52 ⦄ := by
  unfold pow22501
  step as ⟨t0, ht0, ht0b⟩
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨t1, ht1, ht1b⟩
  step as ⟨t2, ht2, ht2b⟩
  step as ⟨t3, ht3, ht3b⟩
  step as ⟨t4, ht4, ht4b⟩
  step as ⟨t5, ht5, ht5b⟩
  step with pow2k_spec' as ⟨t6, ht6, ht6b⟩
  step as ⟨t7, ht7, ht7b⟩
  step with pow2k_spec' as ⟨t8, ht8, ht8b⟩
  step as ⟨t9, ht9, ht9b⟩
  step with pow2k_spec' as ⟨t10, ht10, ht10b⟩
  step as ⟨t11, ht11, ht11b⟩
  step with pow2k_spec' as ⟨t12, ht12, ht12b⟩
  step as ⟨t13, ht13, ht13b⟩
  step with pow2k_spec' as ⟨t14, ht14, ht14b⟩
  step as ⟨t15, ht15, ht15b⟩
  step with pow2k_spec' as ⟨t16, ht16, ht16b⟩
  step as ⟨t17, ht17, ht17b⟩
  step with pow2k_spec' as ⟨t18, ht18, ht18b⟩
  step as ⟨t19, ht19, ht19b⟩
  set x := self.asNat
  have h2 : t2.asNat ≡ x * ((x ^ 2) ^ 2) ^ 2 [MOD p] :=
    Nat.ModEq.trans ht2 (Nat.ModEq.mul_left _
      (Nat.ModEq.trans ht1 (Nat.ModEq.pow _ (Nat.ModEq.trans hfe (Nat.ModEq.pow _ ht0)))))
  have h3 : t3.asNat ≡ x ^ 11 [MOD p] := by
    have h := Nat.ModEq.trans ht3 (Nat.ModEq.mul ht0 h2)
    rwa [show x ^ 2 * (x * ((x ^ 2) ^ 2) ^ 2) = x ^ 11 by ring] at h
  have h5 : t5.asNat % p = x ^ (2 ^ 5 - 1) % p := by
    have h := Nat.ModEq.trans ht5 (Nat.ModEq.mul h2 (Nat.ModEq.trans ht4 (Nat.ModEq.pow _ h3)))
    rwa [show x * ((x ^ 2) ^ 2) ^ 2 * (x ^ 11) ^ 2 = x ^ 31 by ring] at h
  have h7 := pow_step 5 5 10 rfl h5 ht6 h5 ht7
  have h9 := pow_step 10 10 20 rfl h7 ht8 h7 ht9
  have h11 := pow_step 20 20 40 rfl h9 ht10 h9 ht11
  have h13 := pow_step 40 10 50 rfl h11 ht12 h7 ht13
  have h15 := pow_step 50 50 100 rfl h13 ht14 h13 ht15
  have h17 := pow_step 100 100 200 rfl h15 ht16 h15 ht17
  exact ⟨pow_step 200 50 250 rfl h17 ht18 h13 ht19, h3, ht19b, ht3b⟩

end Curve25519Dalek.field.FieldElement51
