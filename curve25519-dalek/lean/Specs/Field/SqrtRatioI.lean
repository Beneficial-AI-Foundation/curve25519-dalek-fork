/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Alessandro D'Angelo
-/
module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Field.PowP58
public import Specs.Field.CtEq
public import Specs.Field.IsNegative
public import Specs.Backend.Serial.U64.Field.Square
public import Specs.Backend.Serial.U64.Field.Mul
public import Specs.Backend.Serial.U64.Field.Neg
public import Specs.Backend.Serial.U64.Field.ConditionalAssign
public import Specs.Backend.Serial.U64.Constants.SqrtM1
public import Specs.Lemmas.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.field.FieldElement51

/-- The exponent `(p - 5) / 8` of `pow_p58`, kept irreducible. -/
private def e58 : ℕ := 2 ^ 252 - 3

@[local step]
private theorem pow_p58_spec' (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow_p58 self ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ e58 % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  pow_p58_spec self hself

private theorem e58_eq : 8 * e58 + 5 = p := by
  unfold e58
  have := p_add_nineteen
  omega

attribute [irreducible] e58

/-! ## Arithmetic in `ZMod p` -/

/-- In a field containing a square root `i` of `-1`, the fourth roots of unity are `±1`, `±i`. -/
private theorem eq_one_or_neg_one_or_of_pow_four_eq_one {K : Type*} [Field K] {t i : K}
    (hi : i ^ 2 = -1) (ht : t ^ 4 = 1) : t = 1 ∨ t = -1 ∨ t = i ∨ t = -i := by
  have h : (t - 1) * (t + 1) * ((t - i) * (t + i)) = 0 := by
    linear_combination ht - (t ^ 2 - 1) * hi
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at h
  tauto

private theorem mod_eq_iff {a b : ℕ} : a % p = b % p ↔ (a : ZMod p) = b :=
  (ZMod.natCast_eq_natCast_iff' a b p).symm

private theorem cast_neg {a b : ℕ} (h : (a + b) % p = 0) : (a : ZMod p) = -b := by
  have h' := ZMod.natCast_eq_zero_iff_mod.mpr h
  push_cast at h'
  linear_combination h'

private theorem two_ne_zero_p : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) h'
  have := p_add_nineteen
  omega

private theorem sqrtM1_sq : (sqrtM1 : ZMod p) ^ 2 = -1 := by
  have h := ZMod.natCast_eq_zero_iff_mod.mpr sqrtM1_sq_add_one
  push_cast at h
  linear_combination h

private theorem one_ne_neg_one_p : (1 : ZMod p) ≠ -1 := by
  intro h
  exact two_ne_zero_p (by linear_combination h)

private theorem sqrtM1_ne_one : (sqrtM1 : ZMod p) ≠ 1 := by
  intro h
  have := sqrtM1_sq
  rw [h] at this
  exact one_ne_neg_one_p (by simpa using this)

private theorem sqrtM1_ne_neg_one : (sqrtM1 : ZMod p) ≠ -1 := by
  intro h
  have := sqrtM1_sq
  rw [h] at this
  exact one_ne_neg_one_p (by simpa using this)

private theorem sqrtM1_ne_neg_self : (sqrtM1 : ZMod p) ≠ -sqrtM1 := by
  intro h
  have h0 : (sqrtM1 : ZMod p) = 0 := by
    have : 2 * (sqrtM1 : ZMod p) = 0 := by linear_combination h
    simpa [two_ne_zero_p] using this
  have := sqrtM1_sq
  rw [h0] at this
  exact one_ne_neg_one_p (by simpa using this.symm)

/-- `v r² = u w^((p-1)/4)` for `r = u v³ w^((p-5)/8)`, `w = u v⁷`. -/
private theorem check_eq (U V : ZMod p) (n : ℕ) :
    V * (U * V ^ 3 * (U * V ^ 7) ^ n) ^ 2 = U * (U * V ^ 7) ^ (2 * n + 1) := by
  ring

/-- `w^((p-1)/4)` is a fourth root of unity. -/
private theorem pow_cases (W : ZMod p) (hW : W ≠ 0) :
    W ^ (2 * e58 + 1) = 1 ∨ W ^ (2 * e58 + 1) = -1 ∨ W ^ (2 * e58 + 1) = sqrtM1 ∨
      W ^ (2 * e58 + 1) = -sqrtM1 := by
  refine eq_one_or_neg_one_or_of_pow_four_eq_one sqrtM1_sq ?_
  rw [← pow_mul, show (2 * e58 + 1) * 4 = p - 1 by have := e58_eq; omega]
  exact ZMod.pow_card_sub_one_eq_one hW

/-- If `u / v` is a nonzero square, `w^((p-1)/4) = ±1`. -/
private theorem pow_cases_of_sq (X V : ZMod p) (hX : X ≠ 0) (hV : V ≠ 0) :
    (X ^ 2 * V * V ^ 7) ^ (2 * e58 + 1) = 1 ∨ (X ^ 2 * V * V ^ 7) ^ (2 * e58 + 1) = -1 := by
  rw [← mul_self_eq_one_iff, ← pow_add, show X ^ 2 * V * V ^ 7 = (X * V ^ 4) ^ 2 by ring,
    ← pow_mul, show 2 * (2 * e58 + 1 + (2 * e58 + 1)) = p - 1 by have := e58_eq; omega]
  exact ZMod.pow_card_sub_one_eq_one (mul_ne_zero hX (pow_ne_zero _ hV))

private theorem exists_sq_iff (v u : ℕ) :
    (∃ x : ℕ, x ^ 2 * v % p = u % p) ↔ ∃ X : ZMod p, X ^ 2 * v = u := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mod_eq_iff] at hx
    push_cast at hx
    exact hx
  · rintro ⟨X, hX⟩
    refine ⟨X.val, ?_⟩
    rw [mod_eq_iff]
    push_cast
    simpa using hX

/-- Negating an odd canonical value gives an even one (`p` is odd). -/
private theorem neg_mod_two {a b : ℕ} (h : (a + b) % p = 0) (hb : b % p % 2 = 1) :
    a % p % 2 = 0 := by
  have hp2 : p % 2 = 1 := by
    have := p_add_nineteen
    omega
  have hpos := p_pos
  have ha := Nat.mod_lt a hpos
  have hb' := Nat.mod_lt b hpos
  rw [Nat.add_mod] at h
  have hsum : a % p + b % p = p := by
    rcases Nat.lt_or_ge (a % p + b % p) p with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h
      omega
    · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
      omega
  omega

/-! ## The `Choice` logic -/

private theorem choice_or {a b : subtle.Choice} {P Q : Prop} (ha1 : P → a = 1#u8)
    (ha0 : ¬P → a = 0#u8) (hb1 : Q → b = 1#u8) (hb0 : ¬Q → b = 0#u8) :
    (P ∨ Q → (a ||| b) = 1#u8) ∧ (¬(P ∨ Q) → (a ||| b) = 0#u8) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp_all [show (1#u8 ||| 1#u8) = 1#u8 by decide]

/-- `conditional_negate` on field elements. -/
@[local step]
private theorem conditional_negate_spec (x : FieldElement51) (c : subtle.Choice)
    (hc : c.IsValid) (hx : ∀ i < 5, x[i]!.val < 2 ^ 54) :
    subtle.ConditionallyNegatable.Blanket.conditional_negate
      backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
      Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51 x c ⦃ (r : FieldElement51) =>
      (c = 0#u8 → r = x) ∧
      (c = 1#u8 → (r.asNat + x.asNat) % p = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52) ⦄ := by
  unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
  step as ⟨n, hn, hnb⟩
  step as ⟨r, hr0, hr1⟩
  exact ⟨hr0, fun hc => by rw [hr1 hc]; exact ⟨hn, hnb⟩⟩

@[step]
theorem sqrt_ratio_i_spec (u v : FieldElement51) (hu : ∀ i < 5, u[i]!.val < 2 ^ 54)
    (hv : ∀ i < 5, v[i]!.val < 2 ^ 54) :
    sqrt_ratio_i u v ⦃ (c : subtle.Choice) (r : FieldElement51) =>
      c.IsValid ∧ (u.asNat % p = 0 → c = 1#u8 ∧ r.asNat % p = 0) ∧
      (u.asNat % p ≠ 0 → v.asNat % p = 0 → c = 0#u8 ∧ r.asNat % p = 0) ∧
      (v.asNat % p ≠ 0 → (∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) →
        c = 1#u8 ∧ r.asNat ^ 2 * v.asNat % p = u.asNat % p) ∧
      (v.asNat % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) →
        c = 0#u8 ∧ r.asNat ^ 2 * v.asNat % p = sqrtM1 * u.asNat % p) ∧
      r.asNat % p % 2 = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold sqrt_ratio_i
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨v3, hv3, hv3b⟩
  step as ⟨fe1, hfe1, hfe1b⟩
  step as ⟨v7, hv7, hv7b⟩
  step as ⟨fe2, hfe2, hfe2b⟩
  step as ⟨fe3, hfe3, hfe3b⟩
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨r, hr, hrb⟩
  step as ⟨fe5, hfe5, hfe5b⟩
  step as ⟨check, hcheck, hcheckb⟩
  step as ⟨fe6, hfe6, hfe6b⟩
  step as ⟨cs, hcsv, hcs1, hcs0⟩
  step as ⟨fe7, hfe7, hfe7b⟩
  step as ⟨fs, hfsv, hfs1, hfs0⟩
  step as ⟨fe8, hfe8, hfe8b⟩
  step as ⟨fsi, hfsiv, hfsi1, hfsi0⟩
  step as ⟨r', hr', hr'b⟩
  step as ⟨c, hcv, hc⟩
  step as ⟨r1, hr10, hr11⟩
  step as ⟨rn, hrnv, hrn⟩
  have hr1b : ∀ i < 5, r1[i]!.val < 2 ^ 52 := by
    rcases hcv with h | h
    · rw [hr10 h]
      exact hrb
    · rw [hr11 h]
      exact hr'b
  have hr1b' : ∀ i < 5, r1[i]!.val < 2 ^ 54 := fun i hi =>
    lt_trans (hr1b i hi) (by norm_num)
  step as ⟨r2, hr20, hr21⟩
  step as ⟨out, houtv, hout⟩
  -- the value of `r2`
  have hsq : (r2.asNat : ZMod p) ^ 2 = (r1.asNat : ZMod p) ^ 2 := by
    rcases hrnv with h | h
    · rw [hr20 h]
    · rw [cast_neg (hr21 h).1, neg_sq]
  have hpar : r2.asNat % p % 2 = 0 := by
    rcases hrnv with h | h
    · rw [hr20 h, ← hrn, h]
      rfl
    · refine neg_mod_two (hr21 h).1 ?_
      rw [← hrn, h]
      rfl
  have hr2b : ∀ i < 5, r2[i]!.val < 2 ^ 52 := by
    rcases hrnv with h | h
    · rw [hr20 h]
      exact hr1b
    · exact (hr21 h).2
  -- move to `ZMod p`
  have eR : (r.asNat : ZMod p) = u.asNat * v.asNat ^ 3 * (u.asNat * v.asNat ^ 7) ^ e58 := by
    have h1 := mod_eq_iff.mp hr
    have h2 := mod_eq_iff.mp hfe2
    have h3 := mod_eq_iff.mp hfe4
    have h4 := mod_eq_iff.mp hfe3
    have h5 := mod_eq_iff.mp hv7
    have h6 := mod_eq_iff.mp hfe1
    have h7 := mod_eq_iff.mp hv3
    have h8 := mod_eq_iff.mp hfe
    push_cast at h1 h2 h3 h4 h5 h6 h7 h8
    rw [h1, h2, h3, h4, h5, h6, h7, h8]
    ring
  have eF7 : (fe7.asNat : ZMod p) = -u.asNat := cast_neg hfe7
  have eF8 : (fe8.asNat : ZMod p) = -u.asNat * sqrtM1 := by
    have h1 := mod_eq_iff.mp hfe8
    push_cast at h1
    rw [h1, eF7, hfe6]
  have eR' : (r'.asNat : ZMod p) = sqrtM1 * r.asNat := by
    have h1 := mod_eq_iff.mp hr'
    push_cast at h1
    rw [h1, hfe6]
  have eC0 : (check.asNat : ZMod p) = v.asNat * (r.asNat : ZMod p) ^ 2 := by
    have h1 := mod_eq_iff.mp hcheck
    have h2 := mod_eq_iff.mp hfe5
    push_cast at h1 h2
    rw [h1, h2]
  simp only [ne_eq, ← ZMod.natCast_eq_zero_iff_mod (n := p), mod_eq_iff (b := u.asNat),
    mod_eq_iff (b := sqrtM1 * u.asNat)]
  push_cast
  simp only [ne_eq, mod_eq_iff] at hcs1 hfs1 hfsi1 hcs0 hfs0 hfsi0
  rw [eF7] at hfs1 hfs0
  rw [eF8] at hfsi1 hfsi0
  -- name the values in `ZMod p`
  set U : ZMod p := (u.asNat : ZMod p) with hU
  set V : ZMod p := (v.asNat : ZMod p) with hV
  set R : ZMod p := (r.asNat : ZMod p) with hR
  set T : ZMod p := (U * V ^ 7) ^ (2 * e58 + 1) with hT
  clear_value U V R T
  have eVR : V * R ^ 2 = U * T := by
    rw [eR, hT]
    exact check_eq U V e58
  rw [eC0, eVR] at hcs1 hfs1 hfsi1 hcs0 hfs0 hfsi0
  obtain ⟨hc1, hc0⟩ := choice_or hfs1 hfs0 hfsi1 hfsi0
  rw [← hc] at hc1 hc0
  obtain ⟨ho1, ho0⟩ := choice_or hcs1 hcs0 hfs1 hfs0
  rw [← hout] at ho1 ho0
  have hR1 : U * T = -U ∨ U * T = -U * sqrtM1 → V * (r1.asNat : ZMod p) ^ 2 = -(U * T) := by
    intro h
    rw [hr11 (hc1 h), eR', mul_pow, sqrtM1_sq, ← eVR]
    ring
  have hR1' : ¬(U * T = -U ∨ U * T = -U * sqrtM1) → V * (r1.asNat : ZMod p) ^ 2 = U * T := by
    intro h
    rw [hr10 (hc0 h), ← hR, eVR]
  have hr2V : V * (r2.asNat : ZMod p) ^ 2 = V * (r1.asNat : ZMod p) ^ 2 := by rw [hsq]
  have hzero : R = 0 → (r2.asNat : ZMod p) = 0 := by
    intro h0
    rw [← pow_eq_zero_iff two_ne_zero, hsq]
    rcases hcv with h | h
    · rw [hr10 h, ← hR, h0]
      ring
    · rw [hr11 h, eR', h0]
      ring
  have hcase1 : U = 0 → out = 1#u8 ∧ (r2.asNat : ZMod p) = 0 := fun hU0 =>
    ⟨ho1 (Or.inl (by rw [hU0, zero_mul])), hzero (by rw [eR, hU0]; ring)⟩
  refine ⟨houtv, hcase1, fun hU0 hV0 => ?_, fun hV0 x hx => ?_, fun hV0 hns => ?_, hpar, hr2b⟩
  · -- `u ≠ 0`, `v = 0`
    have hT0 : T = 0 := by
      rw [hT, hV0]
      simp
    refine ⟨ho0 ?_, hzero (by rw [eR, hV0]; ring)⟩
    rw [hT0, mul_zero]
    rintro (h | h)
    · exact hU0 h.symm
    · exact hU0 (neg_eq_zero.mp h.symm)
  · -- `u / v` is a square
    by_cases hU0 : U = 0
    · obtain ⟨h1, h2⟩ := hcase1 hU0
      refine ⟨h1, ?_⟩
      rw [h2, hU0]
      ring
    have hX0 : (x : ZMod p) ≠ 0 := by
      intro h
      apply hU0
      rw [← hx, h]
      ring
    have hT' : T = 1 ∨ T = -1 := by
      rw [hT, ← hx]
      exact pow_cases_of_sq _ _ hX0 hV0
    rw [mul_comm, hr2V]
    rcases hT' with h | h
    · refine ⟨ho1 (Or.inl (by rw [h, mul_one])), ?_⟩
      rw [hR1' ?_, h, mul_one]
      rw [h]
      rintro (h' | h')
      · exact one_ne_neg_one_p (mul_left_cancel₀ hU0 (by linear_combination h'))
      · exact sqrtM1_ne_neg_one (mul_left_cancel₀ hU0 (by linear_combination h'))
    · refine ⟨ho1 (Or.inr (by rw [h, mul_neg_one])), ?_⟩
      rw [hR1 (Or.inl (by rw [h, mul_neg_one])), h]
      ring
  · -- `u / v` is not a square
    have hU0 : U ≠ 0 := by
      intro h
      exact hns ⟨0, by rw [h]; push_cast; ring⟩
    have hW : U * V ^ 7 ≠ 0 := mul_ne_zero hU0 (pow_ne_zero _ hV0)
    rw [mul_comm _ U, mul_comm, hr2V]
    rcases pow_cases _ hW with h | h | h | h <;> rw [← hT] at h
    · exact absurd ⟨r.asNat, by rw [← hR, mul_comm, eVR, h, mul_one]⟩ hns
    · refine absurd ⟨r'.asNat, ?_⟩ hns
      rw [eR']
      linear_combination (R ^ 2 * V) * sqrtM1_sq - eVR - U * h
    · have hn : ¬(U * T = -U ∨ U * T = -U * sqrtM1) := by
        rw [h]
        rintro (h' | h')
        · exact sqrtM1_ne_neg_one (mul_left_cancel₀ hU0 (by linear_combination h'))
        · exact sqrtM1_ne_neg_self (mul_left_cancel₀ hU0 (by linear_combination h'))
      refine ⟨ho0 ?_, by rw [hR1' hn, h]⟩
      rw [h]
      rintro (h' | h')
      · exact sqrtM1_ne_one (mul_left_cancel₀ hU0 (by linear_combination h'))
      · exact sqrtM1_ne_neg_one (mul_left_cancel₀ hU0 (by linear_combination h'))
    · have hy : U * T = -U * sqrtM1 := by
        rw [h]
        ring
      refine ⟨ho0 ?_, by rw [hR1 (Or.inr hy), h]; ring⟩
      rw [h]
      rintro (h' | h')
      · exact sqrtM1_ne_neg_one (mul_left_cancel₀ hU0 (by linear_combination -h'))
      · exact sqrtM1_ne_one (mul_left_cancel₀ hU0 (by linear_combination -h'))

end Curve25519Dalek.field.FieldElement51
