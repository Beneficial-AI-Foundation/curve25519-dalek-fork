/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519.Edwards.Torsion
import Curve25519.Edwards.Order
import Curve25519.Proofs.Ristretto.DescentCert
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public section

/-! # ristretto255: even points and the 4-torsion

ristretto255 (RFC 9496) represents its elements by **even** Edwards points (`Even P`, i.e.
`P = Q + Q`), two representatives standing for the same element when they differ by 4-torsion
(`edwards.Rel`, from `Curve25519.Models.TwistedEdwards.Even`). No quotient type is defined: the
specifications speak about representatives, and these are the facts they need.

* The 4-torsion is `{0, (∓√-1, 0), (0, -1)} = {eightTorsion 0, 2, 4, 6}`
  (`mem_torsionBy_four_iff_eightTorsion`).
* The even points are the points killed by `4 L` (`even_iff_four_mul_L_nsmul`), a subgroup of
  order `4 L` (`card_even`) containing the 4-torsion (`torsionBy_four_le_even`) and the basepoint
  (`even_basepoint`).
* Two representatives are related iff `x₁ y₂ = y₁ x₂` or `x₁ x₂ = y₁ y₂` (`rel_iff_formula`,
  RFC 9496's equality, what `RistrettoPoint::ct_eq` computes).
* A point is even iff `1 - y²` is a square (`even_iff_isSquare`, the 2-descent criterion of
  Decaf: the validity test of the encoding).

The 2-descent: the generic subgroup `edwards.descent = {P | IsSquare ((a - d)(1 - y²))}` of
`EllipticCurve.TwistedEdwards.Even` contains the even points, `a - d` is a square, and
`torsion8 ∉ descent` by Euler's criterion (`one_sub_torsion8_y_sq_pow_p_div_two` in
`Curve25519.Proofs.Ristretto.DescentCert`); as `|even| = 4 L` and `|edwards.Point| = 8 L`,
`descent` is the even subgroup (`descent_eq_even`). -/

namespace curve25519

open TwistedEdwardsModel

/-! ### The 4-torsion -/

/-- `eightTorsion 2 = (-√-1, 0)`. -/
theorem eightTorsion_two_x : (eightTorsion 2).x = -sqrtM1 := by
  rw [eightTorsion_two_x_eq, neg_sqrtM1_eq]

/-- `4 • eightTorsion i = 0` iff `i` is even. -/
theorem four_nsmul_eightTorsion_eq_zero_iff (i : Fin 8) :
    4 • eightTorsion i = 0 ↔ (i : ℕ) % 2 = 0 := by
  rw [eightTorsion_apply, smul_smul, ← addOrderOf_dvd_iff_nsmul_eq_zero, addOrderOf_torsion8]
  omega

/-- **The 4-torsion** of `edwards` is `{0, eightTorsion 2, eightTorsion 4, eightTorsion 6}`, i.e.
`{(0, 1), (-√-1, 0), (0, -1), (√-1, 0)}`. -/
theorem mem_torsionBy_four_iff_eightTorsion (P : edwards.Point) :
    P ∈ AddSubgroup.torsionBy edwards.Point 4 ↔
      P = 0 ∨ P = eightTorsion 2 ∨ P = eightTorsion 4 ∨ P = eightTorsion 6 := by
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, AddSubgroup.torsionBy.nsmul_iff]
  constructor
  · intro h
    have h8 : 8 • P = 0 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, ← smul_smul, h, smul_zero]
    obtain ⟨i, rfl⟩ := (eight_nsmul_eq_zero_iff P).mp h8
    rw [four_nsmul_eightTorsion_eq_zero_iff] at h
    fin_cases i
    · exact Or.inl eightTorsion_zero
    · exact absurd h (by decide)
    · exact Or.inr (Or.inl rfl)
    · exact absurd h (by decide)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact absurd h (by decide)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact absurd h (by decide)
  · rintro (rfl | rfl | rfl | rfl)
    · exact smul_zero 4
    · exact (four_nsmul_eightTorsion_eq_zero_iff 2).mpr rfl
    · exact (four_nsmul_eightTorsion_eq_zero_iff 4).mpr rfl
    · exact (four_nsmul_eightTorsion_eq_zero_iff 6).mpr rfl

/-! ### The even points -/

/-- **The even points**: in the cyclic group of order `8 L`, the doubles are the points killed
by `4 L`. -/
theorem even_iff_four_mul_L_nsmul (P : edwards.Point) : Even P ↔ (4 * L) • P = 0 := by
  constructor
  · rintro ⟨Q, rfl⟩
    rw [← two_nsmul, smul_smul, show 4 * L * 2 = 8 * L by ring, eight_mul_L_nsmul]
  · intro h
    obtain ⟨⟨i, n⟩, hq, -⟩ := exists_unique_decomposition P
    dsimp only at hq
    have hL := L_mod_two
    rw [hq, smul_add, eightTorsion_apply, smul_smul, smul_smul,
      show 4 * L * (n : ℕ) = 4 * n * L by ring, mul_smul (4 * (n : ℕ)) L, L_nsmul_basepoint,
      smul_zero, add_zero, ← addOrderOf_dvd_iff_nsmul_eq_zero, addOrderOf_torsion8,
      mul_assoc] at h
    have h2 : 2 ∣ L * i := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) h
    have hi : 2 ∣ (i : ℕ) := by
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h2L | h2i
      · omega
      · exact h2i
    obtain ⟨j, hj⟩ := hi
    have h2L : 2 * ((L + 1) / 2) = L + 1 := by omega
    refine ⟨j • torsion8 + ((L + 1) / 2 * n) • basepoint, ?_⟩
    rw [hq, eightTorsion_apply, hj, ← two_nsmul, smul_add, smul_smul, smul_smul,
      show 2 * ((L + 1) / 2 * (n : ℕ)) = n + n * L by rw [← mul_assoc, h2L]; ring, add_smul,
      mul_smul (n : ℕ) L, L_nsmul_basepoint, smul_zero, add_zero]

/-- The 4-torsion consists of even points. -/
theorem torsionBy_four_le_even :
    AddSubgroup.torsionBy edwards.Point 4 ≤ AddSubgroup.even edwards.Point := by
  intro P hP
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, AddSubgroup.torsionBy.nsmul_iff] at hP
  rw [AddSubgroup.mem_even, even_iff_four_mul_L_nsmul, mul_comm, ← smul_smul, hP, smul_zero]

/-- The generator `torsion8 + basepoint` of `edwards.Point`. -/
theorem zmultiples_torsion8_add_basepoint_eq_top :
    AddSubgroup.zmultiples (torsion8 + basepoint) = ⊤ :=
  AddSubgroup.eq_top_of_card_eq _ (by
    rw [Nat.card_zmultiples, addOrderOf_torsion8_add_basepoint, Nat.card_eq_fintype_card,
      card_edwards])

/-- `2 • (torsion8 + basepoint)` has order `4 L`. -/
theorem addOrderOf_two_nsmul_torsion8_add_basepoint :
    addOrderOf (2 • (torsion8 + basepoint)) = 4 * L := by
  rw [addOrderOf_nsmul' _ (by norm_num : (2 : ℕ) ≠ 0), addOrderOf_torsion8_add_basepoint,
    Nat.gcd_eq_right (Dvd.dvd.mul_right (by norm_num : 2 ∣ 8) L)]
  omega

/-- The even points are the multiples of `2 • (torsion8 + basepoint)`. -/
theorem even_eq_zmultiples :
    AddSubgroup.even edwards.Point = AddSubgroup.zmultiples (2 • (torsion8 + basepoint)) := by
  apply le_antisymm
  · intro P hP
    obtain ⟨Q, rfl⟩ := (AddSubgroup.mem_even.mp hP).exists_two_nsmul
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (zmultiples_torsion8_add_basepoint_eq_top ▸ AddSubgroup.mem_top Q)
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨k, ?_⟩
    rw [← hk, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, mul_comm]
  · rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.mem_even.mpr (Even.two_nsmul _)

/-- **The even points** form a subgroup of order `4 L` (index `2`). -/
theorem card_even : Nat.card (AddSubgroup.even edwards.Point) = 4 * L := by
  rw [even_eq_zmultiples, Nat.card_zmultiples, addOrderOf_two_nsmul_torsion8_add_basepoint]

/-- The basepoint is even. -/
theorem even_basepoint : Even basepoint :=
  (even_iff_four_mul_L_nsmul _).mpr (by rw [mul_smul, L_nsmul_basepoint, smul_zero])

/-! ### Equality of representatives -/

/-- **Equality of representatives**: `P` and `Q` represent the same element of ristretto255 iff
`x₁ y₂ = y₁ x₂` or `x₁ x₂ = y₁ y₂` (RFC 9496's equality, what `RistrettoPoint::ct_eq`
computes). -/
theorem rel_iff_formula (P Q : edwards.Point) :
    edwards.Rel P Q ↔ P.x * Q.y = P.y * Q.x ∨ P.x * Q.x = P.y * Q.y := by
  rw [rel_iff, edwards_a_eq_neg_one]
  refine or_congr_right ⟨fun h => ?_, fun h => ?_⟩
  · linear_combination -h
  · linear_combination -h

/-! ### The 2-descent -/

/-- `a - d = (2 / sqrtNegAAddTwo)²` is a square. -/
theorem a_sub_d_eq_sq : a - d = (2 / sqrtNegAAddTwo) ^ 2 := by
  rw [div_pow, eq_div_iff (pow_ne_zero 2 sqrtNegAAddTwo_ne_zero), mul_comm,
    ← four_eq_sqrtNegAAddTwo_sq_mul]
  norm_num

/-- Membership in the 2-descent subgroup of `edwards`: `1 - y²` is a square (the factor `a - d`
is a nonzero square). -/
theorem mem_descent_iff (P : edwards.Point) : P ∈ edwards.descent ↔ IsSquare (1 - P.y ^ 2) := by
  rw [mem_descent, edwards_a, edwards_d, a_sub_d_eq_sq,
    isSquare_sq_mul_iff (div_ne_zero two_ne_zero sqrtNegAAddTwo_ne_zero)]

/-- The 2-descent certificate: `1 - y²` is not a square at the point of order `8`
(Euler's criterion, `Proofs.one_sub_torsion8_y_sq_pow_p_div_two`). -/
theorem not_isSquare_one_sub_torsion8_y_sq : ¬ IsSquare (1 - torsion8.y ^ 2) := by
  rw [torsion8_y_eq]
  intro h
  have hpow := Proofs.one_sub_torsion8_y_sq_pow_p_div_two
  push_cast at hpow
  have hne : (1 - (55188659117513257062467267217118295137698188065244968500265048394206261417927 :
      ZMod p) ^ 2) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.div_pos two_lt_p.le two_pos).ne'] at hpow
    exact one_ne_zero (by linear_combination hpow)
  have := (ZMod.euler_criterion p hne).mp h
  rw [hpow] at this
  exact ZMod.neg_one_ne_one this

theorem torsion8_not_mem_descent : torsion8 ∉ edwards.descent := by
  rw [mem_descent_iff]
  exact not_isSquare_one_sub_torsion8_y_sq

/-- **The 2-descent**: the subgroup of points with `1 - y²` a square is exactly the subgroup of
even points. (`even ≤ descent` generically; `descent ≠ ⊤` by the certificate; `|even| = 4 L`
and `|descent|` divides `8 L`.) -/
theorem descent_eq_even : edwards.descent = AddSubgroup.even edwards.Point := by
  symm
  apply AddSubgroup.eq_of_le_of_card_ge even_le_descent
  obtain ⟨k, hk⟩ := AddSubgroup.card_dvd_of_le (even_le_descent (E := edwards))
  have hdvd := AddSubgroup.card_addSubgroup_dvd_card edwards.descent
  have hne : Nat.card edwards.descent ≠ Nat.card edwards.Point := fun h =>
    torsion8_not_mem_descent
      (((AddSubgroup.card_eq_iff_eq_top _).mp h).symm ▸ AddSubgroup.mem_top _)
  rw [Nat.card_eq_fintype_card (α := edwards.Point), card_edwards, hk, card_even] at hdvd hne
  rw [hk, card_even]
  have hL := L_pos
  have hk2 : k ∣ 2 :=
    Nat.dvd_of_mul_dvd_mul_left (by positivity : 0 < 4 * L)
      (by rw [show 4 * L * 2 = 8 * L by ring]; exact hdvd)
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
  · rw [mul_one]
  · exact absurd (by ring) hne

/-- **The 2-descent criterion** (Decaf/Ristretto): a point is even iff `1 - y²` is a square. -/
theorem even_iff_isSquare (P : edwards.Point) : Even P ↔ IsSquare (1 - P.y ^ 2) := by
  rw [← AddSubgroup.mem_even, ← descent_eq_even, mem_descent_iff]

/-- The 2-descent criterion on the Montgomery side: a point is even iff the `u`-coordinate of
its image in `edwards.toMontgomery` is a square. -/
theorem even_iff_isSquare_u (P : edwards.Point) :
    Even P ↔ IsSquare (edwards.toMontgomeryEquiv P).u := by
  rw [← AddSubgroup.mem_even, ← descent_eq_even, mem_descent,
    ← isSquare_toMontgomery_B_mul_u_iff, edwards_toMontgomery_B,
    isSquare_sq_mul_iff sqrtNegAAddTwo_ne_zero]

end curve25519
