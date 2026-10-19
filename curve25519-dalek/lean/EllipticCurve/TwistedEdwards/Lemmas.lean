/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Defs
import all EllipticCurve.TwistedEdwards.Defs
import EllipticCurve.Proofs.TwistedEdwards.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public section

/-! # Twisted Edwards models: characterising lemmas

The audited statements about `TwistedEdwardsModel`: completeness of the addition formula
(`addDen₁_ne_zero`, `addDen₂_ne_zero`, `equation_addX_addY`), the group law on `E.Point` in
coordinates (`zero_x`, `zero_y`, `neg_x`, `neg_y`, `add_x`, `add_y`), the computable scalar
multiplication `nsmulBinary` with `nsmulBinary_eq`, the curve (`toCurve_toMontgomery`,
`pointEquiv_eq`) and the coordinate lemmas pinning `toMontgomeryEquiv` in both directions
(`u_toMontgomeryEquiv`, `v_toMontgomeryEquiv`, `toMontgomeryEquiv_of_y_eq_one`,
`toMontgomeryEquiv_of_x_eq_zero`, `toMontgomeryEquiv_symm_x`, `toMontgomeryEquiv_symm_y`).
These lemmas are the whole interface to the hidden constructions of
`EllipticCurve.TwistedEdwards.Defs`: importers never see the bodies, and a different
construction of the group would only change the proofs here and in
`EllipticCurve.Proofs.TwistedEdwards.Group` (not audited), whose results this module
re-exports. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F}

/-! ### The addition formula on a complete model -/

section IsComplete

variable [E.IsComplete]

/-- Completeness: the denominator `1 + d x₁ x₂ y₁ y₂` is nonzero. -/
theorem addDen₁_ne_zero (P Q : E.Point) : addDen₁ P Q ≠ 0 :=
  Proofs.addDen₁_ne_zero P Q

/-- Completeness: the denominator `1 - d x₁ x₂ y₁ y₂` is nonzero. -/
theorem addDen₂_ne_zero (P Q : E.Point) : addDen₂ P Q ≠ 0 :=
  Proofs.addDen₂_ne_zero P Q

/-- Closure: the addition formula lands on the model. -/
theorem equation_addX_addY (P Q : E.Point) : E.Equation (addX P Q) (addY P Q) :=
  Proofs.equation_addX_addY P Q

/-! ### The group law in coordinates -/

/-- The zero of the group is `(0, 1)`: `x`-coordinate. -/
@[simp]
theorem zero_x : (0 : E.Point).x = 0 := by
  rw [zero_eq, MontgomeryModel.zero_def]
  rfl

/-- The zero of the group is `(0, 1)`: `y`-coordinate. -/
@[simp]
theorem zero_y : (0 : E.Point).y = 1 := by
  rw [zero_eq, MontgomeryModel.zero_def]
  rfl

/-- Negation is `(x, y) ↦ (-x, y)`: `x`-coordinate. -/
@[simp]
theorem neg_x (P : E.Point) : (-P).x = -P.x := by
  rw [neg_eq]
  by_cases hy : P.y = 1
  · rw [toMontgomeryEquivAux_apply_of_y_eq_one hy, ← MontgomeryModel.zero_def, neg_zero,
      MontgomeryModel.zero_def, x_eq_zero_of_y_eq_one P.equation hy, neg_zero]
    rfl
  · conv_rhs => rw [← E.toMontgomeryEquivAux.symm_apply_apply P]
    rw [toMontgomeryEquivAux_apply_of_y_ne_one hy, MontgomeryModel.neg_some,
      toMontgomeryEquivAux_symm_some, toMontgomeryEquivAux_symm_some]
    exact div_neg _

/-- Negation is `(x, y) ↦ (-x, y)`: `y`-coordinate. -/
@[simp]
theorem neg_y (P : E.Point) : (-P).y = P.y := by
  rw [neg_eq]
  by_cases hy : P.y = 1
  · rw [toMontgomeryEquivAux_apply_of_y_eq_one hy, ← MontgomeryModel.zero_def, neg_zero,
      MontgomeryModel.zero_def, hy]
    rfl
  · conv_rhs => rw [← E.toMontgomeryEquivAux.symm_apply_apply P]
    rw [toMontgomeryEquivAux_apply_of_y_ne_one hy, MontgomeryModel.neg_some,
      toMontgomeryEquivAux_symm_some, toMontgomeryEquivAux_symm_some]

/-- The sum of two points, as a point: the addition formula. -/
theorem add_eq_mk (P Q : E.Point) : P + Q = ⟨addX P Q, addY P Q, equation_addX_addY P Q⟩ :=
  Proofs.add_eq_mk P Q

/-- **The group law in coordinates**: the `x`-coordinate of the sum is
`(x₁ y₂ + x₂ y₁) / (1 + d x₁ x₂ y₁ y₂)`. -/
@[simp]
theorem add_x (P Q : E.Point) : (P + Q).x = addX P Q := by
  rw [add_eq_mk]

/-- **The group law in coordinates**: the `y`-coordinate of the sum is
`(y₁ y₂ - a x₁ x₂) / (1 - d x₁ x₂ y₁ y₂)`. -/
@[simp]
theorem add_y (P Q : E.Point) : (P + Q).y = addY P Q := by
  rw [add_eq_mk]

/-- The `x`-coordinate of a difference. -/
theorem sub_x (P Q : E.Point) : (P - Q).x = addX P (-Q) := by
  rw [sub_eq_add_neg, add_x]

/-- The `y`-coordinate of a difference. -/
theorem sub_y (P Q : E.Point) : (P - Q).y = addY P (-Q) := by
  rw [sub_eq_add_neg, add_y]

/-- The `x`-coordinate of a double. -/
theorem two_nsmul_x (P : E.Point) : (2 • P).x = addX P P := by
  rw [two_nsmul, add_x]

/-- The `y`-coordinate of a double. -/
theorem two_nsmul_y (P : E.Point) : (2 • P).y = addY P P := by
  rw [two_nsmul, add_y]

/-- The `2`-torsion of a complete model is `{(0, 1), (0, -1)}`: `2 • P = 0` exactly when
`P.x = 0`. -/
theorem two_nsmul_eq_zero_iff (P : E.Point) : 2 • P = 0 ↔ P.x = 0 := by
  have hd2 : 1 - E.d * P.x * P.x * P.y * P.y ≠ 0 := addDen₂_ne_zero P P
  have hPe := P.equation
  unfold Equation at hPe
  rw [Point.ext_iff, two_nsmul_x, two_nsmul_y, zero_x, zero_y]
  constructor
  · rintro ⟨hx, hy⟩
    unfold addX addDen₁ at hx
    rw [div_eq_zero_iff] at hx
    rcases hx with hx | hx
    · rcases mul_eq_zero.mp (show (2 * P.x) * P.y = 0 by linear_combination hx) with h | h
      · exact (mul_eq_zero.mp h).resolve_left (IsComplete.two_ne_zero (E := E))
      · exfalso
        unfold addY addDen₂ at hy
        rw [div_eq_one_iff_eq hd2, h] at hy
        rw [h] at hPe
        exact IsComplete.two_ne_zero (E := E) (by linear_combination -hy - hPe)
    · exact absurd hx (addDen₁_ne_zero P P)
  · intro hx
    have hy := y_sq_eq_one_of_x_eq_zero P.equation hx
    refine ⟨?_, ?_⟩
    · unfold addX addDen₁
      rw [hx]
      ring
    · unfold addY addDen₂
      rw [hx]
      simp only [mul_zero, zero_mul, sub_zero, div_one]
      linear_combination hy

/-! ### Computable scalar multiplication -/

/-- The binary method with fuel `k`: `nsmulBinaryAux P k n = n • P` for `n < 2 ^ k`
(`nsmulBinaryAux_eq`), by the exposed addition formula. -/
@[expose] def nsmulBinaryAux (P : E.Point) : ℕ → ℕ → E.Point
  | 0, _ => ⟨0, 1, E.equation_zero_one⟩
  | k + 1, n =>
    if n = 0 then ⟨0, 1, E.equation_zero_one⟩
    else
      let Q := nsmulBinaryAux P k (n / 2)
      let Q₂ : E.Point := ⟨addX Q Q, addY Q Q, equation_addX_addY Q Q⟩
      if n % 2 = 0 then Q₂ else ⟨addX Q₂ P, addY Q₂ P, equation_addX_addY Q₂ P⟩

/-- Computable scalar multiplication `n • P` by the binary method on the exposed addition
formula, for `decide` on constants (`nsmulBinary_eq`). -/
@[expose] def nsmulBinary (n : ℕ) (P : E.Point) : E.Point :=
  nsmulBinaryAux P n n

/-- `(0, 1)` is the zero of the group. -/
theorem zero_eq_mk : (0 : E.Point) = ⟨0, 1, E.equation_zero_one⟩ :=
  Point.ext zero_x zero_y

/-- The binary method computes `n • P` given enough fuel. -/
theorem nsmulBinaryAux_eq (P : E.Point) (k n : ℕ) (hn : n < 2 ^ k) :
    nsmulBinaryAux P k n = n • P := by
  induction k generalizing n with
  | zero =>
    obtain rfl : n = 0 := by simpa using hn
    rw [zero_nsmul, zero_eq_mk]
    rfl
  | succ k ih =>
    have hQ := ih (n / 2) ((Nat.div_lt_iff_lt_mul two_pos).mpr (by rw [← pow_succ]; exact hn))
    simp only [nsmulBinaryAux]
    split_ifs with h0 h2
    · rw [h0, zero_nsmul, zero_eq_mk]
    · rw [← add_eq_mk, hQ, ← two_nsmul, smul_smul]
      congr 1
      omega
    · rw [← add_eq_mk, ← add_eq_mk, hQ, ← two_nsmul, smul_smul, ← succ_nsmul]
      congr 1
      omega

/-- The binary method computes `n • P`. -/
theorem nsmulBinary_eq (n : ℕ) (P : E.Point) : nsmulBinary n P = n • P :=
  nsmulBinaryAux_eq P n n Nat.lt_two_pow_self

/-! ### The curve -/

/-- The curve of the Montgomery model of `E` is the curve of `E`. -/
theorem toCurve_toMontgomery (E : TwistedEdwardsModel F) [E.IsComplete] :
    E.toMontgomery.toCurve = E.toCurve := by
  rfl

/-- `pointEquiv` factors through the Montgomery model. -/
theorem pointEquiv_eq (E : TwistedEdwardsModel F) [E.IsComplete] :
    E.pointEquiv = E.toMontgomeryEquiv.trans E.toMontgomery.pointEquiv := by
  rfl

/-! ### The equivalence with the Montgomery model, in coordinates -/

/-- The `u`-coordinate of the image of `P` is `(1 + y) / (1 - y)` (which is `0` at `(0, 1)`,
whose image is `∞`, as the convention `u ∞ = 0` requires). -/
theorem u_toMontgomeryEquiv (P : E.Point) :
    (E.toMontgomeryEquiv P).u = (1 + P.y) / (1 - P.y) := by
  rw [toMontgomeryEquiv_apply]
  by_cases hy : P.y = 1
  · rw [toMontgomeryEquivAux_apply_of_y_eq_one hy, ← MontgomeryModel.zero_def,
      MontgomeryModel.u_zero, hy, sub_self, div_zero]
  · rw [toMontgomeryEquivAux_apply_of_y_ne_one hy, MontgomeryModel.u_some]

/-- The `v`-coordinate of the image of `P` is `(1 + y) / ((1 - y) x)` away from `(0, 1)`. -/
theorem v_toMontgomeryEquiv (P : E.Point) (hy : P.y ≠ 1) :
    (E.toMontgomeryEquiv P).v = (1 + P.y) / ((1 - P.y) * P.x) := by
  rw [toMontgomeryEquiv_apply, toMontgomeryEquivAux_apply_of_y_ne_one hy,
    MontgomeryModel.v_some]

/-- The image of `(0, 1)` is the point at infinity. -/
theorem toMontgomeryEquiv_of_y_eq_one (P : E.Point) (h : P.y = 1) :
    E.toMontgomeryEquiv P = 0 := by
  rw [toMontgomeryEquiv_apply, toMontgomeryEquivAux_apply_of_y_eq_one h,
    MontgomeryModel.zero_def]

/-- The image of `(0, -1)` is `(0, 0)`. -/
theorem toMontgomeryEquiv_of_x_eq_zero (P : E.Point) (hx : P.x = 0) (hy : P.y = -1) :
    E.toMontgomeryEquiv P = .some 0 0 E.toMontgomery_equation_zero_zero := by
  have hy' : P.y ≠ 1 := by
    rw [hy]
    intro h
    exact IsComplete.two_ne_zero (E := E) (by linear_combination -h)
  rw [toMontgomeryEquiv_apply, toMontgomeryEquivAux_apply_of_y_ne_one hy']
  simp only [MontgomeryModel.Point.some.injEq, hx, hy]
  norm_num

/-- The `x`-coordinate of the preimage of a Montgomery point `Q` with `v ≠ 0` is `u / v`. -/
theorem toMontgomeryEquiv_symm_x (Q : E.toMontgomery.Point) (hv : Q.v ≠ 0) :
    (E.toMontgomeryEquiv.symm Q).x = Q.u / Q.v := by
  rcases MontgomeryModel.Point.cases Q with rfl | ⟨u, v, h, rfl⟩
  · exact absurd MontgomeryModel.v_zero hv
  · rw [toMontgomeryEquiv_symm_apply, toMontgomeryEquivAux_symm_some, MontgomeryModel.u_some,
      MontgomeryModel.v_some]

/-- The `y`-coordinate of the preimage of an affine Montgomery point `Q` is
`(u - 1) / (u + 1)` (for `Q = ∞`, whose `u` is `0` by convention, the preimage is `(0, 1)`). -/
theorem toMontgomeryEquiv_symm_y (Q : E.toMontgomery.Point) (hQ : Q ≠ 0) :
    (E.toMontgomeryEquiv.symm Q).y = (Q.u - 1) / (Q.u + 1) := by
  rcases MontgomeryModel.Point.cases Q with rfl | ⟨u, v, h, rfl⟩
  · exact absurd rfl hQ
  · rw [toMontgomeryEquiv_symm_apply, toMontgomeryEquivAux_symm_some, MontgomeryModel.u_some]

end IsComplete

end TwistedEdwardsModel
