/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.Montgomery.Lemmas
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public section

/-! # Montgomery models: counting points

Over a finite field `F` of odd characteristic, a Montgomery model `M` with `B ≠ 0` and its
quadratic twist `M.twist c` by a non-square `c` have `2 |F| + 2` points in total
(`card_add_card_twist`): for each `u`, the equations `B v² = f(u)` and `B c v² = f(u)` have two
solutions `v` between them (one each if `f(u) = 0`; otherwise exactly one of `f(u) / B`,
`f(u) / (B c)` is a square, with two square roots), and each model has its point at infinity.
The count is through the quadratic character: the number of square roots of `a` is
`χ(a) + 1`, and `χ(a / c) = -χ(a)`.

Also here: `M.Point` is finite when `F` is (`instFinitePoint`), and the equation is decidable
when equality in `F` is (`instDecidableEquation`). -/

universe u

namespace MontgomeryModel

variable {F : Type u} [Field F] {M : MontgomeryModel F}

/-- The equation is decidable when equality in `F` is. -/
instance instDecidableEquation [DecidableEq F] (M : MontgomeryModel F) (u v : F) :
    Decidable (M.Equation u v) :=
  inferInstanceAs (Decidable (M.B * v ^ 2 = u ^ 3 + M.A * u ^ 2 + u))

/-- The points of `M` as the point at infinity plus, for each `u`, the solutions `v`. -/
private def pointEquivSigma (M : MontgomeryModel F) :
    M.Point ≃ Option (Σ u : F, {v : F // M.Equation u v}) where
  toFun
    | .zero => none
    | .some u v h => some ⟨u, v, h⟩
  invFun
    | none => .zero
    | some ⟨u, v, h⟩ => .some u v h
  left_inv P := by
    cases P <;> rfl
  right_inv o := by
    rcases o with _ | ⟨u, v, h⟩ <;> rfl

instance instFinitePoint [Finite F] : Finite M.Point :=
  Finite.of_equiv _ (pointEquivSigma M).symm

/-- `Nat.card M.Point` as `1 + ∑ u, #{v | M.Equation u v}`. -/
private theorem natCard_point [Fintype F] [DecidableEq F] (M : MontgomeryModel F) :
    Nat.card M.Point = ∑ u : F, (Finset.univ.filter fun v => M.Equation u v).card + 1 := by
  rw [Nat.card_congr (pointEquivSigma M), Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_sigma]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Fintype.card_subtype]

/-- The equation at `u` as the square-root equation `v² = f(u) / B`. -/
private theorem equation_iff_sq_eq (hB : M.B ≠ 0) (u v : F) :
    M.Equation u v ↔ v ^ 2 = M.rhs u / M.B := by
  rw [equation_iff_rhs, eq_div_iff hB, mul_comm]

/-- The number of `v` with `M.Equation u v` is `χ(f(u) / B) + 1`. -/
private theorem card_filter_equation [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (hB : M.B ≠ 0) (u : F) :
    ((Finset.univ.filter fun v => M.Equation u v).card : ℤ) =
      quadraticChar F (M.rhs u / M.B) + 1 := by
  rw [← quadraticChar_card_sqrts hF, Set.toFinset_ofPred]
  congr 2
  exact Finset.filter_congr fun v _ => equation_iff_sq_eq hB u v

/-- `(2 : F) ≠ 0` gives odd characteristic. -/
private theorem ringChar_ne_two (h2 : (2 : F) ≠ 0) : ringChar F ≠ 2 := fun h =>
  h2 (by exact_mod_cast (ringChar.spec F 2).mpr (h ▸ dvd_rfl))

/-- For each `u`, the model and its twist by a non-square have two points with that
`u`-coordinate between them. -/
private theorem card_filter_add_card_filter_twist [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0)
    (hB : M.B ≠ 0) {c : F} (hc : ¬ IsSquare c) (u : F) :
    (Finset.univ.filter fun v => M.Equation u v).card +
      (Finset.univ.filter fun v => (M.twist c).Equation u v).card = 2 := by
  have hF := ringChar_ne_two h2
  have hc0 : c ≠ 0 := fun h => hc (h ▸ IsSquare.zero)
  have hBc : M.B * c ≠ 0 := mul_ne_zero hB hc0
  have h₁ := card_filter_equation hF hB u
  have h₂ := card_filter_equation (M := M.twist c) hF (by rw [twist_B]; exact hBc) u
  rw [twist_rhs, twist_B] at h₂
  have hχc : quadraticChar F c⁻¹ = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr (by
    rwa [isSquare_inv])
  have hdiv : M.rhs u / (M.B * c) = M.rhs u / M.B * c⁻¹ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc]
  rw [hdiv, map_mul, hχc] at h₂
  zify
  rw [h₁, h₂]
  ring

/-- **The point count of a model and its twist**: over a finite field of odd characteristic, a
model with `B ≠ 0` and its quadratic twist by a non-square `c` have `2 |F| + 2` points in
total. -/
theorem card_add_card_twist [Fintype F] (M : MontgomeryModel F) (h2 : (2 : F) ≠ 0)
    (hB : M.B ≠ 0) {c : F} (hc : ¬ IsSquare c) :
    Nat.card M.Point + Nat.card (M.twist c).Point = 2 * Fintype.card F + 2 := by
  classical
  rw [natCard_point, natCard_point, add_add_add_comm, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun u _ => card_filter_add_card_filter_twist h2 hB hc u,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

end MontgomeryModel
