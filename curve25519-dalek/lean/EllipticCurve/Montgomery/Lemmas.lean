/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.Montgomery.Defs
import all EllipticCurve.Montgomery.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
public section

/-! # Montgomery models: characterising lemmas

The audited statements about `MontgomeryModel`: the defining equation of `twist`, the
coordinates `u`, `v`, the group law on `M.Point` in Montgomery coordinates (`zero_def`,
`neg_some`, the chord-and-tangent formulas `some_add_some_of_u_ne`, `some_add_some_of_v_ne`,
`some_add_some_eq_zero`), and `pointEquiv_zero`. These lemmas are the whole interface to the
hidden constructions of `EllipticCurve.Montgomery.Defs`: importers never see the bodies, and a
different construction of the group would only change the proofs here. -/

universe u

namespace MontgomeryModel

variable {F : Type u} [Field F] {M : MontgomeryModel F}

/-! ### The equation and the twist -/

/-- The equation in terms of `rhs`. -/
theorem equation_iff_rhs {u v : F} : M.Equation u v ↔ M.B * v ^ 2 = M.rhs u :=
  Iff.rfl

/-- If `(u, v)` is on the model then so is `(u, -v)`. -/
theorem equation_neg {u v : F} (h : M.Equation u v) : M.Equation u (-v) := by
  unfold Equation at h ⊢
  rwa [neg_sq]

/-- The defining equation of `twist`. -/
theorem twist_def (M : MontgomeryModel F) (c : F) : M.twist c = ⟨M.A, M.B * c⟩ := by
  rfl

/-- The twist keeps `A`. -/
@[simp]
theorem twist_A (M : MontgomeryModel F) (c : F) : (M.twist c).A = M.A := by
  rw [twist_def]

/-- The twist scales `B` by `c`. -/
@[simp]
theorem twist_B (M : MontgomeryModel F) (c : F) : (M.twist c).B = M.B * c := by
  rw [twist_def]

/-! ### Coordinates -/

/-- The `u`-coordinate of an affine point. -/
@[simp]
theorem u_some {u v : F} (h : M.Equation u v) : (Point.some u v h).u = u := by
  rfl

/-- The `v`-coordinate of an affine point. -/
@[simp]
theorem v_some {u v : F} (h : M.Equation u v) : (Point.some u v h).v = v := by
  rfl

/-! The chord-and-tangent formulas. The Weierstrass coordinates of the sum, in terms of the
Weierstrass slope, are `B` and `B²` times our `addU` and `addV` in terms of our slope. -/

private theorem addX_eq (u₁ u₂ ℓ : F) :
    M.toWeierstrass.addX (M.B * u₁) (M.B * u₂) (M.B * ℓ) = M.B * M.addU u₁ u₂ ℓ := by
  simp only [WeierstrassCurve.Affine.addX, toWeierstrass, addU]
  ring

private theorem addY_eq (u₁ u₂ v₁ ℓ : F) :
    M.toWeierstrass.addY (M.B * u₁) (M.B * u₂) (M.B ^ 2 * v₁) (M.B * ℓ) =
      M.B ^ 2 * M.addV u₁ u₂ v₁ ℓ := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, toWeierstrass, addV, addU]
  ring

/-! ### The group law

Everything below assumes `M.IsNonsingular`, which is what gives `M.Point` its group structure. -/

variable [M.IsNonsingular]

/-- The zero of the group is the point at infinity. -/
theorem zero_def : (0 : M.Point) = .zero := by
  rw [zero_eq]
  rfl

/-- The `u`-coordinate of the point at infinity is `0`, by convention. -/
@[simp]
theorem u_zero : (0 : M.Point).u = 0 := by
  rw [zero_def]
  rfl

/-- The `v`-coordinate of the point at infinity is `0`, by convention. -/
@[simp]
theorem v_zero : (0 : M.Point).v = 0 := by
  rw [zero_def]
  rfl

/-- Every point is `0` or an affine point `some u v h`. -/
theorem Point.cases (P : M.Point) : P = 0 ∨ ∃ u v h, P = Point.some u v h := by
  cases P with
  | zero => exact Or.inl zero_def.symm
  | some u v h => exact Or.inr ⟨u, v, h, rfl⟩

/-- Affine points are not the point at infinity. -/
theorem some_ne_zero {u v : F} (h : M.Equation u v) : Point.some u v h ≠ 0 := by
  rw [zero_def]
  exact nofun

/-- Negation flips the sign of `v`. -/
@[simp]
theorem neg_some {u v : F} (h : M.Equation u v) :
    -Point.some u v h = Point.some u (-v) (equation_neg h) := by
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  rw [neg_eq, pointEquivWeierstrass_some, WeierstrassCurve.Affine.Point.neg_some,
    pointEquivWeierstrass_symm_some, Point.some.injEq]
  simp only [WeierstrassCurve.Affine.negY, toWeierstrass, zero_mul, sub_zero]
  refine ⟨mul_div_cancel_left₀ u hB, ?_⟩
  rw [div_eq_iff (pow_ne_zero 2 hB)]
  ring

/-- Negation preserves the `u`-coordinate. -/
@[simp]
theorem u_neg (P : M.Point) : (-P).u = P.u := by
  rcases Point.cases P with rfl | ⟨u, v, h, rfl⟩
  · rw [neg_zero]
  · rw [neg_some, u_some, u_some]

/-- Negation negates the `v`-coordinate. -/
@[simp]
theorem v_neg (P : M.Point) : (-P).v = -P.v := by
  rcases Point.cases P with rfl | ⟨u, v, h, rfl⟩
  · rw [neg_zero, v_zero, neg_zero]
  · rw [neg_some, v_some, v_some]

open scoped Classical in
private theorem slope_eq_of_u_ne {u₁ v₁ u₂ v₂ : F} (hu : u₁ ≠ u₂) :
    M.toWeierstrass.slope (M.B * u₁) (M.B * u₂) (M.B ^ 2 * v₁) (M.B ^ 2 * v₂) =
      M.B * chordSlope u₁ v₁ u₂ v₂ := by
  classical
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  have hu' : M.B * u₁ ≠ M.B * u₂ := fun h => hu (mul_left_cancel₀ hB h)
  rw [WeierstrassCurve.Affine.slope_of_X_ne hu', chordSlope]
  have h₁ : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr hu
  have h₂ : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  field_simp
  ring

open scoped Classical in
private theorem slope_eq_of_v_ne {u₁ v₁ u₂ v₂ : F} (hu : u₁ = u₂) (hv : v₁ ≠ -v₂) :
    M.toWeierstrass.slope (M.B * u₁) (M.B * u₂) (M.B ^ 2 * v₁) (M.B ^ 2 * v₂) =
      M.B * M.tangentSlope u₁ v₁ := by
  classical
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  have hv' : M.B ^ 2 * v₁ ≠ M.toWeierstrass.negY (M.B * u₂) (M.B ^ 2 * v₂) := by
    simp only [WeierstrassCurve.Affine.negY, toWeierstrass, zero_mul, sub_zero]
    intro h
    exact hv (mul_left_cancel₀ (pow_ne_zero 2 hB) (by rw [h]; ring))
  rw [WeierstrassCurve.Affine.slope_of_Y_ne (by rw [hu]) hv', tangentSlope]
  simp only [WeierstrassCurve.Affine.negY, toWeierstrass, zero_mul, sub_zero]
  by_cases hv₁ : v₁ = 0
  · simp [hv₁]
  · field_simp
    ring

open scoped Classical in
/-- The equation at the sum of two affine points that are not inverse to each other, given the
Weierstrass slope as `B` times a Montgomery slope `ℓ`. -/
private theorem equation_add_of_slope {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁)
    (h₂ : M.Equation u₂ v₂) (hxy : ¬(M.B * u₁ = M.B * u₂ ∧
      M.B ^ 2 * v₁ = M.toWeierstrass.negY (M.B * u₂) (M.B ^ 2 * v₂))) (ℓ : F)
    (hℓ : M.toWeierstrass.slope (M.B * u₁) (M.B * u₂) (M.B ^ 2 * v₁) (M.B ^ 2 * v₂) = M.B * ℓ) :
    M.Equation (M.addU u₁ u₂ ℓ) (M.addV u₁ u₂ v₁ ℓ) := by
  rw [M.equation_iff_toWeierstrass IsNonsingular.B_ne_zero, ← addX_eq, ← addY_eq, ← hℓ]
  exact (WeierstrassCurve.Affine.nonsingular_add (M.nonsingular_mul h₁) (M.nonsingular_mul h₂)
    hxy).1

open scoped Classical in
/-- The sum of two affine points that are not inverse to each other, given the Weierstrass slope
as `B` times a Montgomery slope `ℓ`. -/
private theorem some_add_some_eq {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁)
    (h₂ : M.Equation u₂ v₂) (hxy : ¬(M.B * u₁ = M.B * u₂ ∧
      M.B ^ 2 * v₁ = M.toWeierstrass.negY (M.B * u₂) (M.B ^ 2 * v₂))) (ℓ : F)
    (hℓ : M.toWeierstrass.slope (M.B * u₁) (M.B * u₂) (M.B ^ 2 * v₁) (M.B ^ 2 * v₂) = M.B * ℓ) :
    Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ =
      Point.some (M.addU u₁ u₂ ℓ) (M.addV u₁ u₂ v₁ ℓ) (equation_add_of_slope h₁ h₂ hxy ℓ hℓ) := by
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  rw [add_eq, pointEquivWeierstrass_some, pointEquivWeierstrass_some,
    WeierstrassCurve.Affine.Point.add_some hxy, pointEquivWeierstrass_symm_some, Point.some.injEq,
    hℓ, addX_eq, addY_eq, mul_div_cancel_left₀ _ hB, mul_div_cancel_left₀ _ (pow_ne_zero 2 hB)]
  exact ⟨rfl, rfl⟩

private theorem not_inverse_of_u_ne {u₁ v₁ u₂ v₂ : F} (hu : u₁ ≠ u₂) :
    ¬(M.B * u₁ = M.B * u₂ ∧ M.B ^ 2 * v₁ = M.toWeierstrass.negY (M.B * u₂) (M.B ^ 2 * v₂)) :=
  fun h => hu (mul_left_cancel₀ IsNonsingular.B_ne_zero h.1)

private theorem not_inverse_of_v_ne {u₁ v₁ u₂ v₂ : F} (hv : v₁ ≠ -v₂) :
    ¬(M.B * u₁ = M.B * u₂ ∧ M.B ^ 2 * v₁ = M.toWeierstrass.negY (M.B * u₂) (M.B ^ 2 * v₂)) := by
  simp only [WeierstrassCurve.Affine.negY, toWeierstrass, zero_mul, sub_zero]
  intro h
  exact hv (mul_left_cancel₀ (pow_ne_zero 2 IsNonsingular.B_ne_zero) (by rw [h.2]; ring))

private theorem ne_neg_self (h2 : (2 : F) ≠ 0) {v : F} (hv : v ≠ 0) : v ≠ -v := fun h =>
  hv (mul_left_cancel₀ h2 (by linear_combination h))

/-- The chord through two affine points with distinct `u`-coordinates meets the model again. -/
theorem equation_add_of_u_ne {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁) (h₂ : M.Equation u₂ v₂)
    (hu : u₁ ≠ u₂) :
    M.Equation (M.addU u₁ u₂ (chordSlope u₁ v₁ u₂ v₂))
      (M.addV u₁ u₂ v₁ (chordSlope u₁ v₁ u₂ v₂)) :=
  equation_add_of_slope h₁ h₂ (not_inverse_of_u_ne hu) _ (slope_eq_of_u_ne hu)

/-- The chord-and-tangent formula for two affine points with distinct `u`-coordinates:
`(u₁, v₁) + (u₂, v₂) = (B ℓ² - A - u₁ - u₂, ℓ (u₁ - u₃) - v₁)` with `ℓ = (v₂ - v₁) / (u₂ - u₁)`. -/
theorem some_add_some_of_u_ne {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁) (h₂ : M.Equation u₂ v₂)
    (hu : u₁ ≠ u₂) :
    Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ =
      Point.some (M.addU u₁ u₂ (chordSlope u₁ v₁ u₂ v₂))
        (M.addV u₁ u₂ v₁ (chordSlope u₁ v₁ u₂ v₂)) (equation_add_of_u_ne h₁ h₂ hu) :=
  some_add_some_eq h₁ h₂ (not_inverse_of_u_ne hu) _ (slope_eq_of_u_ne hu)

/-- The tangent at an affine point `(u₁, v₁)` with `v₁ ≠ 0` meets the model again (stated for
`(u₂, v₂)` with `u₂ = u₁` and `v₂ ≠ -v₁`, which forces `(u₂, v₂) = (u₁, v₁)`). -/
theorem equation_add_of_v_ne {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁) (h₂ : M.Equation u₂ v₂)
    (hu : u₁ = u₂) (hv : v₁ ≠ -v₂) :
    M.Equation (M.addU u₁ u₂ (M.tangentSlope u₁ v₁)) (M.addV u₁ u₂ v₁ (M.tangentSlope u₁ v₁)) :=
  equation_add_of_slope h₁ h₂ (not_inverse_of_v_ne hv) _ (slope_eq_of_v_ne hu hv)

/-- The chord-and-tangent formula for two affine points with the same `u`-coordinate that are
not inverse to each other (so that they coincide, with `v₁ ≠ 0`): the tangent formula,
`ℓ = (3 u₁² + 2 A u₁ + 1) / (2 B v₁)`. -/
theorem some_add_some_of_v_ne {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁) (h₂ : M.Equation u₂ v₂)
    (hu : u₁ = u₂) (hv : v₁ ≠ -v₂) :
    Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ =
      Point.some (M.addU u₁ u₂ (M.tangentSlope u₁ v₁)) (M.addV u₁ u₂ v₁ (M.tangentSlope u₁ v₁))
        (equation_add_of_v_ne h₁ h₂ hu hv) :=
  some_add_some_eq h₁ h₂ (not_inverse_of_v_ne hv) _ (slope_eq_of_v_ne hu hv)

/-- The tangent at an affine point with `v ≠ 0` meets the model again. -/
theorem equation_add_self {u v : F} (h : M.Equation u v) (hv : v ≠ 0) :
    M.Equation (M.addU u u (M.tangentSlope u v)) (M.addV u u v (M.tangentSlope u v)) :=
  equation_add_of_v_ne h h rfl (ne_neg_self (IsNonsingular.two_ne_zero (M := M)) hv)

/-- Doubling an affine point with `v ≠ 0`: the tangent formula. -/
theorem some_add_self {u v : F} (h : M.Equation u v) (hv : v ≠ 0) :
    Point.some u v h + Point.some u v h =
      Point.some (M.addU u u (M.tangentSlope u v)) (M.addV u u v (M.tangentSlope u v))
        (equation_add_self h hv) :=
  some_add_some_of_v_ne h h rfl (ne_neg_self (IsNonsingular.two_ne_zero (M := M)) hv)

/-- Two affine points with the same `u`-coordinate and opposite `v`-coordinates are inverse. -/
theorem some_add_some_eq_zero {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁) (h₂ : M.Equation u₂ v₂)
    (hu : u₁ = u₂) (hv : v₁ = -v₂) : Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ = 0 := by
  classical
  rw [add_eq, pointEquivWeierstrass_some, pointEquivWeierstrass_some,
    WeierstrassCurve.Affine.Point.add_of_Y_eq (by rw [hu]) (by
      simp only [WeierstrassCurve.Affine.negY, toWeierstrass, zero_mul, sub_zero, hv]
      ring), zero_def]
  rfl

/-! ### The curve -/

/-- `pointEquiv` sends the point at infinity to the zero of the curve. -/
@[simp]
theorem pointEquiv_zero : M.pointEquiv 0 = 0 :=
  map_zero _

end MontgomeryModel
