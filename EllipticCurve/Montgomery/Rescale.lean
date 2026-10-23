/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.Montgomery.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public section

/-! # Montgomery models: rescaling

Two Montgomery models `M = (A, B)` and `M' = (A, B')` with the same `A` and `B' c² = B` for some
`c ≠ 0` have the same points up to the scaling `(u, v) ↦ (u, c v)` of the second coordinate:
`B v² = f(u)` gives `B' (c v)² = B' c² v² = B v² = f(u)`. This scaling is a group isomorphism
`rescaleEquiv M M' hA c hc hB : M.Point ≃+ M'.Point` (the chord and tangent slopes scale by
`c`, and the addition formulas `addU`, `addV` follow), pinned in both directions by
`rescaleEquiv_zero`, `rescaleEquiv_some`, `rescaleEquiv_symm_zero`, `rescaleEquiv_symm_some`
and the coordinate lemmas `u_rescaleEquiv`, `v_rescaleEquiv`, `u_rescaleEquiv_symm`,
`v_rescaleEquiv_symm`. The two models realise the same curve (`toCurve_eq_of_rescale`, from
`toCurve_eq_of_B_eq_mul_sq`), and `M'` is nonsingular when `M` is (`isNonsingular_rescale`).

The relation is stated for two models rather than through a model `M.rescale c`, so that it
applies to models given by their own definitions (the Montgomery model of a twisted Edwards
model and the Montgomery model of the same curve with `B = 1`, for curve25519). -/

universe u

namespace MontgomeryModel

variable {F : Type u} [Field F]

/-! ### The equation under rescaling -/

/-- `(u, c v)` is on `M'` when `(u, v)` is on `M`, for `M'.A = M.A` and `M'.B c² = M.B`. -/
theorem equation_rescale {M M' : MontgomeryModel F} (hA : M'.A = M.A) {c : F}
    (hB : M'.B * c ^ 2 = M.B) {u v : F} (h : M.Equation u v) : M'.Equation u (c * v) := by
  unfold Equation at h ⊢
  rw [hA, mul_pow, ← mul_assoc, hB, h]

/-- The inverse relation: `M.B c⁻¹² = M'.B`. -/
theorem B_mul_inv_sq_of_rescale {M M' : MontgomeryModel F} {c : F} (hc : c ≠ 0)
    (hB : M'.B * c ^ 2 = M.B) : M.B * c⁻¹ ^ 2 = M'.B := by
  rw [← hB, mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, mul_one]

/-- `(u, v / c)` is on `M` when `(u, v)` is on `M'`, for `M'.A = M.A`, `M'.B c² = M.B` and
`c ≠ 0`. -/
theorem equation_rescale_div {M M' : MontgomeryModel F} (hA : M'.A = M.A) {c : F} (hc : c ≠ 0)
    (hB : M'.B * c ^ 2 = M.B) {u v : F} (h : M'.Equation u v) : M.Equation u (v / c) := by
  rw [div_eq_inv_mul]
  exact equation_rescale hA.symm (B_mul_inv_sq_of_rescale hc hB) h

/-- A model related to a nonsingular model by rescaling is nonsingular. Not an instance, since
the relation is a hypothesis. -/
theorem isNonsingular_rescale (M M' : MontgomeryModel F) [M.IsNonsingular] (hA : M'.A = M.A)
    {c : F} (hB : M'.B * c ^ 2 = M.B) : M'.IsNonsingular where
  two_ne_zero := IsNonsingular.two_ne_zero (M := M)
  B_ne_zero := fun h => IsNonsingular.B_ne_zero (M := M) (by rw [← hB, h, zero_mul])
  A_sq_ne_four := by
    rw [hA]
    exact IsNonsingular.A_sq_ne_four

/-- Two models related by rescaling realise the same curve. -/
theorem toCurve_eq_of_rescale (M M' : MontgomeryModel F) [M.IsNonsingular] [M'.IsNonsingular]
    (hA : M'.A = M.A) (c : F) (hc : c ≠ 0) (hB : M'.B * c ^ 2 = M.B) :
    M'.toCurve = M.toCurve :=
  (toCurve_eq_of_B_eq_mul_sq M' M hA.symm hc hB.symm).symm

/-! ### The addition formulas under rescaling -/

/-- The chord slope scales by `c`. -/
theorem chordSlope_mul_left (c u₁ v₁ u₂ v₂ : F) :
    chordSlope u₁ (c * v₁) u₂ (c * v₂) = c * chordSlope u₁ v₁ u₂ v₂ := by
  unfold chordSlope
  rw [← mul_sub, mul_div_assoc]

/-- The tangent slope scales by `c` under rescaling. -/
theorem tangentSlope_rescale {M M' : MontgomeryModel F} (hA : M'.A = M.A) {c : F} (hc : c ≠ 0)
    (hB : M'.B * c ^ 2 = M.B) (u v : F) :
    M'.tangentSlope u (c * v) = c * M.tangentSlope u v := by
  unfold tangentSlope
  rw [hA, ← hB]
  by_cases hv : v = 0
  · simp [hv]
  · field_simp

/-- `addU` is unchanged under rescaling, with the slope scaled by `c`. -/
theorem addU_rescale {M M' : MontgomeryModel F} (hA : M'.A = M.A) {c : F}
    (hB : M'.B * c ^ 2 = M.B) (u₁ u₂ ℓ : F) : M'.addU u₁ u₂ (c * ℓ) = M.addU u₁ u₂ ℓ := by
  unfold addU
  rw [hA, ← hB]
  ring

/-- `addV` scales by `c` under rescaling, with the slope scaled by `c`. -/
theorem addV_rescale {M M' : MontgomeryModel F} (hA : M'.A = M.A) {c : F}
    (hB : M'.B * c ^ 2 = M.B) (u₁ u₂ v₁ ℓ : F) :
    M'.addV u₁ u₂ (c * v₁) (c * ℓ) = c * M.addV u₁ u₂ v₁ ℓ := by
  unfold addV
  rw [addU_rescale hA hB]
  ring

/-! ### The group isomorphism -/

/-- The map `(u, v) ↦ (u, c v)` on points. Internal. -/
private def rescaleFun {M M' : MontgomeryModel F} (hA : M'.A = M.A) {c : F}
    (hB : M'.B * c ^ 2 = M.B) : M.Point → M'.Point
  | .zero => .zero
  | .some u v h => .some u (c * v) (equation_rescale hA hB h)

private theorem rescaleFun_rescaleFun {M M' : MontgomeryModel F} (hA : M'.A = M.A)
    (hA' : M.A = M'.A) {c c' : F} (hcc : c' * c = 1) (hB : M'.B * c ^ 2 = M.B)
    (hB' : M.B * c' ^ 2 = M'.B) (P : M.Point) : rescaleFun hA' hB' (rescaleFun hA hB P) = P := by
  cases P with
  | zero => rfl
  | some u v h =>
    simp only [rescaleFun, Point.some.injEq, true_and]
    rw [← mul_assoc, hcc, one_mul]

private theorem rescaleFun_add {M M' : MontgomeryModel F} [M.IsNonsingular] [M'.IsNonsingular]
    (hA : M'.A = M.A) {c : F} (hc : c ≠ 0) (hB : M'.B * c ^ 2 = M.B) (P Q : M.Point) :
    rescaleFun hA hB (P + Q) = rescaleFun hA hB P + rescaleFun hA hB Q := by
  rcases Point.cases P with rfl | ⟨u₁, v₁, h₁, rfl⟩
  · rw [zero_add, zero_def]
    change _ = Point.zero + _
    rw [← zero_def, zero_add]
  rcases Point.cases Q with rfl | ⟨u₂, v₂, h₂, rfl⟩
  · rw [add_zero, zero_def]
    change _ = _ + Point.zero
    rw [← zero_def, add_zero]
  change _ = Point.some u₁ (c * v₁) _ + Point.some u₂ (c * v₂) _
  by_cases hu : u₁ = u₂
  · by_cases hv : v₁ = -v₂
    · rw [some_add_some_eq_zero h₁ h₂ hu hv, some_add_some_eq_zero _ _ hu (by rw [hv, mul_neg]),
        zero_def, zero_def]
      rfl
    · have hv' : c * v₁ ≠ -(c * v₂) := fun h => hv (mul_left_cancel₀ hc (by rw [h, mul_neg]))
      rw [some_add_some_of_v_ne h₁ h₂ hu hv, some_add_some_of_v_ne _ _ hu hv']
      simp only [rescaleFun, Point.some.injEq]
      rw [tangentSlope_rescale hA hc hB, addU_rescale hA hB, addV_rescale hA hB]
      exact ⟨rfl, rfl⟩
  · rw [some_add_some_of_u_ne h₁ h₂ hu, some_add_some_of_u_ne _ _ hu]
    simp only [rescaleFun, Point.some.injEq]
    rw [chordSlope_mul_left, addU_rescale hA hB, addV_rescale hA hB]
    exact ⟨rfl, rfl⟩

/-- **Rescaling**: for models `M`, `M'` with `M'.A = M.A` and `M'.B c² = M.B` (`c ≠ 0`), the
group isomorphism `M.Point ≃+ M'.Point`, `(u, v) ↦ (u, c v)`. Hidden; characterised by
`rescaleEquiv_zero`, `rescaleEquiv_some`, `rescaleEquiv_symm_zero`, `rescaleEquiv_symm_some`,
`u_rescaleEquiv`, `v_rescaleEquiv`, `u_rescaleEquiv_symm`, `v_rescaleEquiv_symm`. -/
def rescaleEquiv (M M' : MontgomeryModel F) [M.IsNonsingular] [M'.IsNonsingular]
    (hA : M'.A = M.A) (c : F) (hc : c ≠ 0) (hB : M'.B * c ^ 2 = M.B) : M.Point ≃+ M'.Point where
  toFun := rescaleFun hA hB
  invFun := rescaleFun hA.symm (B_mul_inv_sq_of_rescale hc hB)
  left_inv := rescaleFun_rescaleFun hA hA.symm (inv_mul_cancel₀ hc) hB _
  right_inv := rescaleFun_rescaleFun hA.symm hA (mul_inv_cancel₀ hc) _ hB
  map_add' := rescaleFun_add hA hc hB

section

variable (M M' : MontgomeryModel F) [M.IsNonsingular] [M'.IsNonsingular] (hA : M'.A = M.A)
  (c : F) (hc : c ≠ 0) (hB : M'.B * c ^ 2 = M.B)

/-- Rescaling fixes the point at infinity. -/
theorem rescaleEquiv_zero : rescaleEquiv M M' hA c hc hB 0 = 0 :=
  map_zero _

/-- Rescaling sends `(u, v)` to `(u, c v)`. -/
theorem rescaleEquiv_some {u v : F} (h : M.Equation u v) :
    rescaleEquiv M M' hA c hc hB (.some u v h) = .some u (c * v) (equation_rescale hA hB h) := by
  rfl

/-- The inverse of rescaling fixes the point at infinity. -/
theorem rescaleEquiv_symm_zero : (rescaleEquiv M M' hA c hc hB).symm 0 = 0 :=
  map_zero _

/-- The inverse of rescaling sends `(u, v)` to `(u, v / c)`. -/
theorem rescaleEquiv_symm_some {u v : F} (h : M'.Equation u v) :
    (rescaleEquiv M M' hA c hc hB).symm (.some u v h) =
      .some u (v / c) (equation_rescale_div hA hc hB h) := by
  change Point.some u (c⁻¹ * v) _ = _
  rw [Point.some.injEq, div_eq_inv_mul]
  exact ⟨rfl, rfl⟩

/-- Rescaling preserves the `u`-coordinate. -/
@[simp]
theorem u_rescaleEquiv (P : M.Point) : (rescaleEquiv M M' hA c hc hB P).u = P.u := by
  rcases Point.cases P with rfl | ⟨u, v, h, rfl⟩
  · rw [rescaleEquiv_zero, u_zero, u_zero]
  · rw [rescaleEquiv_some, u_some, u_some]

/-- Rescaling multiplies the `v`-coordinate by `c`. -/
@[simp]
theorem v_rescaleEquiv (P : M.Point) : (rescaleEquiv M M' hA c hc hB P).v = c * P.v := by
  rcases Point.cases P with rfl | ⟨u, v, h, rfl⟩
  · rw [rescaleEquiv_zero, v_zero, v_zero, mul_zero]
  · rw [rescaleEquiv_some, v_some, v_some]

/-- The inverse of rescaling preserves the `u`-coordinate. -/
@[simp]
theorem u_rescaleEquiv_symm (Q : M'.Point) :
    ((rescaleEquiv M M' hA c hc hB).symm Q).u = Q.u := by
  rcases Point.cases Q with rfl | ⟨u, v, h, rfl⟩
  · rw [rescaleEquiv_symm_zero, u_zero, u_zero]
  · rw [rescaleEquiv_symm_some, u_some, u_some]

/-- The inverse of rescaling divides the `v`-coordinate by `c`. -/
@[simp]
theorem v_rescaleEquiv_symm (Q : M'.Point) :
    ((rescaleEquiv M M' hA c hc hB).symm Q).v = Q.v / c := by
  rcases Point.cases Q with rfl | ⟨u, v, h, rfl⟩
  · rw [rescaleEquiv_symm_zero, v_zero, v_zero, zero_div]
  · rw [rescaleEquiv_symm_some, v_some, v_some]

end

end MontgomeryModel
