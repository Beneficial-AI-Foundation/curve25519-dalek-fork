/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # The point map of a variable change

Mathlib's `WeierstrassCurve.VariableChange R` acts on Weierstrass curves (`C • W`): the curve
`C • W` is the model obtained from `W` by the substitution `(X, Y) ↦ (u² X + r, u³ Y + u² s X + t)`
(`WeierstrassCurve.variableChange_def`), so that `(x', y')` is on `C • W` exactly when
`(u² x' + r, u³ y' + u² s x' + t)` is on `W` (this is the direction of Mathlib's
`WeierstrassCurve.Affine.equation_iff_variableChange`). Mathlib provides the action and the
invariance of the discriminant and of the `j`-invariant, but not the induced map on points. This
module provides it, over a field `F`:

* `WeierstrassCurve.VariableChange.mapX`, `mapY`: the coordinates `x' = u⁻² (x - r)` and
  `y' = u⁻³ (y - s (x - r) - t)` of the image of a point `(x, y)` of `W` on `C • W`; `invX`,
  `invY`: the inverse substitution `(x', y') ↦ (u² x' + r, u³ y' + u² s x' + t)`;
* `WeierstrassCurve.Affine.equation_variableChange`, `nonsingular_variableChange`: the map
  preserves and reflects the equation and nonsingularity;
* `WeierstrassCurve.Affine.Point.variableChange C : W.Point ≃+ (C • W).Point`: the induced
  isomorphism of point groups, pinned by `variableChange_zero`, `variableChange_some`,
  `variableChange_symm_zero`, `variableChange_symm_some`.

Additivity is proved from the explicit addition formulas (`Point.add_some`, `Point.add_of_Y_eq`)
and the transformation of the slope, `ℓ' = u⁻¹ (ℓ - s)` (`variableChange_slope`), of `negY`
(`variableChange_negY`) and of `addX`, `addY` (`variableChange_addX`, `variableChange_addY`).
All identities are polynomial in `u⁻¹` (the coefficients of `C • W` only involve `u⁻¹`), so
they are closed by `ring` after unfolding; only the slope needs `field_simp`. -/

universe u

namespace WeierstrassCurve

variable {F : Type u} [Field F]

namespace VariableChange

variable (C : VariableChange F)

/-- The `x`-coordinate `u⁻² (x - r)` of the image of `(x, y)` under the variable change `C`. -/
@[expose] def mapX (x : F) : F :=
  (C.u : F)⁻¹ ^ 2 * (x - C.r)

/-- The `y`-coordinate `u⁻³ (y - s (x - r) - t)` of the image of `(x, y)` under the variable
change `C`. -/
@[expose] def mapY (x y : F) : F :=
  (C.u : F)⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)

/-- The `x`-coordinate `u² x + r` of the preimage of `(x, y)` under the variable change `C`. -/
@[expose] def invX (x : F) : F :=
  (C.u : F) ^ 2 * x + C.r

/-- The `y`-coordinate `u³ y + u² s x + t` of the preimage of `(x, y)` under the variable
change `C`. -/
@[expose] def invY (x y : F) : F :=
  (C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t

theorem mapX_invX (x : F) : C.mapX (C.invX x) = x := by
  simp only [mapX, invX]
  field_simp [C.u.ne_zero]
  ring

theorem mapY_invX_invY (x y : F) : C.mapY (C.invX x) (C.invY x y) = y := by
  simp only [mapY, invX, invY]
  field_simp [C.u.ne_zero]
  ring

theorem invX_mapX (x : F) : C.invX (C.mapX x) = x := by
  simp only [mapX, invX]
  field_simp [C.u.ne_zero]
  ring

theorem invY_mapX_mapY (x y : F) : C.invY (C.mapX x) (C.mapY x y) = y := by
  simp only [mapX, mapY, invY]
  field_simp [C.u.ne_zero]
  ring

theorem mapX_injective : Function.Injective C.mapX :=
  Function.LeftInverse.injective C.invX_mapX

theorem mapX_inj {x₁ x₂ : F} : C.mapX x₁ = C.mapX x₂ ↔ x₁ = x₂ :=
  C.mapX_injective.eq_iff

/-- At a fixed `x`-coordinate, `mapY` is injective in `y`. -/
theorem mapY_inj {x y₁ y₂ : F} : C.mapY x y₁ = C.mapY x y₂ ↔ y₁ = y₂ := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have := congr_arg (C.invY (C.mapX x)) h
  rwa [invY_mapX_mapY, invY_mapX_mapY] at this

end VariableChange

namespace Affine

variable (W : Affine F) (C : VariableChange F)

/-! ### The equation and nonsingularity -/

/-- The Weierstrass polynomial of `C • W` at the image of `(x, y)` is `u⁻⁶` times that of `W` at
`(x, y)`. -/
theorem evalEval_polynomial_variableChange (x y : F) :
    (C • W).polynomial.evalEval (C.mapX x) (C.mapY x y) =
      (C.u : F)⁻¹ ^ 6 * W.polynomial.evalEval x y := by
  simp only [evalEval_polynomial, VariableChange.mapX, VariableChange.mapY, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆,
    Units.val_inv_eq_inv_val]
  ring

/-- The `X`-derivative of `C • W` at the image of `(x, y)`: the chain rule. -/
theorem evalEval_polynomialX_variableChange (x y : F) :
    (C • W).polynomialX.evalEval (C.mapX x) (C.mapY x y) =
      (C.u : F)⁻¹ ^ 4 * (W.polynomialX.evalEval x y + C.s * W.polynomialY.evalEval x y) := by
  simp only [evalEval_polynomialX, evalEval_polynomialY, VariableChange.mapX,
    VariableChange.mapY, variableChange_a₁, variableChange_a₂, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  ring

/-- The `Y`-derivative of `C • W` at the image of `(x, y)`: the chain rule. -/
theorem evalEval_polynomialY_variableChange (x y : F) :
    (C • W).polynomialY.evalEval (C.mapX x) (C.mapY x y) =
      (C.u : F)⁻¹ ^ 3 * W.polynomialY.evalEval x y := by
  simp only [evalEval_polynomialY, VariableChange.mapX, VariableChange.mapY, variableChange_a₁,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  ring

/-- A point is on `W` exactly when its image is on `C • W`. -/
theorem equation_variableChange (x y : F) :
    W.Equation x y ↔ (C • W).Equation (C.mapX x) (C.mapY x y) := by
  rw [Equation, Equation, evalEval_polynomial_variableChange, mul_eq_zero,
    or_iff_right (pow_ne_zero 6 (inv_ne_zero C.u.ne_zero))]

/-- A point of `W` is nonsingular exactly when its image on `C • W` is. -/
theorem nonsingular_variableChange (x y : F) :
    W.Nonsingular x y ↔ (C • W).Nonsingular (C.mapX x) (C.mapY x y) := by
  have hu : (C.u : F)⁻¹ ≠ 0 := inv_ne_zero C.u.ne_zero
  rw [Nonsingular, Nonsingular, ← equation_variableChange, evalEval_polynomialX_variableChange,
    evalEval_polynomialY_variableChange]
  refine and_congr_right fun _ => ?_
  simp only [ne_eq, mul_eq_zero]
  by_cases hY : W.polynomialY.evalEval x y = 0 <;> simp [hY]

/-- The preimage of a nonsingular point of `C • W` is a nonsingular point of `W`. -/
theorem nonsingular_variableChange_inv {x y : F} (h : (C • W).Nonsingular x y) :
    W.Nonsingular (C.invX x) (C.invY x y) := by
  rw [nonsingular_variableChange W C, VariableChange.mapY_invX_invY, VariableChange.mapX_invX]
  exact h

/-! ### The addition formulas -/

/-- `negY` commutes with the point map. -/
theorem variableChange_negY (x y : F) :
    (C • W).negY (C.mapX x) (C.mapY x y) = C.mapY x (W.negY x y) := by
  simp only [negY, VariableChange.mapX, VariableChange.mapY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  ring

/-- `addX` commutes with the point map, the slope transforming as `ℓ' = u⁻¹ (ℓ - s)`. -/
theorem variableChange_addX (x₁ x₂ ℓ : F) :
    (C • W).addX (C.mapX x₁) (C.mapX x₂) ((C.u : F)⁻¹ * (ℓ - C.s)) =
      C.mapX (W.addX x₁ x₂ ℓ) := by
  simp only [addX, VariableChange.mapX, variableChange_a₁, variableChange_a₂,
    Units.val_inv_eq_inv_val]
  ring

/-- `addY` commutes with the point map, the slope transforming as `ℓ' = u⁻¹ (ℓ - s)`. -/
theorem variableChange_addY (x₁ x₂ y₁ ℓ : F) :
    (C • W).addY (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) ((C.u : F)⁻¹ * (ℓ - C.s)) =
      C.mapY (W.addX x₁ x₂ ℓ) (W.addY x₁ x₂ y₁ ℓ) := by
  simp only [addY, negAddY, addX, negY, VariableChange.mapX, VariableChange.mapY,
    variableChange_a₁, variableChange_a₂, variableChange_a₃, Units.val_inv_eq_inv_val]
  ring

variable {W C}

/-- Two points are inverse to each other exactly when their images are. -/
theorem variableChange_inverse_iff {x₁ x₂ y₁ y₂ : F} :
    (C.mapX x₁ = C.mapX x₂ ∧ C.mapY x₁ y₁ = (C • W).negY (C.mapX x₂) (C.mapY x₂ y₂)) ↔
      (x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
  rw [VariableChange.mapX_inj, variableChange_negY]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, (VariableChange.mapY_inj (C := C)).mp h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by rw [h]⟩

section slope

variable [DecidableEq F]

/-- The slope of the line through two points of `W` that are not inverse to each other transforms
as `ℓ' = u⁻¹ (ℓ - s)`. -/
theorem variableChange_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    (C • W).slope (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.mapY x₂ y₂) =
      (C.u : F)⁻¹ * (W.slope x₁ x₂ y₁ y₂ - C.s) := by
  have hv : (C.u : F)⁻¹ ≠ 0 := inv_ne_zero C.u.ne_zero
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hy' : C.mapY x₁ y₁ ≠ (C • W).negY (C.mapX x₁) (C.mapY x₁ y₁) := by
      rw [variableChange_negY, Ne, VariableChange.mapY_inj]
      exact hy
    have hD : W.polynomialY.evalEval x₁ y₁ ≠ 0 := by
      rw [evalEval_polynomialY]
      intro h
      exact hy (by rw [negY]; linear_combination h)
    rw [slope_of_Y_ne_eq_evalEval rfl hy', slope_of_Y_ne_eq_evalEval rfl hy,
      evalEval_polynomialX_variableChange, evalEval_polynomialY_variableChange]
    field_simp
    ring
  · have hx' : C.mapX x₁ ≠ C.mapX x₂ := fun h => hx (C.mapX_inj.mp h)
    rw [slope_of_X_ne hx', slope_of_X_ne hx]
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    simp only [VariableChange.mapX, VariableChange.mapY]
    field_simp [hd]
    ring

end slope

/-! ### The isomorphism of point groups -/

namespace Point

variable (W C)

/-- The image of a point of `W` on `C • W`, as a function on points. -/
def variableChangeFun : W.Point → (C • W).Point
  | .zero => .zero
  | .some x y h => .some _ _ ((nonsingular_variableChange W C x y).mp h)

/-- The preimage of a point of `C • W` on `W`, as a function on points. -/
def variableChangeInvFun : (C • W).Point → W.Point
  | .zero => .zero
  | .some x y h => .some (C.invX x) (C.invY x y) (nonsingular_variableChange_inv W C h)

variable [DecidableEq F]

/-- The isomorphism of point groups `W.Point ≃+ (C • W).Point` induced by the variable change `C`:
`(x, y) ↦ (u⁻² (x - r), u⁻³ (y - s (x - r) - t))`, `∞ ↦ ∞` (`variableChange_some`,
`variableChange_zero`); its inverse is `(x', y') ↦ (u² x' + r, u³ y' + u² s x' + t)`. -/
def variableChange : W.Point ≃+ (C • W).Point where
  toFun := variableChangeFun W C
  invFun := variableChangeInvFun W C
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
      simp only [variableChangeFun, variableChangeInvFun, some.injEq]
      exact ⟨C.invX_mapX x, C.invY_mapX_mapY x y⟩
  right_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
      simp only [variableChangeFun, variableChangeInvFun, some.injEq]
      exact ⟨C.mapX_invX x, C.mapY_invX_invY x y⟩
  map_add' P Q := by
    cases P with
    | zero => rfl
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero => rfl
      | some x₂ y₂ h₂ =>
        by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
        · have hxy' := variableChange_inverse_iff (C := C).mpr hxy
          change variableChangeFun W C (some x₁ y₁ h₁ + some x₂ y₂ h₂) =
            some _ _ _ + some _ _ _
          rw [add_of_Y_eq hxy.1 hxy.2, add_of_Y_eq hxy'.1 hxy'.2]
          rfl
        · have hxy' : ¬(C.mapX x₁ = C.mapX x₂ ∧
              C.mapY x₁ y₁ = (C • W).negY (C.mapX x₂) (C.mapY x₂ y₂)) :=
            fun h => hxy (variableChange_inverse_iff.mp h)
          change variableChangeFun W C (some x₁ y₁ h₁ + some x₂ y₂ h₂) =
            some _ _ _ + some _ _ _
          rw [add_some hxy, add_some hxy']
          simp only [variableChangeFun, some.injEq]
          rw [variableChange_slope h₁.1 h₂.1 hxy]
          exact ⟨(variableChange_addX W C x₁ x₂ _).symm, (variableChange_addY W C x₁ x₂ y₁ _).symm⟩

variable {W C}

@[simp]
theorem variableChange_zero : variableChange W C 0 = 0 := by
  rfl

@[simp]
theorem variableChange_some {x y : F} (h : W.Nonsingular x y) :
    variableChange W C (some x y h) =
      some (C.mapX x) (C.mapY x y) ((nonsingular_variableChange W C x y).mp h) := by
  rfl

@[simp]
theorem variableChange_symm_zero : (variableChange W C).symm 0 = 0 := by
  rfl

@[simp]
theorem variableChange_symm_some {x y : F} (h : (C • W).Nonsingular x y) :
    (variableChange W C).symm (some x y h) =
      some (C.invX x) (C.invY x y) (nonsingular_variableChange_inv W C h) := by
  rfl

end Point

end Affine

end WeierstrassCurve
