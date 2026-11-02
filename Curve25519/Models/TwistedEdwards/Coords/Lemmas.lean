/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Models.TwistedEdwards.Coords.Defs
public import EllipticCurve.TwistedEdwards.Coords.Lemmas
import all Curve25519.Models.TwistedEdwards.Coords.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # Twisted Edwards models: Niels coordinates, lemmas

The audited statements about the Niels coordinates of
`Curve25519.Models.TwistedEdwards.Coords.Defs`: each coordinate in terms of the represented point
(`YplusX_eq`, `yPlusX_eq`, …, the form the formula proofs use), the identities and negations
(`onCurve_identity`, `toPoint_identity`, `onCurve_neg`, `toPoint_neg`) and the conversions into
them (`onCurve_toProjectiveNiels`, `toPoint_toProjectiveNiels`, …): every conversion preserves
`OnCurve` and represents the same point, and `Point.toAffineNiels` is a section of `toPoint`. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F}

/-! ### From extended coordinates -/

namespace Extended

/-- The `X`-coordinate recovered from the projective Niels form of `P` is `P.X`. -/
theorem toProjectiveNiels_X (h2 : (2 : F) ≠ 0) (P : E.Extended) :
    P.toProjectiveNiels.X = P.X := by
  change (P.Y + P.X - (P.Y - P.X)) / 2 = P.X
  rw [div_eq_iff h2]
  ring

/-- The `Y`-coordinate recovered from the projective Niels form of `P` is `P.Y`. -/
theorem toProjectiveNiels_Y (h2 : (2 : F) ≠ 0) (P : E.Extended) :
    P.toProjectiveNiels.Y = P.Y := by
  change (P.Y + P.X + (P.Y - P.X)) / 2 = P.Y
  rw [div_eq_iff h2]
  ring

/-- The projective Niels form of a point on the curve is on the curve (in characteristic
`≠ 2`). -/
theorem onCurve_toProjectiveNiels (h2 : (2 : F) ≠ 0) {P : E.Extended} (h : P.OnCurve) :
    P.toProjectiveNiels.OnCurve := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [toProjectiveNiels_X h2, toProjectiveNiels_Y h2]
    exact h.2.2
  · rw [toProjectiveNiels_X h2, toProjectiveNiels_Y h2]
    change P.T * (2 * E.d) * P.Z = 2 * E.d * P.X * P.Y
    linear_combination (-2 * E.d) * h.2.1

/-- The projective Niels form represents the same point. -/
theorem toPoint_toProjectiveNiels [E.IsComplete] {P : E.Extended} (h : P.OnCurve) :
    P.toProjectiveNiels.toPoint = P.toPoint := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  refine Point.ext ?_ ?_
  · rw [ProjectiveNiels.toPoint_x (onCurve_toProjectiveNiels h2 h), toProjectiveNiels_X h2,
      toPoint_x h]
    rfl
  · rw [ProjectiveNiels.toPoint_y (onCurve_toProjectiveNiels h2 h), toProjectiveNiels_Y h2,
      toPoint_y h]
    rfl

/-- The `x`-coordinate recovered from the affine Niels form of `P` is `X / Z`. -/
theorem toAffineNiels_x (h2 : (2 : F) ≠ 0) (P : E.Extended) :
    P.toAffineNiels.x = P.X / P.Z := by
  change (P.Y * P.Z⁻¹ + P.X * P.Z⁻¹ - (P.Y * P.Z⁻¹ - P.X * P.Z⁻¹)) / 2 = P.X / P.Z
  rw [div_eq_iff h2, div_eq_mul_inv]
  ring

/-- The `y`-coordinate recovered from the affine Niels form of `P` is `Y / Z`. -/
theorem toAffineNiels_y (h2 : (2 : F) ≠ 0) (P : E.Extended) :
    P.toAffineNiels.y = P.Y / P.Z := by
  change (P.Y * P.Z⁻¹ + P.X * P.Z⁻¹ + (P.Y * P.Z⁻¹ - P.X * P.Z⁻¹)) / 2 = P.Y / P.Z
  rw [div_eq_iff h2, div_eq_mul_inv]
  ring

/-- The affine Niels form of a point on the curve is on the curve (in characteristic `≠ 2`). -/
theorem onCurve_toAffineNiels (h2 : (2 : F) ≠ 0) {P : E.Extended} (h : P.OnCurve) :
    P.toAffineNiels.OnCurve := by
  refine ⟨?_, ?_⟩
  · rw [toAffineNiels_x h2, toAffineNiels_y h2]
    exact h.2.2
  · rw [toAffineNiels_x h2, toAffineNiels_y h2]
    change P.X * P.Z⁻¹ * (P.Y * P.Z⁻¹) * (2 * E.d) = 2 * E.d * (P.X / P.Z) * (P.Y / P.Z)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring

/-- The affine Niels form represents the same point. -/
theorem toPoint_toAffineNiels [E.IsComplete] {P : E.Extended} (h : P.OnCurve) :
    P.toAffineNiels.toPoint = P.toPoint := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  refine Point.ext ?_ ?_
  · rw [AffineNiels.toPoint_x (onCurve_toAffineNiels h2 h), toAffineNiels_x h2, toPoint_x h]
  · rw [AffineNiels.toPoint_y (onCurve_toAffineNiels h2 h), toAffineNiels_y h2, toPoint_y h]

end Extended

/-! ### Projective Niels coordinates -/

namespace ProjectiveNiels

section IsComplete

variable [E.IsComplete] {P : E.ProjectiveNiels}

/-- `X = x Z` for the represented point `(x, y)`. -/
theorem X_eq_toPoint_x_mul_Z (h : P.OnCurve) : P.X = P.toPoint.x * P.Z := by
  rw [toPoint_x h, div_mul_cancel₀ _ h.1]

/-- `Y = y Z` for the represented point `(x, y)`. -/
theorem Y_eq_toPoint_y_mul_Z (h : P.OnCurve) : P.Y = P.toPoint.y * P.Z := by
  rw [toPoint_y h, div_mul_cancel₀ _ h.1]

/-- `Y + X = (y + x) Z` for the represented point `(x, y)`. -/
theorem YplusX_eq (h : P.OnCurve) : P.YplusX = (P.toPoint.y + P.toPoint.x) * P.Z := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  rw [toPoint_x h, toPoint_y h, ← add_div, div_mul_cancel₀ _ h.1]
  unfold X Y
  rw [← add_div, eq_div_iff h2]
  ring

/-- `Y - X = (y - x) Z` for the represented point `(x, y)`. -/
theorem YminusX_eq (h : P.OnCurve) : P.YminusX = (P.toPoint.y - P.toPoint.x) * P.Z := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  rw [toPoint_x h, toPoint_y h, ← sub_div, div_mul_cancel₀ _ h.1]
  unfold X Y
  rw [← sub_div, eq_div_iff h2]
  ring

/-- `T2d = 2 d x y Z` for the represented point `(x, y)`. -/
theorem T2d_eq (h : P.OnCurve) : P.T2d = 2 * E.d * P.toPoint.x * P.toPoint.y * P.Z := by
  have key := h.2.2
  rw [X_eq_toPoint_x_mul_Z h, Y_eq_toPoint_y_mul_Z h] at key
  exact mul_right_cancel₀ h.1 (by linear_combination key)

end IsComplete

/-- The `X`-coordinate recovered from the identity `(1 : 1 : 1 : 0)` is `0`. -/
theorem identity_X : (identity : E.ProjectiveNiels).X = 0 := by
  change (1 - 1 : F) / 2 = 0
  rw [sub_self, zero_div]

/-- The `Y`-coordinate recovered from the identity `(1 : 1 : 1 : 0)` is `1` (in characteristic
`≠ 2`). -/
theorem identity_Y (h2 : (2 : F) ≠ 0) : (identity : E.ProjectiveNiels).Y = 1 := by
  change (1 + 1 : F) / 2 = 1
  rw [div_eq_one_iff_eq h2]
  ring

/-- The identity `(1 : 1 : 1 : 0)` is on the curve (in characteristic `≠ 2`). -/
theorem onCurve_identity (h2 : (2 : F) ≠ 0) : (identity : E.ProjectiveNiels).OnCurve := by
  refine ⟨one_ne_zero, ?_, ?_⟩
  · rw [identity_X, identity_Y h2]
    change E.Equation (0 / 1) (1 / 1)
    rw [zero_div, div_one]
    exact E.equation_zero_one
  · rw [identity_X, identity_Y h2]
    change (0 : F) * 1 = 2 * E.d * 0 * 1
    ring

/-- The identity `(1 : 1 : 1 : 0)` represents `0`. -/
theorem toPoint_identity [E.IsComplete] : (identity : E.ProjectiveNiels).toPoint = 0 := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  refine Point.ext ?_ ?_
  · rw [toPoint_x (onCurve_identity h2), identity_X, zero_x]
    exact zero_div 1
  · rw [toPoint_y (onCurve_identity h2), identity_Y h2, zero_y]
    exact div_one 1

/-- The `X`-coordinate recovered from the negation is `-X`. -/
theorem neg_X (P : E.ProjectiveNiels) : P.neg.X = -P.X := by
  change (P.YminusX - P.YplusX) / 2 = -((P.YplusX - P.YminusX) / 2)
  rw [← neg_div, neg_sub]

/-- The `Y`-coordinate recovered from the negation is `Y`. -/
theorem neg_Y (P : E.ProjectiveNiels) : P.neg.Y = P.Y := by
  change (P.YminusX + P.YplusX) / 2 = (P.YplusX + P.YminusX) / 2
  rw [add_comm]

/-- Negation preserves `OnCurve`. -/
theorem onCurve_neg {P : E.ProjectiveNiels} (h : P.OnCurve) : P.neg.OnCurve := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [neg_X, neg_Y, neg_div]
    exact equation_neg h.2.1
  · rw [neg_X, neg_Y]
    change -P.T2d * P.Z = 2 * E.d * -P.X * P.Y
    linear_combination -h.2.2

/-- Negation in coordinates is negation of the represented point. -/
theorem toPoint_neg [E.IsComplete] {P : E.ProjectiveNiels} (h : P.OnCurve) :
    P.neg.toPoint = -P.toPoint := by
  refine Point.ext ?_ ?_
  · rw [toPoint_x (onCurve_neg h), TwistedEdwardsModel.neg_x, toPoint_x h, neg_X]
    exact neg_div _ _
  · rw [toPoint_y (onCurve_neg h), TwistedEdwardsModel.neg_y, toPoint_y h, neg_Y]
    rfl

end ProjectiveNiels

/-! ### Affine Niels coordinates -/

namespace AffineNiels

section IsComplete

variable [E.IsComplete] {P : E.AffineNiels}

/-- `y + x` for the represented point `(x, y)`. -/
theorem yPlusX_eq (h : P.OnCurve) : P.yPlusX = P.toPoint.y + P.toPoint.x := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  rw [toPoint_x h, toPoint_y h]
  unfold x y
  rw [← add_div, eq_div_iff h2]
  ring

/-- `y - x` for the represented point `(x, y)`. -/
theorem yMinusX_eq (h : P.OnCurve) : P.yMinusX = P.toPoint.y - P.toPoint.x := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  rw [toPoint_x h, toPoint_y h]
  unfold x y
  rw [← sub_div, eq_div_iff h2]
  ring

/-- `xy2d = 2 d x y` for the represented point `(x, y)`. -/
theorem xy2d_eq (h : P.OnCurve) : P.xy2d = 2 * E.d * P.toPoint.x * P.toPoint.y := by
  rw [toPoint_x h, toPoint_y h]
  exact h.2

end IsComplete

/-- The `x`-coordinate recovered from the identity `(1, 1, 0)` is `0`. -/
theorem identity_x : (identity : E.AffineNiels).x = 0 := by
  change (1 - 1 : F) / 2 = 0
  rw [sub_self, zero_div]

/-- The `y`-coordinate recovered from the identity `(1, 1, 0)` is `1` (in characteristic
`≠ 2`). -/
theorem identity_y (h2 : (2 : F) ≠ 0) : (identity : E.AffineNiels).y = 1 := by
  change (1 + 1 : F) / 2 = 1
  rw [div_eq_one_iff_eq h2]
  ring

/-- The identity `(1, 1, 0)` is on the curve (in characteristic `≠ 2`). -/
theorem onCurve_identity (h2 : (2 : F) ≠ 0) : (identity : E.AffineNiels).OnCurve := by
  refine ⟨?_, ?_⟩
  · rw [identity_x, identity_y h2]
    exact E.equation_zero_one
  · rw [identity_x, identity_y h2]
    change (0 : F) = 2 * E.d * 0 * 1
    ring

/-- The identity `(1, 1, 0)` represents `0`. -/
theorem toPoint_identity [E.IsComplete] : (identity : E.AffineNiels).toPoint = 0 := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  refine Point.ext ?_ ?_
  · rw [toPoint_x (onCurve_identity h2), identity_x, zero_x]
  · rw [toPoint_y (onCurve_identity h2), identity_y h2, zero_y]

/-- The `x`-coordinate recovered from the negation is `-x`. -/
theorem neg_x (P : E.AffineNiels) : P.neg.x = -P.x := by
  change (P.yMinusX - P.yPlusX) / 2 = -((P.yPlusX - P.yMinusX) / 2)
  rw [← neg_div, neg_sub]

/-- The `y`-coordinate recovered from the negation is `y`. -/
theorem neg_y (P : E.AffineNiels) : P.neg.y = P.y := by
  change (P.yMinusX + P.yPlusX) / 2 = (P.yPlusX + P.yMinusX) / 2
  rw [add_comm]

/-- Negation preserves `OnCurve`. -/
theorem onCurve_neg {P : E.AffineNiels} (h : P.OnCurve) : P.neg.OnCurve := by
  refine ⟨?_, ?_⟩
  · rw [neg_x, neg_y]
    exact equation_neg h.1
  · rw [neg_x, neg_y]
    change -P.xy2d = 2 * E.d * -P.x * P.y
    linear_combination -h.2

/-- Negation in coordinates is negation of the represented point. -/
theorem toPoint_neg [E.IsComplete] {P : E.AffineNiels} (h : P.OnCurve) :
    P.neg.toPoint = -P.toPoint := by
  refine Point.ext ?_ ?_
  · rw [toPoint_x (onCurve_neg h), TwistedEdwardsModel.neg_x, toPoint_x h, neg_x]
  · rw [toPoint_y (onCurve_neg h), TwistedEdwardsModel.neg_y, toPoint_y h, neg_y]

end AffineNiels

/-! ### From affine points -/

namespace Point

/-- The `x`-coordinate recovered from the affine Niels form of `P` is `P.x`. -/
theorem toAffineNiels_x (h2 : (2 : F) ≠ 0) (P : E.Point) : P.toAffineNiels.x = P.x := by
  change (P.y + P.x - (P.y - P.x)) / 2 = P.x
  rw [div_eq_iff h2]
  ring

/-- The `y`-coordinate recovered from the affine Niels form of `P` is `P.y`. -/
theorem toAffineNiels_y (h2 : (2 : F) ≠ 0) (P : E.Point) : P.toAffineNiels.y = P.y := by
  change (P.y + P.x + (P.y - P.x)) / 2 = P.y
  rw [div_eq_iff h2]
  ring

/-- The affine Niels form `(y + x, y - x, x y (2 d))` of a point is on the curve (in
characteristic `≠ 2`). -/
theorem onCurve_toAffineNiels (h2 : (2 : F) ≠ 0) (P : E.Point) : P.toAffineNiels.OnCurve := by
  refine ⟨?_, ?_⟩
  · rw [toAffineNiels_x h2, toAffineNiels_y h2]
    exact P.equation
  · rw [toAffineNiels_x h2, toAffineNiels_y h2]
    change P.x * P.y * (2 * E.d) = 2 * E.d * P.x * P.y
    ring

/-- The affine Niels form represents the point: `Point.toAffineNiels` is a section of
`toPoint`. -/
theorem toPoint_toAffineNiels [E.IsComplete] (P : E.Point) : P.toAffineNiels.toPoint = P := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  refine Point.ext ?_ ?_
  · rw [AffineNiels.toPoint_x (onCurve_toAffineNiels h2 P), toAffineNiels_x h2]
  · rw [AffineNiels.toPoint_y (onCurve_toAffineNiels h2 P), toAffineNiels_y h2]

end Point

end TwistedEdwardsModel
