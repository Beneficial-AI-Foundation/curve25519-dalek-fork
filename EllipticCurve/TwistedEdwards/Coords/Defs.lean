/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public section

/-! # Twisted Edwards models: coordinate systems

The redundant ways to write a point of a twisted Edwards model `E` that implementations use,
named after curve25519-dalek's `curve_models.rs` (Hisil–Wong–Carter–Dawson 2008):

* `E.Extended`: `(X : Y : Z : T)` with `x = X / Z`, `y = Y / Z`, `x y = T / Z`;
* `E.Projective`: `(X : Y : Z)` with `x = X / Z`, `y = Y / Z`;
* `E.Completed`: `((X : Z), (Y : T)) ∈ ℙ¹ × ℙ¹` with `x = X / Z`, `y = Y / T`;
* `E.ProjectiveNiels`: `(Y + X : Y - X : Z : 2 d T)` of an extended point;
* `E.AffineNiels`: `(y + x, y - x, 2 d x y)` of an affine point.

Each is a plain structure of field elements, with an exposed validity predicate `OnCurve`
(stated with the affine point, and restated without division by `onCurve_iff_homogeneous`), a
total hidden `toPoint` into `E.Point` (the affine point when `OnCurve`, `0` otherwise;
characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`), and for the two
projective systems the exposed projective equality `ProjEq` (what `EdwardsPoint::ct_eq`
computes), with `projEq_iff_toPoint_eq`. The conversions between the systems, the identities
and the negations are the exposed formulas the code computes; their `onCurve_*` and
`toPoint_*` lemmas are in `EllipticCurve.TwistedEdwards.Coords.Lemmas`. The group operations in
coordinates are in `EllipticCurve.TwistedEdwards.Formulas.*`. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] (E : TwistedEdwardsModel F)

/-- The equation of a model is decidable in a field with decidable equality. -/
instance instDecidableEquation [DecidableEq F] (x y : F) : Decidable (E.Equation x y) :=
  inferInstanceAs (Decidable (E.a * x ^ 2 + y ^ 2 = 1 + E.d * x ^ 2 * y ^ 2))

/-- The defining equation of `E` at `(X / Z, Y / T)`, without division. -/
theorem equation_div_iff {X Y Z T : F} (hZ : Z ≠ 0) (hT : T ≠ 0) :
    E.Equation (X / Z) (Y / T) ↔
      E.a * X ^ 2 * T ^ 2 + Y ^ 2 * Z ^ 2 = Z ^ 2 * T ^ 2 + E.d * X ^ 2 * Y ^ 2 := by
  have hZT : Z ^ 2 * T ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hZ) (pow_ne_zero 2 hT)
  have key : E.a * (X / Z) ^ 2 + (Y / T) ^ 2 - (1 + E.d * (X / Z) ^ 2 * (Y / T) ^ 2) =
      (E.a * X ^ 2 * T ^ 2 + Y ^ 2 * Z ^ 2 - (Z ^ 2 * T ^ 2 + E.d * X ^ 2 * Y ^ 2)) /
        (Z ^ 2 * T ^ 2) := by
    field_simp
  unfold Equation
  rw [← sub_eq_zero, key, div_eq_zero_iff, or_iff_left hZT, sub_eq_zero]

/-! ### The coordinate systems -/

/-- Extended coordinates `(X : Y : Z : T)`: `x = X / Z`, `y = Y / Z`, `x y = T / Z`
(curve25519-dalek's `EdwardsPoint`). -/
@[ext] structure Extended (E : TwistedEdwardsModel F) where
  /-- The `X`-coordinate. -/
  X : F
  /-- The `Y`-coordinate. -/
  Y : F
  /-- The `Z`-coordinate. -/
  Z : F
  /-- The `T`-coordinate, `T / Z = x y`. -/
  T : F
  deriving DecidableEq

/-- Projective coordinates `(X : Y : Z)`: `x = X / Z`, `y = Y / Z` (curve25519-dalek's
`ProjectivePoint`). -/
@[ext] structure Projective (E : TwistedEdwardsModel F) where
  /-- The `X`-coordinate. -/
  X : F
  /-- The `Y`-coordinate. -/
  Y : F
  /-- The `Z`-coordinate. -/
  Z : F
  deriving DecidableEq

/-- Completed coordinates `((X : Z), (Y : T)) ∈ ℙ¹ × ℙ¹`: `x = X / Z`, `y = Y / T`
(curve25519-dalek's `CompletedPoint`). -/
@[ext] structure Completed (E : TwistedEdwardsModel F) where
  /-- The `X`-coordinate, `x = X / Z`. -/
  X : F
  /-- The `Y`-coordinate, `y = Y / T`. -/
  Y : F
  /-- The denominator of `x`. -/
  Z : F
  /-- The denominator of `y`. -/
  T : F
  deriving DecidableEq

/-- Projective Niels coordinates `(Y + X : Y - X : Z : 2 d T)` of an extended point
(curve25519-dalek's `ProjectiveNielsPoint`). -/
@[ext] structure ProjectiveNiels (E : TwistedEdwardsModel F) where
  /-- `Y + X`. -/
  YplusX : F
  /-- `Y - X`. -/
  YminusX : F
  /-- The `Z`-coordinate. -/
  Z : F
  /-- `2 d T`. -/
  T2d : F
  deriving DecidableEq

/-- Affine Niels coordinates `(y + x, y - x, 2 d x y)` of an affine point (curve25519-dalek's
`AffineNielsPoint`). -/
@[ext] structure AffineNiels (E : TwistedEdwardsModel F) where
  /-- `y + x`. -/
  yPlusX : F
  /-- `y - x`. -/
  yMinusX : F
  /-- `2 d x y`. -/
  xy2d : F
  deriving DecidableEq

variable {E}

/-! ### Extended coordinates -/

namespace Extended

/-- `(X : Y : Z : T)` represents a point of `E`: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)`
satisfies the equation. -/
@[expose] def OnCurve (P : E.Extended) : Prop :=
  P.Z ≠ 0 ∧ P.X * P.Y = P.Z * P.T ∧ E.Equation (P.X / P.Z) (P.Y / P.Z)

instance instDecidableOnCurve [DecidableEq F] (P : E.Extended) : Decidable P.OnCurve :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (P : E.Extended) :
    P.OnCurve ↔ P.Z ≠ 0 ∧ P.X * P.Y = P.Z * P.T ∧
      E.a * P.X ^ 2 * P.Z ^ 2 + P.Y ^ 2 * P.Z ^ 2 = P.Z ^ 4 + E.d * P.X ^ 2 * P.Y ^ 2 := by
  constructor
  · rintro ⟨hZ, hT, h⟩
    rw [equation_div_iff E hZ hZ] at h
    exact ⟨hZ, hT, by linear_combination h⟩
  · rintro ⟨hZ, hT, h⟩
    exact ⟨hZ, hT, (E.equation_div_iff hZ hZ).mpr (by linear_combination h)⟩

/-- Projective equality, what `EdwardsPoint::ct_eq` computes (`T` is ignored). -/
@[expose] def ProjEq (P Q : E.Extended) : Prop :=
  P.X * Q.Z = Q.X * P.Z ∧ P.Y * Q.Z = Q.Y * P.Z

instance instDecidableRelProjEq [DecidableEq F] : DecidableRel (ProjEq (E := E)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

section IsComplete

variable [E.IsComplete]

open scoped Classical in
/-- The point represented by `(X : Y : Z : T)`: `(X / Z, Y / Z)` when `OnCurve`, and `0`
otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.Extended) : E.Point :=
  if h : P.OnCurve then ⟨P.X / P.Z, P.Y / P.Z, h.2.2⟩ else 0

/-- The `x`-coordinate of the point represented by `(X : Y : Z : T)` is `X / Z`. -/
theorem toPoint_x {P : E.Extended} (h : P.OnCurve) : P.toPoint.x = P.X / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- The `y`-coordinate of the point represented by `(X : Y : Z : T)` is `Y / Z`. -/
theorem toPoint_y {P : E.Extended} (h : P.OnCurve) : P.toPoint.y = P.Y / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- Off the curve, `toPoint` is `0`. -/
theorem toPoint_of_not_onCurve {P : E.Extended} (h : ¬ P.OnCurve) : P.toPoint = 0 := by
  unfold toPoint
  rw [dite_eq_right h]

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {P Q : E.Extended} (hP : P.OnCurve) (hQ : Q.OnCurve) :
    P.ProjEq Q ↔ P.toPoint = Q.toPoint := by
  rw [Point.ext_iff, toPoint_x hP, toPoint_x hQ, toPoint_y hP, toPoint_y hQ,
    div_eq_div_iff hP.1 hQ.1, div_eq_div_iff hP.1 hQ.1]
  rfl

end IsComplete

/-- The identity `(0 : 1 : 1 : 0)` (`EdwardsPoint::identity`). -/
@[expose] def identity : E.Extended :=
  ⟨0, 1, 1, 0⟩

/-- Negation `(X : Y : Z : T) ↦ (-X : Y : Z : -T)` (`Neg for EdwardsPoint`). -/
@[expose] def neg (P : E.Extended) : E.Extended :=
  ⟨-P.X, P.Y, P.Z, -P.T⟩

/-- Forget `T` (`EdwardsPoint::as_projective`). -/
@[expose] def toProjective (P : E.Extended) : E.Projective :=
  ⟨P.X, P.Y, P.Z⟩

/-- The projective Niels form `(Y + X : Y - X : Z : T (2 d))`
(`EdwardsPoint::as_projective_niels`, with `EDWARDS_D2 = 2 d`). -/
@[expose] def toProjectiveNiels (P : E.Extended) : E.ProjectiveNiels :=
  ⟨P.Y + P.X, P.Y - P.X, P.Z, P.T * (2 * E.d)⟩

/-- The affine Niels form, through the inverse of `Z` (`EdwardsPoint::as_affine_niels`):
`x = X Z⁻¹`, `y = Y Z⁻¹`, result `(y + x, y - x, x y (2 d))`. -/
@[expose] def toAffineNiels (P : E.Extended) : E.AffineNiels :=
  let recip := P.Z⁻¹
  let x := P.X * recip
  let y := P.Y * recip
  ⟨y + x, y - x, x * y * (2 * E.d)⟩

end Extended

/-! ### Projective coordinates -/

namespace Projective

/-- `(X : Y : Z)` represents a point of `E`: `Z ≠ 0` and `(X / Z, Y / Z)` satisfies the
equation. -/
@[expose] def OnCurve (P : E.Projective) : Prop :=
  P.Z ≠ 0 ∧ E.Equation (P.X / P.Z) (P.Y / P.Z)

instance instDecidableOnCurve [DecidableEq F] (P : E.Projective) : Decidable P.OnCurve :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (P : E.Projective) :
    P.OnCurve ↔ P.Z ≠ 0 ∧
      E.a * P.X ^ 2 * P.Z ^ 2 + P.Y ^ 2 * P.Z ^ 2 = P.Z ^ 4 + E.d * P.X ^ 2 * P.Y ^ 2 := by
  constructor
  · rintro ⟨hZ, h⟩
    rw [equation_div_iff E hZ hZ] at h
    exact ⟨hZ, by linear_combination h⟩
  · rintro ⟨hZ, h⟩
    exact ⟨hZ, (E.equation_div_iff hZ hZ).mpr (by linear_combination h)⟩

/-- Projective equality. -/
@[expose] def ProjEq (P Q : E.Projective) : Prop :=
  P.X * Q.Z = Q.X * P.Z ∧ P.Y * Q.Z = Q.Y * P.Z

instance instDecidableRelProjEq [DecidableEq F] : DecidableRel (ProjEq (E := E)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

section IsComplete

variable [E.IsComplete]

open scoped Classical in
/-- The point represented by `(X : Y : Z)`: `(X / Z, Y / Z)` when `OnCurve`, and `0`
otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.Projective) : E.Point :=
  if h : P.OnCurve then ⟨P.X / P.Z, P.Y / P.Z, h.2⟩ else 0

/-- The `x`-coordinate of the point represented by `(X : Y : Z)` is `X / Z`. -/
theorem toPoint_x {P : E.Projective} (h : P.OnCurve) : P.toPoint.x = P.X / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- The `y`-coordinate of the point represented by `(X : Y : Z)` is `Y / Z`. -/
theorem toPoint_y {P : E.Projective} (h : P.OnCurve) : P.toPoint.y = P.Y / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- Off the curve, `toPoint` is `0`. -/
theorem toPoint_of_not_onCurve {P : E.Projective} (h : ¬ P.OnCurve) : P.toPoint = 0 := by
  unfold toPoint
  rw [dite_eq_right h]

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {P Q : E.Projective} (hP : P.OnCurve) (hQ : Q.OnCurve) :
    P.ProjEq Q ↔ P.toPoint = Q.toPoint := by
  rw [Point.ext_iff, toPoint_x hP, toPoint_x hQ, toPoint_y hP, toPoint_y hQ,
    div_eq_div_iff hP.1 hQ.1, div_eq_div_iff hP.1 hQ.1]
  rfl

end IsComplete

/-- The identity `(0 : 1 : 1)` (`ProjectivePoint::identity`). -/
@[expose] def identity : E.Projective :=
  ⟨0, 1, 1⟩

/-- Extended coordinates `(X Z : Y Z : Z² : X Y)` (`ProjectivePoint::as_extended`). -/
@[expose] def toExtended (P : E.Projective) : E.Extended :=
  ⟨P.X * P.Z, P.Y * P.Z, P.Z ^ 2, P.X * P.Y⟩

end Projective

/-! ### Completed coordinates -/

namespace Completed

/-- `((X : Z), (Y : T))` represents a point of `E`: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)`
satisfies the equation. -/
@[expose] def OnCurve (P : E.Completed) : Prop :=
  P.Z ≠ 0 ∧ P.T ≠ 0 ∧ E.Equation (P.X / P.Z) (P.Y / P.T)

instance instDecidableOnCurve [DecidableEq F] (P : E.Completed) : Decidable P.OnCurve :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `OnCurve` without division: `a X² T² + Y² Z² = Z² T² + d X² Y²`. -/
theorem onCurve_iff_homogeneous (P : E.Completed) :
    P.OnCurve ↔ P.Z ≠ 0 ∧ P.T ≠ 0 ∧
      E.a * P.X ^ 2 * P.T ^ 2 + P.Y ^ 2 * P.Z ^ 2 =
        P.Z ^ 2 * P.T ^ 2 + E.d * P.X ^ 2 * P.Y ^ 2 := by
  constructor
  · rintro ⟨hZ, hT, h⟩
    exact ⟨hZ, hT, (E.equation_div_iff hZ hT).mp h⟩
  · rintro ⟨hZ, hT, h⟩
    exact ⟨hZ, hT, (E.equation_div_iff hZ hT).mpr h⟩

section IsComplete

variable [E.IsComplete]

open scoped Classical in
/-- The point represented by `((X : Z), (Y : T))`: `(X / Z, Y / T)` when `OnCurve`, and `0`
otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.Completed) : E.Point :=
  if h : P.OnCurve then ⟨P.X / P.Z, P.Y / P.T, h.2.2⟩ else 0

/-- The `x`-coordinate of the point represented by `((X : Z), (Y : T))` is `X / Z`. -/
theorem toPoint_x {P : E.Completed} (h : P.OnCurve) : P.toPoint.x = P.X / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- The `y`-coordinate of the point represented by `((X : Z), (Y : T))` is `Y / T`. -/
theorem toPoint_y {P : E.Completed} (h : P.OnCurve) : P.toPoint.y = P.Y / P.T := by
  unfold toPoint
  rw [dite_eq_left h]

/-- Off the curve, `toPoint` is `0`. -/
theorem toPoint_of_not_onCurve {P : E.Completed} (h : ¬ P.OnCurve) : P.toPoint = 0 := by
  unfold toPoint
  rw [dite_eq_right h]

end IsComplete

/-- Extended coordinates `(X T : Y Z : Z T : X Y)` (`CompletedPoint::as_extended`). -/
@[expose] def toExtended (P : E.Completed) : E.Extended :=
  ⟨P.X * P.T, P.Y * P.Z, P.Z * P.T, P.X * P.Y⟩

/-- Projective coordinates `(X T : Y Z : Z T)` (`CompletedPoint::as_projective`). -/
@[expose] def toProjective (P : E.Completed) : E.Projective :=
  ⟨P.X * P.T, P.Y * P.Z, P.Z * P.T⟩

end Completed

/-! ### Projective Niels coordinates -/

namespace ProjectiveNiels

/-- The `X`-coordinate `((Y + X) - (Y - X)) / 2` recovered from the Niels form. -/
@[expose] def X (P : E.ProjectiveNiels) : F :=
  (P.YplusX - P.YminusX) / 2

/-- The `Y`-coordinate `((Y + X) + (Y - X)) / 2` recovered from the Niels form. -/
@[expose] def Y (P : E.ProjectiveNiels) : F :=
  (P.YplusX + P.YminusX) / 2

/-- `(Y + X : Y - X : Z : T2d)` represents a point of `E`: `Z ≠ 0`, `(X / Z, Y / Z)` satisfies
the equation (`X`, `Y` recovered from the Niels form), and `T2d Z = 2 d X Y`. -/
@[expose] def OnCurve (P : E.ProjectiveNiels) : Prop :=
  P.Z ≠ 0 ∧ E.Equation (P.X / P.Z) (P.Y / P.Z) ∧ P.T2d * P.Z = 2 * E.d * P.X * P.Y

instance instDecidableOnCurve [DecidableEq F] (P : E.ProjectiveNiels) : Decidable P.OnCurve :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `OnCurve` without division, in terms of `X' = 2 X = (Y + X) - (Y - X)` and
`Y' = 2 Y = (Y + X) + (Y - X)` (in characteristic `≠ 2`):
`4 a X'² Z² + 4 Y'² Z² = 16 Z⁴ + d X'² Y'²` and `2 T2d Z = d X' Y'`. -/
theorem onCurve_iff_homogeneous (h2 : (2 : F) ≠ 0) (P : E.ProjectiveNiels) :
    P.OnCurve ↔ P.Z ≠ 0 ∧
      4 * E.a * (P.YplusX - P.YminusX) ^ 2 * P.Z ^ 2 + 4 * (P.YplusX + P.YminusX) ^ 2 * P.Z ^ 2 =
        16 * P.Z ^ 4 + E.d * (P.YplusX - P.YminusX) ^ 2 * (P.YplusX + P.YminusX) ^ 2 ∧
      2 * P.T2d * P.Z = E.d * (P.YplusX - P.YminusX) * (P.YplusX + P.YminusX) := by
  have h16 : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 2 * 2 * 2 * 2 by norm_num]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2
  have hX : P.YplusX - P.YminusX = 2 * P.X := (mul_div_cancel₀ _ h2).symm
  have hY : P.YplusX + P.YminusX = 2 * P.Y := (mul_div_cancel₀ _ h2).symm
  rw [hX, hY]
  unfold OnCurve
  constructor
  · rintro ⟨hZ, h, hT⟩
    rw [equation_div_iff E hZ hZ] at h
    exact ⟨hZ, by linear_combination 16 * h, by linear_combination 2 * hT⟩
  · rintro ⟨hZ, h, hT⟩
    refine ⟨hZ, (E.equation_div_iff hZ hZ).mpr ?_, ?_⟩
    · apply mul_left_cancel₀ h16
      linear_combination h
    · apply mul_left_cancel₀ h2
      linear_combination hT

section IsComplete

variable [E.IsComplete]

open scoped Classical in
/-- The point represented by `(Y + X : Y - X : Z : T2d)`: `(X / Z, Y / Z)` when `OnCurve`, and
`0` otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.ProjectiveNiels) : E.Point :=
  if h : P.OnCurve then ⟨P.X / P.Z, P.Y / P.Z, h.2.1⟩ else 0

/-- The `x`-coordinate of the point represented by a projective Niels point is `X / Z`. -/
theorem toPoint_x {P : E.ProjectiveNiels} (h : P.OnCurve) : P.toPoint.x = P.X / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- The `y`-coordinate of the point represented by a projective Niels point is `Y / Z`. -/
theorem toPoint_y {P : E.ProjectiveNiels} (h : P.OnCurve) : P.toPoint.y = P.Y / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- Off the curve, `toPoint` is `0`. -/
theorem toPoint_of_not_onCurve {P : E.ProjectiveNiels} (h : ¬ P.OnCurve) : P.toPoint = 0 := by
  unfold toPoint
  rw [dite_eq_right h]

end IsComplete

/-- The identity `(1 : 1 : 1 : 0)` (`ProjectiveNielsPoint::identity`). -/
@[expose] def identity : E.ProjectiveNiels :=
  ⟨1, 1, 1, 0⟩

/-- Negation: swap `Y + X` and `Y - X`, negate `T2d` (`Neg for ProjectiveNielsPoint`). -/
@[expose] def neg (P : E.ProjectiveNiels) : E.ProjectiveNiels :=
  ⟨P.YminusX, P.YplusX, P.Z, -P.T2d⟩

end ProjectiveNiels

/-! ### Affine Niels coordinates -/

namespace AffineNiels

/-- The `x`-coordinate `((y + x) - (y - x)) / 2` recovered from the Niels form. -/
@[expose] def x (P : E.AffineNiels) : F :=
  (P.yPlusX - P.yMinusX) / 2

/-- The `y`-coordinate `((y + x) + (y - x)) / 2` recovered from the Niels form. -/
@[expose] def y (P : E.AffineNiels) : F :=
  (P.yPlusX + P.yMinusX) / 2

/-- `(y + x, y - x, xy2d)` represents a point of `E`: `(x, y)` satisfies the equation (`x`, `y`
recovered from the Niels form) and `xy2d = 2 d x y`. -/
@[expose] def OnCurve (P : E.AffineNiels) : Prop :=
  E.Equation P.x P.y ∧ P.xy2d = 2 * E.d * P.x * P.y

instance instDecidableOnCurve [DecidableEq F] (P : E.AffineNiels) : Decidable P.OnCurve :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `OnCurve` without division, in terms of `x' = 2 x = (y + x) - (y - x)` and
`y' = 2 y = (y + x) + (y - x)` (in characteristic `≠ 2`): `4 a x'² + 4 y'² = 16 + d x'² y'²`
and `2 xy2d = d x' y'`. -/
theorem onCurve_iff_homogeneous (h2 : (2 : F) ≠ 0) (P : E.AffineNiels) :
    P.OnCurve ↔
      4 * E.a * (P.yPlusX - P.yMinusX) ^ 2 + 4 * (P.yPlusX + P.yMinusX) ^ 2 =
        16 + E.d * (P.yPlusX - P.yMinusX) ^ 2 * (P.yPlusX + P.yMinusX) ^ 2 ∧
      2 * P.xy2d = E.d * (P.yPlusX - P.yMinusX) * (P.yPlusX + P.yMinusX) := by
  have h16 : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 2 * 2 * 2 * 2 by norm_num]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2
  have hx : P.yPlusX - P.yMinusX = 2 * P.x := (mul_div_cancel₀ _ h2).symm
  have hy : P.yPlusX + P.yMinusX = 2 * P.y := (mul_div_cancel₀ _ h2).symm
  rw [hx, hy]
  unfold OnCurve Equation
  constructor
  · rintro ⟨h, hT⟩
    exact ⟨by linear_combination 16 * h, by linear_combination 2 * hT⟩
  · rintro ⟨h, hT⟩
    refine ⟨?_, ?_⟩
    · apply mul_left_cancel₀ h16
      linear_combination h
    · apply mul_left_cancel₀ h2
      linear_combination hT

section IsComplete

variable [E.IsComplete]

open scoped Classical in
/-- The point represented by `(y + x, y - x, xy2d)`: `(x, y)` when `OnCurve`, and `0`
otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.AffineNiels) : E.Point :=
  if h : P.OnCurve then ⟨P.x, P.y, h.1⟩ else 0

/-- The `x`-coordinate of the point represented by an affine Niels point is `x`. -/
theorem toPoint_x {P : E.AffineNiels} (h : P.OnCurve) : P.toPoint.x = P.x := by
  unfold toPoint
  rw [dite_eq_left h]

/-- The `y`-coordinate of the point represented by an affine Niels point is `y`. -/
theorem toPoint_y {P : E.AffineNiels} (h : P.OnCurve) : P.toPoint.y = P.y := by
  unfold toPoint
  rw [dite_eq_left h]

/-- Off the curve, `toPoint` is `0`. -/
theorem toPoint_of_not_onCurve {P : E.AffineNiels} (h : ¬ P.OnCurve) : P.toPoint = 0 := by
  unfold toPoint
  rw [dite_eq_right h]

end IsComplete

/-- The identity `(1, 1, 0)` (`AffineNielsPoint::identity`). -/
@[expose] def identity : E.AffineNiels :=
  ⟨1, 1, 0⟩

/-- Negation: swap `y + x` and `y - x`, negate `xy2d` (`Neg for AffineNielsPoint`). -/
@[expose] def neg (P : E.AffineNiels) : E.AffineNiels :=
  ⟨P.yMinusX, P.yPlusX, -P.xy2d⟩

end AffineNiels

/-! ### From affine points -/

namespace Point

/-- Extended coordinates `(x : y : 1 : x y)` of an affine point (`AffinePoint::to_edwards`). -/
@[expose] def toExtended (P : E.Point) : E.Extended :=
  ⟨P.x, P.y, 1, P.x * P.y⟩

/-- Affine Niels coordinates `(y + x, y - x, x y (2 d))` of an affine point. -/
@[expose] def toAffineNiels (P : E.Point) : E.AffineNiels :=
  ⟨P.y + P.x, P.y - P.x, P.x * P.y * (2 * E.d)⟩

end Point

end TwistedEdwardsModel
