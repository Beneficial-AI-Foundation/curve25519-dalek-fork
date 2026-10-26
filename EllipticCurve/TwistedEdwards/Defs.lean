/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.Montgomery.Lemmas
public import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public section

/-! # Twisted Edwards models: definitions

A twisted Edwards model `E = (a, d)` over a field `F` is the equation `a x² + y² = 1 + d x² y²`
(`TwistedEdwardsModel.Equation`); its points (`E.Point`) are the affine solutions. When `E` is
*complete* (`E.IsComplete`: `a` a nonzero square, `d` a non-square, `2 ≠ 0`), the affine points
form the whole group and the addition formula `addX`, `addY` has no exceptional case.

The group structure on `E.Point` is *defined* by transport along a hidden bijection with the
points of the Montgomery model `E.toMontgomery = (2 (a + d) / (a - d), 4 / (a - d))`, the
birational map `(x, y) ↦ ((1 + y) / (1 - y), (1 + y) / ((1 - y) x))` with `(0, 1) ↦ ∞`; it then
becomes the group isomorphism `E.toMontgomeryEquiv`, and `E.toCurve`, `E.pointEquiv` are those
of `E.toMontgomery`. Everything in the section "The Montgomery model of a twisted Edwards model"
is a hidden construction: the characterising lemmas (`zero_x`, `neg_x`, `add_x`, `add_y`,
`u_toMontgomeryEquiv`, …) are proved in `EllipticCurve.TwistedEdwards.Lemmas` and
`EllipticCurve.Proofs.TwistedEdwards.Group` by `import all` of this module, and nothing else may
depend on the bodies. -/

universe u

/-- A twisted Edwards model `a x² + y² = 1 + d x² y²` over `F`: the coefficients of the
equation. -/
structure TwistedEdwardsModel (F : Type u) [Field F] where
  /-- The coefficient of `x²`. -/
  a : F
  /-- The coefficient of `x² y²`. -/
  d : F

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] (E : TwistedEdwardsModel F)

/-- The defining equation `a x² + y² = 1 + d x² y²` of the model. -/
@[expose] def Equation (x y : F) : Prop :=
  E.a * x ^ 2 + y ^ 2 = 1 + E.d * x ^ 2 * y ^ 2

/-- Completeness: `a` is a nonzero square, `d` is not a square, and `2 ≠ 0` in `F`. The affine
points then form the whole group and the addition formula has no exceptional case
(`addDen₁_ne_zero`, `addDen₂_ne_zero` in `EllipticCurve.TwistedEdwards.Lemmas`). -/
class IsComplete : Prop where
  two_ne_zero : (2 : F) ≠ 0
  isSquare_a : IsSquare E.a
  a_ne_zero : E.a ≠ 0
  not_isSquare_d : ¬ IsSquare E.d

/-- The points of `E`: the affine solutions of its equation. -/
@[ext] structure Point where
  /-- The `x`-coordinate. -/
  x : F
  /-- The `y`-coordinate. -/
  y : F
  /-- The point is on the model. -/
  equation : E.Equation x y
  deriving DecidableEq

/-! ### The equation -/

/-- `(0, 1)` is on every model. -/
theorem equation_zero_one : E.Equation 0 1 := by
  unfold Equation
  ring

/-- `(0, -1)` is on every model. -/
theorem equation_zero_neg_one : E.Equation 0 (-1) := by
  unfold Equation
  ring

variable {E}

/-- If `(x, y)` is on the model then so is `(-x, y)`. -/
theorem equation_neg {x y : F} (h : E.Equation x y) : E.Equation (-x) y := by
  unfold Equation at h ⊢
  rwa [neg_sq]

/-- On the model, `x = 0` forces `y² = 1`. -/
theorem y_sq_eq_one_of_x_eq_zero {x y : F} (h : E.Equation x y) (hx : x = 0) : y ^ 2 = 1 := by
  subst hx
  unfold Equation at h
  linear_combination h

/-- On the model, `x = 0` forces `y = 1` or `y = -1`. -/
theorem y_eq_one_or_eq_neg_one_of_x_eq_zero {x y : F} (h : E.Equation x y) (hx : x = 0) :
    y = 1 ∨ y = -1 :=
  sq_eq_one_iff.mp (y_sq_eq_one_of_x_eq_zero h hx)

/-! ### Consequences of completeness -/

section IsComplete

variable (E) [E.IsComplete]

/-- `d ≠ 0` for a complete model (`0` is a square). -/
theorem d_ne_zero : E.d ≠ 0 := fun h =>
  IsComplete.not_isSquare_d (E := E) ⟨0, by rw [h, mul_zero]⟩

/-- `a ≠ d` for a complete model (`a` is a square, `d` is not). -/
theorem a_ne_d : E.a ≠ E.d := fun h =>
  IsComplete.not_isSquare_d (E := E) (h ▸ IsComplete.isSquare_a)

variable {E}

/-- On a complete model, `y² = 1` forces `x = 0` (since `a ≠ d`). -/
theorem x_eq_zero_of_y_sq_eq_one {x y : F} (h : E.Equation x y) (hy : y ^ 2 = 1) : x = 0 := by
  have key : (E.a - E.d) * x ^ 2 = 0 := by
    unfold Equation at h
    linear_combination h - (1 - E.d * x ^ 2) * hy
  exact (pow_eq_zero_iff two_ne_zero).mp
    ((mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr E.a_ne_d))

/-- On a complete model, `y = 1` forces `x = 0`: `(0, 1)` is the only point with `y = 1`. -/
theorem x_eq_zero_of_y_eq_one {x y : F} (h : E.Equation x y) (hy : y = 1) : x = 0 :=
  x_eq_zero_of_y_sq_eq_one h (by rw [hy, one_pow])

/-- On a complete model, `y = -1` forces `x = 0`: `(0, -1)` is the only point with `y = -1`. -/
theorem x_eq_zero_of_y_eq_neg_one {x y : F} (h : E.Equation x y) (hy : y = -1) : x = 0 :=
  x_eq_zero_of_y_sq_eq_one h (by rw [hy, neg_one_sq])

/-- On a complete model, `x ≠ 0` gives `y ≠ 1`. -/
theorem y_ne_one_of_x_ne_zero {x y : F} (h : E.Equation x y) (hx : x ≠ 0) : y ≠ 1 :=
  fun hy => hx (x_eq_zero_of_y_eq_one h hy)

/-- On a complete model, `x ≠ 0` gives `y ≠ -1`. -/
theorem y_ne_neg_one_of_x_ne_zero {x y : F} (h : E.Equation x y) (hx : x ≠ 0) : y ≠ -1 :=
  fun hy => hx (x_eq_zero_of_y_eq_neg_one h hy)

end IsComplete

/-! ### Addition formulas

The complete twisted Edwards addition law, as exposed functions of the two points, so that they
can be evaluated: `(x₁, y₁) + (x₂, y₂) = ((x₁ y₂ + x₂ y₁) / (1 + d x₁ x₂ y₁ y₂),
(y₁ y₂ - a x₁ x₂) / (1 - d x₁ x₂ y₁ y₂))`. They describe the group law of a complete model
(`add_x`, `add_y` in `EllipticCurve.TwistedEdwards.Lemmas`). -/

/-- The denominator `1 + d x₁ x₂ y₁ y₂` of the `x`-coordinate of the sum. -/
@[expose] def addDen₁ (P Q : E.Point) : F :=
  1 + E.d * P.x * Q.x * P.y * Q.y

/-- The denominator `1 - d x₁ x₂ y₁ y₂` of the `y`-coordinate of the sum. -/
@[expose] def addDen₂ (P Q : E.Point) : F :=
  1 - E.d * P.x * Q.x * P.y * Q.y

/-- The `x`-coordinate `(x₁ y₂ + x₂ y₁) / (1 + d x₁ x₂ y₁ y₂)` of the sum. -/
@[expose] def addX (P Q : E.Point) : F :=
  (P.x * Q.y + Q.x * P.y) / addDen₁ P Q

/-- The `y`-coordinate `(y₁ y₂ - a x₁ x₂) / (1 - d x₁ x₂ y₁ y₂)` of the sum. -/
@[expose] def addY (P Q : E.Point) : F :=
  (P.y * Q.y - E.a * P.x * Q.x) / addDen₂ P Q

/-! ### The Montgomery model of a twisted Edwards model -/

variable (E)

/-- The Montgomery model `(2 (a + d) / (a - d), 4 / (a - d))` birationally equivalent to `E`
(`E.toMontgomeryEquiv`). Hidden; see `toMontgomery_def`, `toMontgomery_A`, `toMontgomery_B`. -/
def toMontgomery : MontgomeryModel F :=
  ⟨2 * (E.a + E.d) / (E.a - E.d), 4 / (E.a - E.d)⟩

/-- The defining equation of `toMontgomery`. -/
theorem toMontgomery_def : E.toMontgomery = ⟨2 * (E.a + E.d) / (E.a - E.d), 4 / (E.a - E.d)⟩ := by
  rfl

/-- The coefficient `A = 2 (a + d) / (a - d)` of the Montgomery model of `E`. -/
theorem toMontgomery_A : E.toMontgomery.A = 2 * (E.a + E.d) / (E.a - E.d) := by
  rfl

/-- The coefficient `B = 4 / (a - d)` of the Montgomery model of `E`. -/
theorem toMontgomery_B : E.toMontgomery.B = 4 / (E.a - E.d) := by
  rfl

/-- `(0, 0)` is on the Montgomery model of `E`. -/
theorem toMontgomery_equation_zero_zero : E.toMontgomery.Equation 0 0 := by
  unfold MontgomeryModel.Equation
  ring

section IsComplete

variable [E.IsComplete]

/-- `a B = A + 2` relates the coefficients of `E` and of its Montgomery model. -/
theorem a_mul_toMontgomery_B : E.a * E.toMontgomery.B = E.toMontgomery.A + 2 := by
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  rw [toMontgomery_A, toMontgomery_B]
  field_simp
  ring

/-- `d B = A - 2` relates the coefficients of `E` and of its Montgomery model. -/
theorem d_mul_toMontgomery_B : E.d * E.toMontgomery.B = E.toMontgomery.A - 2 := by
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  rw [toMontgomery_A, toMontgomery_B]
  field_simp
  ring

/-- `B ≠ 0` for the Montgomery model of a complete `E`. -/
theorem toMontgomery_B_ne_zero : E.toMontgomery.B ≠ 0 := by
  rw [toMontgomery_B]
  refine div_ne_zero ?_ (sub_ne_zero.mpr E.a_ne_d)
  rw [show (4 : F) = 2 ^ 2 by norm_num]
  exact pow_ne_zero 2 (IsComplete.two_ne_zero (E := E))

/-- The Montgomery model of a complete twisted Edwards model is nonsingular:
`A² - 4 = a d B² ≠ 0`. -/
instance instIsNonsingularToMontgomery : E.toMontgomery.IsNonsingular where
  two_ne_zero := IsComplete.two_ne_zero (E := E)
  B_ne_zero := E.toMontgomery_B_ne_zero
  A_sq_ne_four := by
    intro h
    have key : E.a * E.d * E.toMontgomery.B ^ 2 = 0 := by
      linear_combination E.d * E.toMontgomery.B * E.a_mul_toMontgomery_B +
        (E.toMontgomery.A + 2) * E.d_mul_toMontgomery_B + h
    exact mul_ne_zero (mul_ne_zero (IsComplete.a_ne_zero (E := E)) E.d_ne_zero)
      (pow_ne_zero 2 E.toMontgomery_B_ne_zero) key

/-- On the Montgomery model of a complete `E`, `u + 1 ≠ 0`: `u = -1` would give `v² = d`. -/
theorem toMontgomery_u_add_one_ne_zero {u v : F} (h : E.toMontgomery.Equation u v) :
    u + 1 ≠ 0 := by
  intro hu
  have hu' : u = -1 := by linear_combination hu
  subst hu'
  apply IsComplete.not_isSquare_d (E := E)
  refine ⟨v, ?_⟩
  apply mul_left_cancel₀ E.toMontgomery_B_ne_zero
  unfold MontgomeryModel.Equation at h
  linear_combination -h + E.d_mul_toMontgomery_B

/-- Certificate for `toMontgomery_sq_add_mul_add_one_ne_zero`: if `u² + A u + 1 = 0` then
`d (s B)² = (2 u + A)²` where `a = s²`. -/
private theorem cert_no_root (a d A B u s : F) (hs : a = s * s) (haB : a * B = A + 2)
    (hdB : d * B = A - 2) (hq : u ^ 2 + A * u + 1 = 0) :
    d * (s * B * (s * B)) = (2 * u + A) * (2 * u + A) := by
  linear_combination (-d * B ^ 2) * hs + (A - 2) * haB + (a * B) * hdB + (-4) * hq

/-- On the Montgomery model of a complete `E`, `u² + A u + 1 ≠ 0`: a root would make
`A² - 4 = a d B²`, hence `d`, a square. So `(0, 0)` is the only affine point of order `2`. -/
theorem toMontgomery_sq_add_mul_add_one_ne_zero (u : F) :
    u ^ 2 + E.toMontgomery.A * u + 1 ≠ 0 := by
  intro hq
  obtain ⟨s, hs⟩ := IsComplete.isSquare_a (E := E)
  have hs0 : s ≠ 0 := fun h => IsComplete.a_ne_zero (E := E) (by rw [hs, h, mul_zero])
  have hB := E.toMontgomery_B_ne_zero
  apply IsComplete.not_isSquare_d (E := E)
  refine ⟨(2 * u + E.toMontgomery.A) / (s * E.toMontgomery.B), ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero (mul_ne_zero hs0 hB) (mul_ne_zero hs0 hB))]
  exact cert_no_root E.a E.d _ _ u s hs E.a_mul_toMontgomery_B E.d_mul_toMontgomery_B hq

/-- On the Montgomery model of a complete `E`, `v = 0` forces `u = 0`. -/
theorem toMontgomery_u_eq_zero_of_v_eq_zero {u v : F} (h : E.toMontgomery.Equation u v)
    (hv : v = 0) : u = 0 := by
  have key : u * (u ^ 2 + E.toMontgomery.A * u + 1) = 0 := by
    unfold MontgomeryModel.Equation at h
    rw [hv] at h
    linear_combination -h
  exact (mul_eq_zero.mp key).resolve_right (E.toMontgomery_sq_add_mul_add_one_ne_zero u)

/-- On the Montgomery model of a complete `E`, `u = 0` forces `v = 0`. -/
theorem toMontgomery_v_eq_zero_of_u_eq_zero {u v : F} (h : E.toMontgomery.Equation u v)
    (hu : u = 0) : v = 0 := by
  have key : E.toMontgomery.B * v ^ 2 = 0 := by
    unfold MontgomeryModel.Equation at h
    rw [hu] at h
    linear_combination h
  exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp key).resolve_left
  E.toMontgomery_B_ne_zero)

/-! #### The bijection with the Montgomery points (hidden construction) -/

/-- Certificate for `equation_toMontgomery`: the image `(u, v)` of `(x, y)` is on the Montgomery
model, before cancelling `x² (1 - y)³`. -/
private theorem cert_equation_toMontgomery (a d A B x y u v : F) (hu : u * (1 - y) = 1 + y)
    (hv : v * x = u) (hc : a * x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2) (haB : a * B = A + 2)
    (hdB : d * B = A - 2) :
    x ^ 2 * (1 - y) ^ 3 * (B * v ^ 2 - (u ^ 3 + A * u ^ 2 + u)) = 0 := by
  linear_combination
    (-u^2*x^2*y^2-u*x^2*y^2*A-x^2*y^2*d*B+2*u^2*x^2*y+u*x^2*y^2+2*u*x^2*y*A+x^2*y^2*A-u^2*x^2
      -2*x^2*y^2-u*x^2*A+u*y^2*B+x^2*d*B-u*x^2-x^2*A-2*u*y*B+2*x^2+u*B) * hu +
    (x^2*y^3*d*B-v*x*y^3*B-x^2*y^2*d*B+3*v*x*y^2*B-u*y^3*B-x^2*y*a*B-3*v*x*y*B+3*u*y^2*B-y^3*B
      +x^2*a*B+v*x*B-3*u*y*B+y^2*B+u*B+y*B-B) * hv +
    (v*x*y*B-v*x*B) * hc + (-u*x^2*y+u*x^2) * haB +
    (-x^2*y^3+u*x^2*y-x^2*y^2-u*x^2+x^2*y+x^2) * hdB

/-- The Montgomery equation at the image `((1 + y) / (1 - y), (1 + y) / ((1 - y) x))` of a point
`(x, y)` with `y ≠ 1`. At `(0, -1)` the image is `(0, 0)` (division by zero is zero). -/
private theorem equation_toMontgomery {x y : F} (h : E.Equation x y) (hy : y ≠ 1) :
    E.toMontgomery.Equation ((1 + y) / (1 - y)) ((1 + y) / ((1 - y) * x)) := by
  have hy1 : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  by_cases hx : x = 0
  · obtain hy' | hy' := y_eq_one_or_eq_neg_one_of_x_eq_zero h hx
    · exact absurd hy' hy
    · subst hx hy'
      unfold MontgomeryModel.Equation
      norm_num
  · have hu : (1 + y) / (1 - y) * (1 - y) = 1 + y := div_mul_cancel₀ _ hy1
    have hv : (1 + y) / ((1 - y) * x) * x = (1 + y) / (1 - y) := by
      rw [← div_div, div_mul_cancel₀ _ hx]
    have key := cert_equation_toMontgomery E.a E.d E.toMontgomery.A E.toMontgomery.B x y _ _ hu hv
      h E.a_mul_toMontgomery_B E.d_mul_toMontgomery_B
    have hne : x ^ 2 * (1 - y) ^ 3 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 3 hy1)
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

/-- Certificate for `equation_ofMontgomery`: the image `(x, y) = (u / v, (u - 1) / (u + 1))` of a
Montgomery point `(u, v)` is on `E`, before cancelling `B v² (u + 1)²`. -/
private theorem cert_equation_ofMontgomery (a d A B x y u v : F)
    (hM : B * v ^ 2 = u ^ 3 + A * u ^ 2 + u) (hx : x * v = u) (hy : y * (u + 1) = u - 1)
    (haB : a * B = A + 2) (hdB : d * B = A - 2) :
    B * v ^ 2 * (u + 1) ^ 2 * (a * x ^ 2 + y ^ 2 - (1 + d * x ^ 2 * y ^ 2)) = 0 := by
  linear_combination (-4*u) * hM +
    (-v*u^2*x*y^2*d*B-u^3*y^2*d*B-2*v*u*x*y^2*d*B+v*u^2*x*a*B-2*u^2*y^2*d*B-v*x*y^2*d*B
      +u^3*a*B+2*v*u*x*a*B-u*y^2*d*B+2*u^2*a*B+v*x*a*B+u*a*B) * hx +
    (-u^3*y*A+v^2*u*y*B+2*u^3*y-u^3*A-u^2*y*A+v^2*u*B+v^2*y*B+2*u^3+2*u^2*y+u^2*A-v^2*B
      -2*u^2) * hy +
    (u^4+2*u^3+u^2) * haB + (-u^4*y^2-2*u^3*y^2-u^2*y^2) * hdB

/-- The equation of `E` at the image `(u / v, (u - 1) / (u + 1))` of a Montgomery point `(u, v)`.
At `(0, 0)` the image is `(0, -1)` (division by zero is zero). -/
private theorem equation_ofMontgomery {u v : F} (h : E.toMontgomery.Equation u v) :
    E.Equation (u / v) ((u - 1) / (u + 1)) := by
  by_cases hv : v = 0
  · have hu := E.toMontgomery_u_eq_zero_of_v_eq_zero h hv
    subst hu hv
    unfold Equation
    norm_num
  · have hu1 := E.toMontgomery_u_add_one_ne_zero h
    have hx : u / v * v = u := div_mul_cancel₀ _ hv
    have hy : (u - 1) / (u + 1) * (u + 1) = u - 1 := div_mul_cancel₀ _ hu1
    have key := cert_equation_ofMontgomery E.a E.d E.toMontgomery.A E.toMontgomery.B _ _ u v h hx
      hy E.a_mul_toMontgomery_B E.d_mul_toMontgomery_B
    have hne : E.toMontgomery.B * v ^ 2 * (u + 1) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero E.toMontgomery_B_ne_zero (pow_ne_zero 2 hv)) (pow_ne_zero 2 hu1)
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

open scoped Classical in
/-- The bijection `(x, y) ↦ ((1 + y) / (1 - y), (1 + y) / ((1 - y) x))`, `(0, 1) ↦ ∞`, with
inverse `(u, v) ↦ (u / v, (u - 1) / (u + 1))`, `∞ ↦ (0, 1)` (so that `(0, -1) ↔ (0, 0)`), along
which the group structure is transported. Internal. -/
private noncomputable def toMontgomeryEquivAux : E.Point ≃ E.toMontgomery.Point where
  toFun P := if hy : P.y = 1 then .zero else .some _ _ (E.equation_toMontgomery P.equation hy)
  invFun
    | .zero => ⟨0, 1, E.equation_zero_one⟩
    | .some u v h => ⟨u / v, (u - 1) / (u + 1), E.equation_ofMontgomery h⟩
  left_inv P := by
    obtain ⟨x, y, h⟩ := P
    by_cases hy : y = 1
    · simp only [dite_eq_left hy]
      ext
      · exact (x_eq_zero_of_y_eq_one h hy).symm
      · exact hy.symm
    · simp only [dite_eq_right hy]
      have hy1 : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
      ext
      · change (1 + y) / (1 - y) / ((1 + y) / ((1 - y) * x)) = x
        by_cases hx : x = 0
        · obtain hy' | hy' := y_eq_one_or_eq_neg_one_of_x_eq_zero h hx
          · exact absurd hy' hy
          · subst hx hy'
            norm_num
        · have hy2 : 1 + y ≠ 0 := fun h0 =>
            y_ne_neg_one_of_x_ne_zero h hx (by linear_combination h0)
          rw [← div_div, div_div_cancel₀ (div_ne_zero hy2 hy1)]
      · change ((1 + y) / (1 - y) - 1) / ((1 + y) / (1 - y) + 1) = y
        have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
        have e1 : (1 + y) / (1 - y) + 1 = 2 / (1 - y) := by
          rw [div_add_one hy1]
          congr 1
          ring
        have e2 : (1 + y) / (1 - y) - 1 = 2 * y / (1 - y) := by
          rw [div_sub_one hy1]
          congr 1
          ring
        rw [e1, e2, div_div_div_cancel_right₀ hy1, mul_div_cancel_left₀ y h2]
  right_inv Q := by
    cases Q with
    | zero => exact dite_eq_left rfl
    | some u v h =>
      have hu1 := E.toMontgomery_u_add_one_ne_zero h
      have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
      have hy : (u - 1) / (u + 1) ≠ 1 := by
        intro hy
        rw [div_eq_one_iff_eq hu1] at hy
        exact h2 (by linear_combination -hy)
      simp only [dite_eq_right hy, MontgomeryModel.Point.some.injEq]
      have e1 : 1 + (u - 1) / (u + 1) = 2 * u / (u + 1) := by
        rw [one_add_div hu1]
        congr 1
        ring
      have e2 : 1 - (u - 1) / (u + 1) = 2 / (u + 1) := by
        rw [one_sub_div hu1]
        congr 1
        ring
      refine ⟨?_, ?_⟩
      · rw [e1, e2, div_div_div_cancel_right₀ hu1, mul_div_cancel_left₀ u h2]
      · rw [e1, e2]
        by_cases hv : v = 0
        · have hu := E.toMontgomery_u_eq_zero_of_v_eq_zero h hv
          subst hu hv
          norm_num
        · have hu0 : u ≠ 0 := fun hu => hv (E.toMontgomery_v_eq_zero_of_u_eq_zero h hu)
          field_simp

/-- The group law on the points of a complete `E`, transported from `E.toMontgomery.Point`.
Hidden construction: it is characterised by `zero_x`, `zero_y`, `neg_x`, `neg_y`, `add_x` and
`add_y` (`EllipticCurve.TwistedEdwards.Lemmas`). -/
@[no_expose] noncomputable instance instAddCommGroupPoint : AddCommGroup E.Point :=
  E.toMontgomeryEquivAux.addCommGroup

/-- The points of `E` are the points of its Montgomery model, as groups: the birational map
`(x, y) ↦ ((1 + y) / (1 - y), (1 + y) / ((1 - y) x))`. Hidden construction, pinned by
`u_toMontgomeryEquiv`, `v_toMontgomeryEquiv`, `toMontgomeryEquiv_of_y_eq_one`,
`toMontgomeryEquiv_of_x_eq_zero`, `toMontgomeryEquiv_symm_x` and `toMontgomeryEquiv_symm_y`
(`EllipticCurve.TwistedEdwards.Lemmas`). -/
noncomputable def toMontgomeryEquiv : E.Point ≃+ E.toMontgomery.Point :=
  E.toMontgomeryEquivAux.addEquiv

/-- The curve realised by `E`: that of its Montgomery model. Exposed: it only
fixes that the curve of `E` is the curve of `E.toMontgomery`. -/
@[expose] noncomputable def toCurve : Curve F :=
  E.toMontgomery.toCurve

/-- The points of `E` are the points of its curve, as groups. Hidden construction. -/
noncomputable def pointEquiv : E.Point ≃+ E.toCurve.Point :=
  E.toMontgomeryEquiv.trans E.toMontgomery.pointEquiv

/-! The group operations on `E.Point` and the equivalences in terms of the bijection, for
`EllipticCurve.TwistedEdwards.Lemmas` and `EllipticCurve.Proofs.TwistedEdwards.Group`.
Internal. -/

variable {E}

private theorem zero_eq : (0 : E.Point) = E.toMontgomeryEquivAux.symm 0 := by
  rfl

private theorem neg_eq (P : E.Point) :
    -P = E.toMontgomeryEquivAux.symm (-E.toMontgomeryEquivAux P) := by
  rfl

private theorem add_eq (P Q : E.Point) :
    P + Q = E.toMontgomeryEquivAux.symm (E.toMontgomeryEquivAux P + E.toMontgomeryEquivAux Q) := by
  rfl

private theorem toMontgomeryEquiv_apply (P : E.Point) :
    E.toMontgomeryEquiv P = E.toMontgomeryEquivAux P := by
  rfl

private theorem toMontgomeryEquiv_symm_apply (Q : E.toMontgomery.Point) :
    E.toMontgomeryEquiv.symm Q = E.toMontgomeryEquivAux.symm Q := by
  rfl

open scoped Classical in
private theorem toMontgomeryEquivAux_apply_of_y_eq_one {P : E.Point} (hy : P.y = 1) :
    E.toMontgomeryEquivAux P = .zero := by
  change (if hy : P.y = 1 then _ else _) = _
  rw [dite_eq_left hy]

open scoped Classical in
private theorem toMontgomeryEquivAux_apply_of_y_ne_one {P : E.Point} (hy : P.y ≠ 1) :
    E.toMontgomeryEquivAux P =
      .some ((1 + P.y) / (1 - P.y)) ((1 + P.y) / ((1 - P.y) * P.x))
        (E.equation_toMontgomery P.equation hy) := by
  change (if hy : P.y = 1 then _ else _) = _
  rw [dite_eq_right hy]

private theorem toMontgomeryEquivAux_symm_zero :
    E.toMontgomeryEquivAux.symm .zero = ⟨0, 1, E.equation_zero_one⟩ := by
  rfl

private theorem toMontgomeryEquivAux_symm_some {u v : F} (h : E.toMontgomery.Equation u v) :
    E.toMontgomeryEquivAux.symm (.some u v h) =
      ⟨u / v, (u - 1) / (u + 1), E.equation_ofMontgomery h⟩ := by
  rfl

end IsComplete

end TwistedEdwardsModel
