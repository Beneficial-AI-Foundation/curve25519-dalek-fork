/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.Curve.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
import EllipticCurve.Curve.Impl
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination
public section

/-! # Montgomery models: definitions

A Montgomery model `M = (A, B)` over a field `F` is the equation `B v² = u³ + A u² + u`
(`MontgomeryModel.Equation`). Its points (`M.Point`) are the affine solutions plus the point at
infinity, as an inductive type of our own (no Mathlib type appears in the API). When `M` is
nonsingular
(`M.IsNonsingular`) it realises a curve `M.toCurve : Curve F`, and the group structure on
`M.Point` is *defined* by transport along a hidden bijection with the points of a model of that
curve, which then becomes the group isomorphism `M.pointEquiv : M.Point ≃+ M.toCurve.Point`.

Everything in the section "The curve of a Montgomery model" is a hidden construction: the
characterising lemmas (`zero_def`, `neg_some`, `some_add_some_of_u_ne`, …) are proved in
`EllipticCurve.Montgomery.Lemmas` by `import all` of this module, and nothing else may depend on
the bodies. Today the construction goes through the Weierstrass model `y² = x³ + A B x² + B² x`
under `(u, v) ↦ (B u, B² v)`: the group on `M.Point` is transported from Mathlib's group law on
that model, `M.toCurve` is its class `Curve.ofWeierstrass`, and `M.pointEquiv` composes the
transport with `Curve.pointEquivOfWeierstrass`; this is invisible outside this file. -/

universe u

/-- A Montgomery model `B v² = u³ + A u² + u` over `F`: the coefficients of the equation. -/
structure MontgomeryModel (F : Type u) [Field F] where
  /-- The coefficient of `u²`. -/
  A : F
  /-- The coefficient of `v²`. -/
  B : F

namespace MontgomeryModel

variable {F : Type u} [Field F] (M : MontgomeryModel F)

/-- The defining equation `B v² = u³ + A u² + u` of the model. -/
@[expose] def Equation (u v : F) : Prop :=
  M.B * v ^ 2 = u ^ 3 + M.A * u ^ 2 + u

/-- The right-hand side `f(u) = u³ + A u² + u` of the equation. -/
@[expose] def rhs (u : F) : F :=
  u ^ 3 + M.A * u ^ 2 + u

/-- Nonsingularity of the model: `B ≠ 0`, `A² ≠ 4`, and `2 ≠ 0` in `F` (in characteristic `2`
every Montgomery model is singular). Equivalently, the discriminant `16 B⁶ (A² - 4)` of the
Weierstrass model `y² = x³ + A B x² + B² x` is nonzero. -/
class IsNonsingular : Prop where
  two_ne_zero : (2 : F) ≠ 0
  B_ne_zero : M.B ≠ 0
  A_sq_ne_four : M.A ^ 2 ≠ 4

/-- The points of `M`: the affine solutions of its equation, and the point at infinity. -/
inductive Point
  /-- The point at infinity, the zero of the group. -/
  | zero
  /-- The affine point `(u, v)` of the model. -/
  | some (u v : F) (h : M.Equation u v)
  deriving DecidableEq

namespace Point

variable {M}

/-- The `u`-coordinate of a point, with `∞ ↦ 0` (the x-only convention). -/
def u : M.Point → F
  | .zero => 0
  | .some u _ _ => u

/-- The `v`-coordinate of a point, with `∞ ↦ 0`. -/
def v : M.Point → F
  | .zero => 0
  | .some _ v _ => v

end Point

/-! ### Addition formulas

The coordinate formulas of the chord-and-tangent law, as functions of the slope `ℓ` of the line
through the two points: exposed, so that they can be evaluated. The slope is `chordSlope` when
the `u`-coordinates differ and `tangentSlope` when the points coincide; see
`some_add_some_of_u_ne` and `some_add_some_of_v_ne` in `EllipticCurve.Montgomery.Lemmas`. -/

/-- The slope `(v₂ - v₁) / (u₂ - u₁)` of the chord through `(u₁, v₁)` and `(u₂, v₂)`. -/
@[expose] def chordSlope (u₁ v₁ u₂ v₂ : F) : F :=
  (v₂ - v₁) / (u₂ - u₁)

/-- The slope `(3 u² + 2 A u + 1) / (2 B v)` of the tangent at `(u, v)`. -/
@[expose] def tangentSlope (u v : F) : F :=
  (3 * u ^ 2 + 2 * M.A * u + 1) / (2 * M.B * v)

/-- The `u`-coordinate `B ℓ² - A - u₁ - u₂` of the sum of `(u₁, v₁)` and `(u₂, v₂)`, where `ℓ` is
the slope of the line through them. -/
@[expose] def addU (u₁ u₂ ℓ : F) : F :=
  M.B * ℓ ^ 2 - M.A - u₁ - u₂

/-- The `v`-coordinate `ℓ (u₁ - u₃) - v₁` of the sum of `(u₁, v₁)` and `(u₂, v₂)`, where `ℓ` is
the slope of the line through them and `u₃ = M.addU u₁ u₂ ℓ`. -/
@[expose] def addV (u₁ u₂ v₁ ℓ : F) : F :=
  ℓ * (u₁ - M.addU u₁ u₂ ℓ) - v₁

/-! ### Twists -/

/-- The quadratic twist of `M` by `c`: the model `B c v² = u³ + A u² + u`. -/
def twist (c : F) : MontgomeryModel F :=
  ⟨M.A, M.B * c⟩

/-! ### The curve of a Montgomery model (hidden construction) -/

/-- The Weierstrass model `y² = x³ + A B x² + B² x`, the image of `M` under
`(u, v) ↦ (B u, B² v)`. Internal. -/
private def toWeierstrass : WeierstrassCurve.Affine F :=
  ⟨0, M.A * M.B, 0, M.B ^ 2, 0⟩

private theorem Δ_toWeierstrass : M.toWeierstrass.Δ = 16 * M.B ^ 6 * (M.A ^ 2 - 4) := by
  simp only [toWeierstrass, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private instance instIsEllipticToWeierstrass [M.IsNonsingular] : M.toWeierstrass.IsElliptic where
  isUnit := by
    rw [Δ_toWeierstrass, isUnit_iff_ne_zero]
    have h16 : (16 : F) ≠ 0 := by
      rw [show (16 : F) = 2 ^ 4 by norm_num]
      exact pow_ne_zero 4 (IsNonsingular.two_ne_zero (M := M))
    exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero 6 IsNonsingular.B_ne_zero))
      (sub_ne_zero.mpr IsNonsingular.A_sq_ne_four)

/-- The curve realised by `M`: the class of its Weierstrass model. Hidden construction. -/
noncomputable def toCurve [M.IsNonsingular] : Curve F :=
  Curve.ofWeierstrass M.toWeierstrass

/-- The equation of `M` at `(u, v)` is the Weierstrass equation at `(B u, B² v)`. -/
private theorem equation_iff_toWeierstrass (hB : M.B ≠ 0) {u v : F} :
    M.Equation u v ↔ M.toWeierstrass.Equation (M.B * u) (M.B ^ 2 * v) := by
  rw [Equation, WeierstrassCurve.Affine.equation_iff]
  simp only [toWeierstrass]
  constructor
  · intro h
    linear_combination M.B ^ 3 * h
  · intro h
    exact mul_left_cancel₀ (pow_ne_zero 3 hB) (by linear_combination h)

private theorem equation_div [M.IsNonsingular] {x y : F} (h : M.toWeierstrass.Nonsingular x y) :
    M.Equation (x / M.B) (y / M.B ^ 2) := by
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  rw [M.equation_iff_toWeierstrass hB, mul_div_cancel₀ _ hB, mul_div_cancel₀ _ (pow_ne_zero 2 hB)]
  exact h.1

private theorem nonsingular_mul [M.IsNonsingular] {u v : F} (h : M.Equation u v) :
    M.toWeierstrass.Nonsingular (M.B * u) (M.B ^ 2 * v) :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    ((M.equation_iff_toWeierstrass IsNonsingular.B_ne_zero).mp h)

/-- The bijection `(u, v) ↦ (B u, B² v)` between the points of `M` and those of its Weierstrass
model. Internal. -/
private noncomputable def pointEquivWeierstrass [M.IsNonsingular] :
    M.Point ≃ M.toWeierstrass.Point where
  toFun
    | .zero => .zero
    | .some u v h => .some (M.B * u) (M.B ^ 2 * v) (M.nonsingular_mul h)
  invFun
    | .zero => .zero
    | .some x y h => .some (x / M.B) (y / M.B ^ 2) (M.equation_div h)
  left_inv P := by
    have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
    cases P with
    | zero => rfl
    | some u v h =>
      simp only [Point.some.injEq]
      exact ⟨mul_div_cancel_left₀ u hB, mul_div_cancel_left₀ v (pow_ne_zero 2 hB)⟩
  right_inv P := by
    have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
    cases P with
    | zero => rfl
    | some x y h =>
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨mul_div_cancel₀ x hB, mul_div_cancel₀ y (pow_ne_zero 2 hB)⟩

private theorem pointEquivWeierstrass_zero [M.IsNonsingular] :
    M.pointEquivWeierstrass .zero = .zero := by
  rfl

private theorem pointEquivWeierstrass_some [M.IsNonsingular] {u v : F} (h : M.Equation u v) :
    M.pointEquivWeierstrass (.some u v h) =
      .some (M.B * u) (M.B ^ 2 * v) (M.nonsingular_mul h) := by
  rfl

private theorem pointEquivWeierstrass_symm_zero [M.IsNonsingular] :
    M.pointEquivWeierstrass.symm .zero = .zero := by
  rfl

private theorem pointEquivWeierstrass_symm_some [M.IsNonsingular] {x y : F}
    (h : M.toWeierstrass.Nonsingular x y) :
    M.pointEquivWeierstrass.symm (.some x y h) =
      .some (x / M.B) (y / M.B ^ 2) (M.equation_div h) := by
  rfl

open scoped Classical in
/-- The group law on the points of `M`, transported from Mathlib's group law on the points of its
Weierstrass model along `pointEquivWeierstrass`. Hidden construction: it is characterised by
`zero_def`, `neg_some`, `some_add_some_of_u_ne`, `some_add_some_of_v_ne` and
`some_add_some_eq_zero` (`EllipticCurve.Montgomery.Lemmas`). -/
@[no_expose] noncomputable instance instAddCommGroupPoint [M.IsNonsingular] :
    AddCommGroup M.Point :=
  M.pointEquivWeierstrass.addCommGroup

open scoped Classical in
/-- The points of `M` are the points of its curve, as groups: the transport along
`pointEquivWeierstrass` followed by the isomorphism between the Weierstrass model and the chosen
representative of its curve. Hidden construction. -/
noncomputable def pointEquiv [M.IsNonsingular] : M.Point ≃+ M.toCurve.Point :=
  M.pointEquivWeierstrass.addEquiv.trans (Curve.pointEquivOfWeierstrass M.toWeierstrass).symm

/-! The group operations on `M.Point` in terms of the Weierstrass model, for
`EllipticCurve.Montgomery.Lemmas`. Internal. The `DecidableEq F` of the Weierstrass group law is
always the classical one (`open scoped Classical`), so that the instance terms agree syntactically
between the construction and the lemmas. -/

private theorem zero_eq [M.IsNonsingular] : (0 : M.Point) = M.pointEquivWeierstrass.symm 0 := by
  rfl

private theorem neg_eq [M.IsNonsingular] (P : M.Point) :
    -P = M.pointEquivWeierstrass.symm (-M.pointEquivWeierstrass P) := by
  rfl

open scoped Classical in
private theorem add_eq [M.IsNonsingular] (P Q : M.Point) :
    P + Q = M.pointEquivWeierstrass.symm
      (M.pointEquivWeierstrass P + M.pointEquivWeierstrass Q) := by
  rfl

end MontgomeryModel
