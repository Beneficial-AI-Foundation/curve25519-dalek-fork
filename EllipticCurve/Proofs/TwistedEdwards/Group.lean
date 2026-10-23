/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Defs
import all EllipticCurve.TwistedEdwards.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public section

/-! # Twisted Edwards models: the group law in coordinates (proofs)

Not audited. The results here are re-exported, with the audited statements, by
`EllipticCurve.TwistedEdwards.Lemmas`: completeness (`addDen₁_ne_zero`, `addDen₂_ne_zero`),
closure (`equation_addX_addY`), and the main theorem `add_eq_mk`:
`P + Q = ⟨addX P Q, addY P Q, _⟩`.

## Route

The group on `E.Point` is the transport along the hidden bijection
`φ = E.toMontgomeryEquivAux : E.Point ≃ E.toMontgomery.Point`
(`EllipticCurve.TwistedEdwards.Defs`), so `P + Q = φ.symm (φ P + φ Q)` and it suffices to show
`φ ⟨addX P Q, addY P Q, _⟩ = φ P + φ Q` (`toMontgomeryEquivAux_add`). The right-hand side is
given by the chord-and-tangent formulas of `EllipticCurve.Montgomery.Lemmas`; the comparison is
reduced to polynomial identities in the Montgomery coordinates `(u₁, v₁)`, `(u₂, v₂)` modulo
the two Montgomery equations, discharged by `linear_combination` with explicit certificates
(computed with Singular, `lift`), after eliminating the Edwards coordinates through
`x = u / v`, `y = (u - 1) / (u + 1)` and the coefficients through `a B = A + 2`, `d B = A - 2`.

## Credits

The structure (`aux_eq_some`, `sum_formulas`, `finish`, `T_case`, the certificates `G1`–`G4`
and the case analysis of `toMontgomeryEquivAux_add_of_x_ne_zero`) follows
`Curve25519Dalek/Parity/EdwardsGroup.lean` of aeneas-use-cases (there for `a = -1` and
Montgomery `B = 1`; here for general `a` and `B`, which changes the certificates). The
completeness argument `d_mul_sq_ne_one` is Bernstein–Birkner–Joye–Lange–Peters' as formalised
in FEC `FFEC/Messy/Edwards/AddFormulaBase.lean` (`lam_sq_ne_one`). -/

universe u

namespace TwistedEdwardsModel.Proofs

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F}

/-! ### Completeness and closure of the addition formula -/

/-- Completeness: `λ = d x₁ x₂ y₁ y₂` satisfies `λ² ≠ 1` for two points of a complete model,
since `λ² = 1` would exhibit `d` as a square (BBJLP; after FEC `lam_sq_ne_one`). -/
theorem d_mul_sq_ne_one [E.IsComplete] {x₁ y₁ x₂ y₂ : F} (h1 : E.Equation x₁ y₁)
    (h2 : E.Equation x₂ y₂) : (E.d * x₁ * x₂ * y₁ * y₂) ^ 2 ≠ 1 := by
  unfold Equation at h1 h2
  intro hLamSq
  have hlamne : E.d * x₁ * x₂ * y₁ * y₂ ≠ 0 := by
    intro h
    rw [h] at hLamSq
    norm_num at hLamSq
  have hx1 : x₁ ≠ 0 := fun h => hlamne (by rw [h]; ring)
  have hy1 : y₁ ≠ 0 := fun h => hlamne (by rw [h]; ring)
  have hx2 : x₂ ≠ 0 := fun h => hlamne (by rw [h]; ring)
  obtain ⟨a', ha'⟩ := IsComplete.isSquare_a (E := E)
  have ha'0 : a' ≠ 0 := fun h => IsComplete.a_ne_zero (E := E) (by rw [ha', h]; ring)
  have lem1 : E.d * x₁ ^ 2 * y₁ ^ 2 * (E.a * x₂ ^ 2 + y₂ ^ 2) = E.a * x₁ ^ 2 + y₁ ^ 2 := by
    linear_combination E.d * x₁ ^ 2 * y₁ ^ 2 * h2 + hLamSq - h1
  have lem2 : (a' * x₁ + E.d * x₁ * x₂ * y₁ * y₂ * y₁) ^ 2 =
      E.d * x₁ ^ 2 * y₁ ^ 2 * (a' * x₂ + y₂) ^ 2 := by
    linear_combination (E.d * x₁ ^ 2 * y₁ ^ 2 * x₂ ^ 2 - x₁ ^ 2) * ha' + y₁ ^ 2 * hLamSq - lem1
  by_cases hcasePos : a' * x₂ + y₂ = 0
  · by_cases hcaseNeg : a' * x₂ - y₂ = 0
    · have h2x : 2 * a' * x₂ = 0 := by linear_combination hcasePos + hcaseNeg
      exact hx2 ((mul_eq_zero.mp h2x).resolve_left
        (mul_ne_zero (IsComplete.two_ne_zero (E := E)) ha'0))
    · exact IsComplete.not_isSquare_d (E := E)
        ⟨(a' * x₁ - E.d * x₁ * x₂ * y₁ * y₂ * y₁) / (x₁ * y₁ * (a' * x₂ - y₂)), by
          rw [← sq, div_pow,
            eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hx1 hy1) hcaseNeg))]
          linear_combination -lem2⟩
  · exact IsComplete.not_isSquare_d (E := E)
      ⟨(a' * x₁ + E.d * x₁ * x₂ * y₁ * y₂ * y₁) / (x₁ * y₁ * (a' * x₂ + y₂)), by
        rw [← sq, div_pow,
          eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hx1 hy1) hcasePos))]
        linear_combination -lem2⟩

/-- The denominator `1 + d x₁ x₂ y₁ y₂` is nonzero on a complete model. -/
theorem addDen₁_ne_zero [E.IsComplete] (P Q : E.Point) : addDen₁ P Q ≠ 0 := fun h =>
  d_mul_sq_ne_one P.equation Q.equation (by
    unfold addDen₁ at h
    linear_combination (E.d * P.x * Q.x * P.y * Q.y - 1) * h)

/-- The denominator `1 - d x₁ x₂ y₁ y₂` is nonzero on a complete model. -/
theorem addDen₂_ne_zero [E.IsComplete] (P Q : E.Point) : addDen₂ P Q ≠ 0 := fun h =>
  d_mul_sq_ne_one P.equation Q.equation (by
    unfold addDen₂ at h
    linear_combination -(E.d * P.x * Q.x * P.y * Q.y + 1) * h)

/-- Certificate for closure: the numerators and denominators of the sum satisfy the equation
cleared of denominators (after FEC `addCoords_onCurve`). -/
private theorem cert_closure (a d x₁ y₁ x₂ y₂ : F)
    (h1 : a * x₁ ^ 2 + y₁ ^ 2 = 1 + d * x₁ ^ 2 * y₁ ^ 2)
    (h2 : a * x₂ ^ 2 + y₂ ^ 2 = 1 + d * x₂ ^ 2 * y₂ ^ 2) :
    a * (x₁ * y₂ + x₂ * y₁) ^ 2 * (1 - d * x₁ * x₂ * y₁ * y₂) ^ 2 +
        (y₁ * y₂ - a * x₁ * x₂) ^ 2 * (1 + d * x₁ * x₂ * y₁ * y₂) ^ 2 =
      (1 + d * x₁ * x₂ * y₁ * y₂) ^ 2 * (1 - d * x₁ * x₂ * y₁ * y₂) ^ 2 +
        d * (x₁ * y₂ + x₂ * y₁) ^ 2 * (y₁ * y₂ - a * x₁ * x₂) ^ 2 := by
  linear_combination
    (x₁ ^ 2 * y₁ ^ 2 * x₂ ^ 4 * a ^ 2 * d + x₁ ^ 2 * y₁ ^ 2 * y₂ ^ 4 * d + 2 * x₁ ^ 2 * y₁ ^ 2 *
    x₂ ^ 2 * a ^ 2 - 2
      * x₁ ^ 2 * y₁ ^ 2 * x₂ ^ 2 * a * d + 2 * x₁ ^ 2 * y₁ ^ 2 * y₂ ^ 2 * a - 2 * x₁ ^ 2 * y₁ ^ 2
      * y₂ ^ 2 * d -
      x₁ ^ 2 * x₂ ^ 2 * a ^ 2 - 2 * x₁ ^ 2 * y₁ ^ 2 * a - y₁ ^ 2 * x₂ ^ 2 * a - x₁ ^ 2 * y₂ ^ 2 *
      a + x₁ ^ 2 * y₁ ^ 2
      * d - y₁ ^ 2 * y₂ ^ 2 + x₁ ^ 2 * a + y₁ ^ 2 + 1) * h1 +
    (x₁ ^ 4 * y₁ ^ 4 * x₂ ^ 2 * y₂ ^ 2 * d ^ 3 + x₁ ^ 4 * y₁ ^ 4 * x₂ ^ 2 * a * d ^ 2 + x₁ ^ 4 *
    y₁ ^ 4 * y₂ ^ 2 * d ^ 2
      - x₁ ^ 4 * y₁ ^ 2 * x₂ ^ 2 * a ^ 2 * d + 2 * x₁ ^ 4 * y₁ ^ 4 * a * d - x₁ ^ 2 * y₁ ^ 4 * x₂
      ^ 2 * a * d -
      x₁ ^ 4 * y₁ ^ 2 * y₂ ^ 2 * a * d - x₁ ^ 4 * y₁ ^ 4 * d ^ 2 - x₁ ^ 2 * y₁ ^ 4 * y₂ ^ 2 * d -
      2 * x₁ ^ 4 * y₁ ^ 2
      * a ^ 2 - 2 * x₁ ^ 2 * y₁ ^ 4 * a + x₁ ^ 4 * a ^ 2 + 4 * x₁ ^ 2 * y₁ ^ 2 * a - 2 * x₁ ^ 2 *
      y₁ ^ 2 * d +
      y₁ ^ 4) * h2

/-- The equation at `(N₁ / D₁, N₂ / D₂)` from the equation cleared of denominators. -/
private theorem equation_of_mul (a d x y D₁ D₂ N₁ N₂ : F) (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hx : x * D₁ = N₁) (hy : y * D₂ = N₂)
    (key : a * N₁ ^ 2 * D₂ ^ 2 + N₂ ^ 2 * D₁ ^ 2 = D₁ ^ 2 * D₂ ^ 2 + d * N₁ ^ 2 * N₂ ^ 2) :
    a * x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2 := by
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hD₁) (pow_ne_zero 2 hD₂))
  linear_combination (a * D₂ ^ 2 * (x * D₁ + N₁) - d * N₂ ^ 2 * (x * D₁ + N₁)) * hx +
    (D₁ ^ 2 * (y * D₂ + N₂) - d * (x * D₁) ^ 2 * (y * D₂ + N₂)) * hy + key

/-- Closure: the sum of two points of a complete model is on the model. -/
theorem equation_addX_addY [E.IsComplete] (P Q : E.Point) :
    E.Equation (addX P Q) (addY P Q) :=
  equation_of_mul E.a E.d _ _ _ _ _ _ (addDen₁_ne_zero P Q) (addDen₂_ne_zero P Q)
    (div_mul_cancel₀ _ (addDen₁_ne_zero P Q)) (div_mul_cancel₀ _ (addDen₂_ne_zero P Q))
    (cert_closure E.a E.d P.x P.y Q.x Q.y P.equation Q.equation)

/-- The addition formula is commutative: `x`-coordinate. -/
theorem addX_comm (P Q : E.Point) : addX P Q = addX Q P := by
  unfold addX addDen₁
  ring

/-- The addition formula is commutative: `y`-coordinate. -/
theorem addY_comm (P Q : E.Point) : addY P Q = addY Q P := by
  unfold addY addDen₂
  ring

/-- Adding `(0, 1)` on the left: `x`-coordinate. -/
theorem addX_of_x_eq_zero_of_y_eq_one {P : E.Point} (Q : E.Point) (hx : P.x = 0)
    (hy : P.y = 1) : addX P Q = Q.x := by
  simp [addX, addDen₁, hx, hy]

/-- Adding `(0, 1)` on the left: `y`-coordinate. -/
theorem addY_of_x_eq_zero_of_y_eq_one {P : E.Point} (Q : E.Point) (hx : P.x = 0)
    (hy : P.y = 1) : addY P Q = Q.y := by
  simp [addY, addDen₂, hx, hy]

/-- Adding `(0, -1)` on the left: `x`-coordinate. -/
theorem addX_of_x_eq_zero_of_y_eq_neg_one {P : E.Point} (Q : E.Point) (hx : P.x = 0)
    (hy : P.y = -1) : addX P Q = -Q.x := by
  simp [addX, addDen₁, hx, hy]

/-- Adding `(0, -1)` on the left: `y`-coordinate. -/
theorem addY_of_x_eq_zero_of_y_eq_neg_one {P : E.Point} (Q : E.Point) (hx : P.x = 0)
    (hy : P.y = -1) : addY P Q = -Q.y := by
  simp [addY, addDen₂, hx, hy]

/-! ### Polynomial identities in Montgomery coordinates

`DX`, `DY`, `NX`, `NY` are `B W` times the denominators and numerators of the Edwards sum,
`W = v₁ v₂ (u₁ + 1) (u₂ + 1)`, written in the Montgomery coordinates (`sum_formulas`). -/

/-- `B W (1 + d x₁ x₂ y₁ y₂)` in Montgomery coordinates. -/
private def DX (A B u₁ u₂ v₁ v₂ : F) : F :=
  B * (v₁ * v₂ * (u₁ + 1) * (u₂ + 1)) + (A - 2) * u₁ * u₂ * (u₁ - 1) * (u₂ - 1)

/-- `B W (1 - d x₁ x₂ y₁ y₂)` in Montgomery coordinates. -/
private def DY (A B u₁ u₂ v₁ v₂ : F) : F :=
  B * (v₁ * v₂ * (u₁ + 1) * (u₂ + 1)) - (A - 2) * u₁ * u₂ * (u₁ - 1) * (u₂ - 1)

/-- `B W (x₁ y₂ + x₂ y₁)` in Montgomery coordinates. -/
private def NX (B u₁ u₂ v₁ v₂ : F) : F :=
  B * (u₁ * (u₂ - 1) * (u₁ + 1) * v₂ + u₂ * (u₁ - 1) * (u₂ + 1) * v₁)

/-- `B W (y₁ y₂ - a x₁ x₂)` in Montgomery coordinates. -/
private def NY (A B u₁ u₂ v₁ v₂ : F) : F :=
  B * (u₁ - 1) * (u₂ - 1) * v₁ * v₂ - (A + 2) * u₁ * u₂ * (u₁ + 1) * (u₂ + 1)

/-- Secant case, `u`-coordinate: `(1 - yR) u₃ = 1 + yR` cleared of denominators. -/
private theorem G1 (A B u₁ u₂ v₁ v₂ : F) (hv1 : B * v₁ ^ 2 = u₁ ^ 3 + A * u₁ ^ 2 + u₁)
    (hv2 : B * v₂ ^ 2 = u₂ ^ 3 + A * u₂ ^ 2 + u₂) :
    (DY A B u₁ u₂ v₁ v₂ - NY A B u₁ u₂ v₁ v₂) *
        (B * (v₂ - v₁) ^ 2 - (A + u₁ + u₂) * (u₂ - u₁) ^ 2) =
      (DY A B u₁ u₂ v₁ v₂ + NY A B u₁ u₂ v₁ v₂) * (u₂ - u₁) ^ 2 := by
  unfold DY NY
  linear_combination
    (2 * v₁ * v₂ * B * u₁ + 2 * v₁ * v₂ * B * u₂ + 2 * A * u₁ ^ 2 * u₂ - 2 * A * u₁ * u₂ ^ 2 + 4 *
      u₁ ^ 2 * u₂ ^ 2 - 4 * A * u₂ ^ 3 - 4 * u₁ * u₂ ^ 3 - 4 * u₂ ^ 4 - 4 * u₂ ^ 2) * hv1 +
    (-4 * v₁ ^ 2 * B * u₁ + 2 * v₁ * v₂ * B * u₁ - 4 * v₁ ^ 2 * B * u₂ + 2 * v₁ * v₂ * B * u₂ + 2
      * A * u₁ ^ 2 * u₂ + 2 * A * u₁ * u₂ ^ 2 + 4 * u₁ ^ 2 * u₂ ^ 2 + 4 * u₁ * u₂) * hv2

/-- Secant case, `v`-coordinate: `xR v₃ = u₃` cleared of denominators. -/
private theorem G2 (A B u₁ u₂ v₁ v₂ : F) (hv1 : B * v₁ ^ 2 = u₁ ^ 3 + A * u₁ ^ 2 + u₁)
    (hv2 : B * v₂ ^ 2 = u₂ ^ 3 + A * u₂ ^ 2 + u₂) :
    NX B u₁ u₂ v₁ v₂ *
        ((v₂ - v₁) * (u₁ * (u₂ - u₁) ^ 2 -
            (B * (v₂ - v₁) ^ 2 - (A + u₁ + u₂) * (u₂ - u₁) ^ 2)) - v₁ * (u₂ - u₁) ^ 3) =
      DX A B u₁ u₂ v₁ v₂ * (B * (v₂ - v₁) ^ 2 - (A + u₁ + u₂) * (u₂ - u₁) ^ 2) *
        (u₂ - u₁) := by
  unfold DX NX
  linear_combination
    (2 * v₁ * v₂ * B * u₁ ^ 2 * u₂ + v₁ ^ 2 * B * u₁ * u₂ ^ 2 - 4 * v₁ * v₂ * B * u₁ * u₂ ^ 2 + A *
      u₁ ^ 3 * u₂ ^ 2 - 4 * A * u₁ ^ 2 * u₂ ^ 3 + 4 * A * u₁ * u₂ ^ 4 - 2 * u₁ ^ 2 * u₂ ^ 4 + 3 *
      u₁ * u₂ ^ 5 +
      v₁ ^ 2 * B * u₁ * u₂ - 2 * v₁ * v₂ * B * u₁ * u₂ - A * u₁ ^ 3 * u₂ - v₁ ^ 2 * B * u₂ ^ 2 + 2
      * v₁
      * v₂ * B * u₂ ^ 2 + 3 * A * u₁ ^ 2 * u₂ ^ 2 - 2 * u₁ ^ 3 * u₂ ^ 2 - 2 * A * u₁ * u₂ ^ 3 + 6
      * u₁ ^ 2 *
      u₂ ^ 3 - 5 * u₁ * u₂ ^ 4 + u₂ ^ 5 - v₁ ^ 2 * B * u₂ + 2 * v₁ * v₂ * B * u₂ + A * u₁ ^ 2 * u₂
      + 2 *
      u₁ ^ 3 * u₂ - 2 * A * u₁ * u₂ ^ 2 - 4 * u₁ ^ 2 * u₂ ^ 2 + u₁ * u₂ ^ 3 + u₂ ^ 4 + u₁ * u₂ ^ 2
      - u₂ ^ 3 -
      u₂ ^ 2) * hv1 +
    (-5 * v₁ ^ 2 * B * u₁ ^ 2 * u₂ + 4 * v₁ * v₂ * B * u₁ ^ 2 * u₂ - v₂ ^ 2 * B * u₁ ^ 2 * u₂ + A
    * u₁ ^ 4
      * u₂ + 2 * u₁ ^ 5 * u₂ + 5 * v₁ ^ 2 * B * u₁ * u₂ ^ 2 - 2 * v₁ * v₂ * B * u₁ * u₂ ^ 2 - A *
      u₁ ^ 3 *
      u₂ ^ 2 - 3 * u₁ ^ 4 * u₂ ^ 2 - A * u₁ ^ 2 * u₂ ^ 3 + v₁ ^ 2 * B * u₁ ^ 2 - 2 * v₁ * v₂ * B *
      u₁ ^ 2 + v₂ ^ 2
      * B * u₁ ^ 2 - A * u₁ ^ 4 - 2 * u₁ ^ 5 + 2 * v₁ * v₂ * B * u₁ * u₂ - v₂ ^ 2 * B * u₁ * u₂ +
      2 * A
      * u₁ ^ 3 * u₂ + 5 * u₁ ^ 4 * u₂ - v₁ ^ 2 * B * u₂ ^ 2 - 2 * A * u₁ ^ 2 * u₂ ^ 2 - 5 * u₁ ^ 3
      * u₂ ^ 2 + A
      * u₁ * u₂ ^ 3 + 2 * u₁ ^ 2 * u₂ ^ 3 + v₁ ^ 2 * B * u₁ - 2 * v₁ * v₂ * B * u₁ + v₂ ^ 2 * B *
      u₁ - A *
      u₁ ^ 3 - 2 * u₁ ^ 4 - v₁ ^ 2 * B * u₂ + 3 * A * u₁ ^ 2 * u₂ + 5 * u₁ ^ 3 * u₂ - A * u₁ * u₂
      ^ 2 - u₁ ^ 2
      * u₂ ^ 2 - 2 * u₁ * u₂ ^ 3 - u₁ ^ 2 * u₂ + u₁ * u₂ ^ 2 + u₁ * u₂) * hv2

/-- Tangent case, `u`-coordinate: `(1 - yR) u₃ = 1 + yR` cleared of denominators. -/
private theorem G3 (A B u v : F) (hv : B * v ^ 2 = u ^ 3 + A * u ^ 2 + u) :
    (DY A B u u v v - NY A B u u v v) *
        (B * (3 * u ^ 2 + 2 * A * u + 1) ^ 2 - (A + u + u) * (2 * B * v) ^ 2) =
      (DY A B u u v v + NY A B u u v v) * (2 * B * v) ^ 2 := by
  unfold DY NY
  linear_combination
    (-16 * v ^ 2 * A * B ^ 2 * u - 40 * v ^ 2 * B ^ 2 * u ^ 2 - 16 * A ^ 2 * B * u ^ 3 - 48 * A *
    B * u ^ 4 -
      36 * B * u ^ 5 - 8 * v ^ 2 * B ^ 2 - 16 * A * B * u ^ 2 - 24 * B * u ^ 3 - 4 * B * u) * hv

/-- Tangent case, `v`-coordinate: `xR v₃ = u₃` cleared of denominators. -/
private theorem G4 (A B u v : F) (hv : B * v ^ 2 = u ^ 3 + A * u ^ 2 + u) :
    NX B u u v v *
        ((3 * u ^ 2 + 2 * A * u + 1) * (u * (2 * B * v) ^ 2 -
            (B * (3 * u ^ 2 + 2 * A * u + 1) ^ 2 - (A + u + u) * (2 * B * v) ^ 2)) -
          v * (2 * B * v) ^ 3) =
      DX A B u u v v * (B * (3 * u ^ 2 + 2 * A * u + 1) ^ 2 - (A + u + u) * (2 * B * v) ^ 2) *
        (2 * B * v) := by
  unfold DX NX
  linear_combination
    (8 * v ^ 3 * A * B ^ 3 * u ^ 2 + 24 * v * A ^ 2 * B ^ 2 * u ^ 4 + 72 * v * A * B ^ 2 * u ^ 5 +
    54 * v *
      B ^ 2 * u ^ 6 + 16 * v ^ 3 * A * B ^ 3 * u + 32 * v ^ 3 * B ^ 3 * u ^ 2 - 16 * v * A ^ 2 * B
      ^ 2 * u ^ 3 - 48
      * v * A * B ^ 2 * u ^ 4 - 36 * v * B ^ 2 * u ^ 5 + 8 * v ^ 3 * A * B ^ 3 + 32 * v ^ 3 * B ^
      3 * u - 8 * v
      * A ^ 2 * B ^ 2 * u ^ 2 + 18 * v * B ^ 2 * u ^ 4 - 16 * v * A * B ^ 2 * u ^ 2 - 24 * v * B ^
      2 * u ^ 3 - 8 *
      v * A * B ^ 2 * u - 6 * v * B ^ 2 * u ^ 2 - 4 * v * B ^ 2 * u - 2 * v * B ^ 2) * hv

/-- The Edwards numerators and denominators of the sum, times `B W`, in Montgomery coordinates
(after aeneas `sum_formulas`). -/
private theorem sum_formulas (a d A B x₁ y₁ x₂ y₂ u₁ u₂ v₁ v₂ : F) (hx₁ : x₁ * v₁ = u₁)
    (hx₂ : x₂ * v₂ = u₂) (hy₁ : y₁ * (u₁ + 1) = u₁ - 1) (hy₂ : y₂ * (u₂ + 1) = u₂ - 1)
    (haB : a * B = A + 2) (hdB : d * B = A - 2) :
    (1 + d * x₁ * x₂ * y₁ * y₂) * (B * (v₁ * v₂ * (u₁ + 1) * (u₂ + 1))) =
        DX A B u₁ u₂ v₁ v₂ ∧
      (1 - d * x₁ * x₂ * y₁ * y₂) * (B * (v₁ * v₂ * (u₁ + 1) * (u₂ + 1))) =
        DY A B u₁ u₂ v₁ v₂ ∧
      (x₁ * y₂ + x₂ * y₁) * (B * (v₁ * v₂ * (u₁ + 1) * (u₂ + 1))) = NX B u₁ u₂ v₁ v₂ ∧
      (y₁ * y₂ - a * x₁ * x₂) * (B * (v₁ * v₂ * (u₁ + 1) * (u₂ + 1))) =
        NY A B u₁ u₂ v₁ v₂ := by
  unfold DX DY NX NY
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination
      (y₁ * y₂ * u₁ * u₂ ^ 2 * d * B + y₁ * y₂ * u₁ * u₂ * d * B + y₁ * y₂ * u₂ ^ 2 * d * B + y₁ *
        y₂ * u₂ * d * B) * hx₁ +
      (x₁ * y₁ * y₂ * v₁ * u₁ * u₂ * d * B + x₁ * y₁ * y₂ * v₁ * u₁ * d * B + x₁ * y₁ * y₂ * v₁
        * u₂ * d * B + x₁ * y₁ * y₂ * v₁ * d * B) * hx₂ +
      (u₁ * u₂ ^ 2 * A - 2 * u₁ * u₂ ^ 2 - u₁ * u₂ * A + 2 * u₁ * u₂) * hy₁ +
      (y₁ * u₁ ^ 2 * u₂ * A - 2 * y₁ * u₁ ^ 2 * u₂ + y₁ * u₁ * u₂ * A - 2 * y₁ * u₁ * u₂) * hy₂ +
      (y₁ * y₂ * u₁ ^ 2 * u₂ ^ 2 + y₁ * y₂ * u₁ ^ 2 * u₂ + y₁ * y₂ * u₁ * u₂ ^ 2 + y₁ * y₂ * u₁ *
      u₂)
        * hdB
  · linear_combination
      (-y₁ * y₂ * u₁ * u₂ ^ 2 * d * B - y₁ * y₂ * u₁ * u₂ * d * B - y₁ * y₂ * u₂ ^ 2 * d * B - y₁ *
        y₂ * u₂ * d * B) * hx₁ +
      (-x₁ * y₁ * y₂ * v₁ * u₁ * u₂ * d * B - x₁ * y₁ * y₂ * v₁ * u₁ * d * B - x₁ * y₁ * y₂ * v₁
        * u₂ * d * B - x₁ * y₁ * y₂ * v₁ * d * B) * hx₂ +
      (-u₁ * u₂ ^ 2 * A + 2 * u₁ * u₂ ^ 2 + u₁ * u₂ * A - 2 * u₁ * u₂) * hy₁ +
      (-y₁ * u₁ ^ 2 * u₂ * A + 2 * y₁ * u₁ ^ 2 * u₂ - y₁ * u₁ * u₂ * A + 2 * y₁ * u₁ * u₂) * hy₂ +
      (-y₁ * y₂ * u₁ ^ 2 * u₂ ^ 2 - y₁ * y₂ * u₁ ^ 2 * u₂ - y₁ * y₂ * u₁ * u₂ ^ 2 - y₁ * y₂ * u₁ *
      u₂)
        * hdB
  · linear_combination
      (y₂ * v₂ * u₁ * u₂ * B + y₂ * v₂ * u₁ * B + y₂ * v₂ * u₂ * B + y₂ * v₂ * B) * hx₁ +
      (y₁ * v₁ * u₁ * u₂ * B + y₁ * v₁ * u₁ * B + y₁ * v₁ * u₂ * B + y₁ * v₁ * B) * hx₂ +
      (v₁ * u₂ ^ 2 * B + v₁ * u₂ * B) * hy₁ + (v₂ * u₁ ^ 2 * B + v₂ * u₁ * B) * hy₂
  · linear_combination
      (-u₁ * u₂ ^ 2 * a * B - u₁ * u₂ * a * B - u₂ ^ 2 * a * B - u₂ * a * B) * hx₁ +
      (-x₁ * v₁ * u₁ * u₂ * a * B - x₁ * v₁ * u₁ * a * B - x₁ * v₁ * u₂ * a * B - x₁ * v₁ * a *
        B) * hx₂ +
      (v₁ * v₂ * u₂ * B - v₁ * v₂ * B) * hy₁ + (y₁ * v₁ * v₂ * u₁ * B + y₁ * v₁ * v₂ * B) * hy₂ +
      (-u₁ ^ 2 * u₂ ^ 2 - u₁ ^ 2 * u₂ - u₁ * u₂ ^ 2 - u₁ * u₂) * haB

/-- Transfer from the cleared identities to the two relations `(1 - yR) X = 1 + yR`,
`xR Y = X` characterising `φ ⟨xR, yR, _⟩ = some X Y _` (after aeneas `finish`). Here
`(X, Y)` is the Montgomery sum with slope `ℓ = N / e`. -/
private theorem finish (A B xR yR X Y ℓ e N u₁ u₂ v₁ DXv DYv NXv NYv : F) (hl : ℓ * e = N)
    (hX : X = B * ℓ ^ 2 - A - u₁ - u₂) (hY : Y = ℓ * (u₁ - X) - v₁) (he : e ≠ 0)
    (hDX : DXv ≠ 0) (hDY : DYv ≠ 0) (hyR : yR * DYv = NYv) (hxR : xR * DXv = NXv)
    (g1 : (DYv - NYv) * (B * N ^ 2 - (A + u₁ + u₂) * e ^ 2) = (DYv + NYv) * e ^ 2)
    (g2 : NXv * (N * (u₁ * e ^ 2 - (B * N ^ 2 - (A + u₁ + u₂) * e ^ 2)) - v₁ * e ^ 3) =
      DXv * (B * N ^ 2 - (A + u₁ + u₂) * e ^ 2) * e) :
    (1 - yR) * X = 1 + yR ∧ xR * Y = X := by
  have hXe : X * e ^ 2 = B * N ^ 2 - (A + u₁ + u₂) * e ^ 2 := by
    rw [hX, ← hl]
    ring
  have hYe : Y * e ^ 3 = N * (u₁ * e ^ 2 - X * e ^ 2) - v₁ * e ^ 3 := by
    rw [hY, ← hl]
    ring
  constructor
  · apply mul_right_cancel₀ (mul_ne_zero hDY (pow_ne_zero 2 he))
    linear_combination (DYv - NYv) * hXe - (X * e ^ 2 + e ^ 2) * hyR + g1
  · apply mul_right_cancel₀ (mul_ne_zero hDX (pow_ne_zero 3 he))
    linear_combination (Y * e ^ 3) * hxR + NXv * hYe - (DXv * e + NXv * N) * hXe + g2

/-- Adding the point `(0, -1)` (Montgomery `(0, 0)`) to `(x, y)` gives `(-x, -y)`: the two
relations for the chord through `(0, 0)` and `(u, v)` (after aeneas `T_case`). -/
private theorem T_case (A B x y u v ℓ X Y : F) (hu : u * (1 - y) = 1 + y) (hv : v * x = u)
    (hc : B * v ^ 2 = u ^ 3 + A * u ^ 2 + u) (hu0 : u ≠ 0) (hl : ℓ = (v - 0) / (u - 0))
    (hX : X = B * ℓ ^ 2 - A - 0 - u) (hY : Y = ℓ * (0 - X) - 0) :
    (1 - -y) * X = 1 + -y ∧ -x * Y = X := by
  have hl' : ℓ * u = v := by
    rw [hl, sub_zero, sub_zero, div_mul_cancel₀ _ hu0]
  have hXu : X * u = 1 := by
    apply mul_right_cancel₀ hu0
    rw [hX]
    linear_combination B * (ℓ * u + v) * hl' + hc
  rw [hY]
  constructor
  · linear_combination (1 - y) * hXu - X * hu
  · linear_combination X ^ 2 * x * hl' + X ^ 2 * hv - X * (x * ℓ - 1) * hXu

/-! ### The bijection on the sum -/

variable [E.IsComplete]

/-- `φ P = some X Y _` as soon as `(1 - y) X = 1 + y` and `x Y = X` (after aeneas
`phi_eq_some`): the two relations determine the image, including at `(0, -1)`. -/
private theorem toMontgomeryEquivAux_eq_some (P : E.Point) {X Y : F} (hX : (1 - P.y) * X = 1 + P.y)
    (hY : P.x * Y = X) (h : E.toMontgomery.Equation X Y) :
    E.toMontgomeryEquivAux P = .some X Y h := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  have hy : P.y ≠ 1 := by
    intro hy
    rw [hy] at hX
    exact h2 (by linear_combination -hX)
  rw [toMontgomeryEquivAux_apply_of_y_ne_one hy]
  simp only [MontgomeryModel.Point.some.injEq]
  have hy1 : 1 - P.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hu : (1 + P.y) / (1 - P.y) = X := by
    rw [div_eq_iff hy1]
    linear_combination -hX
  refine ⟨hu, ?_⟩
  by_cases hx : P.x = 0
  · have hy' : P.y = -1 := (y_eq_one_or_eq_neg_one_of_x_eq_zero P.equation hx).resolve_left hy
    have hX0 : X = 0 := by
      rw [hy'] at hX
      exact (mul_eq_zero.mp (by linear_combination hX : (2 : F) * X = 0)).resolve_left h2
    have hY0 : Y = 0 := E.toMontgomery_v_eq_zero_of_u_eq_zero h hX0
    rw [hx, hy', hY0]
    norm_num
  · rw [← div_div, hu, ← hY, mul_div_cancel_left₀ _ hx]

/-- For `x ≠ 0`, `φ P = some u v _` with `u (1 - y) = 1 + y`, `v x = u` and `u`, `v`,
`u + 1` nonzero. -/
private theorem toMontgomeryEquivAux_spec (P : E.Point) (hx : P.x ≠ 0) :
    ∃ (u v : F) (h : E.toMontgomery.Equation u v), E.toMontgomeryEquivAux P = .some u v h ∧
      u * (1 - P.y) = 1 + P.y ∧ v * P.x = u ∧ u ≠ 0 ∧ v ≠ 0 ∧ u + 1 ≠ 0 := by
  have hy := y_ne_one_of_x_ne_zero P.equation hx
  have hy1 : 1 - P.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hy2 : 1 + P.y ≠ 0 := fun h0 =>
    y_ne_neg_one_of_x_ne_zero P.equation hx (by linear_combination h0)
  refine ⟨_, _, _, toMontgomeryEquivAux_apply_of_y_ne_one hy, div_mul_cancel₀ _ hy1, ?_,
    div_ne_zero hy2 hy1, div_ne_zero hy2 (mul_ne_zero hy1 hx), ?_⟩
  · rw [← div_div, div_mul_cancel₀ _ hx]
  · exact E.toMontgomery_u_add_one_ne_zero (E.equation_toMontgomery P.equation hy)

/-- The sum formula is compatible with `φ` when `P.x = 0`, i.e. `P ∈ {(0, 1), (0, -1)}`. -/
private theorem toMontgomeryEquivAux_add_of_x_eq_zero (P Q : E.Point) (hPx : P.x = 0) :
    E.toMontgomeryEquivAux ⟨addX P Q, addY P Q, equation_addX_addY P Q⟩ =
      E.toMontgomeryEquivAux P + E.toMontgomeryEquivAux Q := by
  obtain hPy | hPy := y_eq_one_or_eq_neg_one_of_x_eq_zero P.equation hPx
  · have hR : (⟨addX P Q, addY P Q, equation_addX_addY P Q⟩ : E.Point) = Q :=
      Point.ext (addX_of_x_eq_zero_of_y_eq_one Q hPx hPy)
        (addY_of_x_eq_zero_of_y_eq_one Q hPx hPy)
    rw [hR, toMontgomeryEquivAux_apply_of_y_eq_one hPy, ← MontgomeryModel.zero_def, zero_add]
  · have hP : E.toMontgomeryEquivAux P = .some 0 0 E.toMontgomery_equation_zero_zero :=
      toMontgomeryEquivAux_eq_some P (by rw [hPy]; ring) (by rw [hPx]; ring) _
    by_cases hQx : Q.x = 0
    · obtain hQy | hQy := y_eq_one_or_eq_neg_one_of_x_eq_zero Q.equation hQx
      · have hR : (⟨addX P Q, addY P Q, equation_addX_addY P Q⟩ : E.Point) = P :=
          Point.ext (show addX P Q = P.x by
              rw [addX_comm]; exact addX_of_x_eq_zero_of_y_eq_one P hQx hQy)
            (show addY P Q = P.y by
              rw [addY_comm]; exact addY_of_x_eq_zero_of_y_eq_one P hQx hQy)
        rw [hR, toMontgomeryEquivAux_apply_of_y_eq_one hQy, ← MontgomeryModel.zero_def,
          add_zero]
      · have hQ : E.toMontgomeryEquivAux Q = .some 0 0 E.toMontgomery_equation_zero_zero :=
          toMontgomeryEquivAux_eq_some Q (by rw [hQy]; ring) (by rw [hQx]; ring) _
        rw [hP, hQ, MontgomeryModel.some_add_some_eq_zero _ _ rfl neg_zero.symm,
          MontgomeryModel.zero_def]
        apply toMontgomeryEquivAux_apply_of_y_eq_one
        change addY P Q = 1
        rw [addY_of_x_eq_zero_of_y_eq_neg_one Q hPx hPy, hQy, neg_neg]
    · obtain ⟨u, v, h, hQ, hu, hv, hu0, hv0, hu1⟩ := toMontgomeryEquivAux_spec Q hQx
      rw [hP, hQ, MontgomeryModel.some_add_some_of_u_ne _ _ hu0.symm]
      have key := T_case E.toMontgomery.A E.toMontgomery.B Q.x Q.y u v _ _ _ hu hv h hu0 rfl
        rfl rfl
      refine toMontgomeryEquivAux_eq_some _ ?_ ?_ _
      · change (1 - addY P Q) * _ = 1 + addY P Q
        rw [addY_of_x_eq_zero_of_y_eq_neg_one Q hPx hPy]
        exact key.1
      · change addX P Q * _ = _
        rw [addX_of_x_eq_zero_of_y_eq_neg_one Q hPx hPy]
        exact key.2

/-- The sum formula is compatible with `φ` when `P.x ≠ 0` and `Q.x ≠ 0`: the chord-and-tangent
formulas of the Montgomery model against `sum_formulas`, `finish` and the certificates
`G1`–`G4`; the inverse case `Q = -P` and the doubling case `Q = P` are recognised from the
Montgomery coordinates. -/
private theorem toMontgomeryEquivAux_add_of_x_ne_zero (P Q : E.Point) (hPx : P.x ≠ 0)
    (hQx : Q.x ≠ 0) :
    E.toMontgomeryEquivAux ⟨addX P Q, addY P Q, equation_addX_addY P Q⟩ =
      E.toMontgomeryEquivAux P + E.toMontgomeryEquivAux Q := by
  obtain ⟨u₁, v₁, h₁, hP, hu₁, hv₁, hu₁0, hv₁0, hu₁1⟩ := toMontgomeryEquivAux_spec P hPx
  obtain ⟨u₂, v₂, h₂, hQ, hu₂, hv₂, hu₂0, hv₂0, hu₂1⟩ := toMontgomeryEquivAux_spec Q hQx
  have h₁' : E.toMontgomery.B * v₁ ^ 2 = u₁ ^ 3 + E.toMontgomery.A * u₁ ^ 2 + u₁ := h₁
  have h₂' : E.toMontgomery.B * v₂ ^ 2 = u₂ ^ 3 + E.toMontgomery.A * u₂ ^ 2 + u₂ := h₂
  have hB := E.toMontgomery_B_ne_zero
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  have hx₁ : P.x * v₁ = u₁ := by linear_combination hv₁
  have hx₂ : Q.x * v₂ = u₂ := by linear_combination hv₂
  have hy₁ : P.y * (u₁ + 1) = u₁ - 1 := by linear_combination -hu₁
  have hy₂ : Q.y * (u₂ + 1) = u₂ - 1 := by linear_combination -hu₂
  obtain ⟨sDX, sDY, sNX, sNY⟩ := sum_formulas E.a E.d E.toMontgomery.A E.toMontgomery.B P.x P.y
    Q.x Q.y u₁ u₂ v₁ v₂ hx₁ hx₂ hy₁ hy₂ E.a_mul_toMontgomery_B E.d_mul_toMontgomery_B
  have hW : E.toMontgomery.B * (v₁ * v₂ * (u₁ + 1) * (u₂ + 1)) ≠ 0 :=
    mul_ne_zero hB (mul_ne_zero (mul_ne_zero (mul_ne_zero hv₁0 hv₂0) hu₁1) hu₂1)
  have hd1 : 1 + E.d * P.x * Q.x * P.y * Q.y ≠ 0 := addDen₁_ne_zero P Q
  have hd2 : 1 - E.d * P.x * Q.x * P.y * Q.y ≠ 0 := addDen₂_ne_zero P Q
  have hDX : DX E.toMontgomery.A E.toMontgomery.B u₁ u₂ v₁ v₂ ≠ 0 := by
    rw [← sDX]
    exact mul_ne_zero hd1 hW
  have hDY : DY E.toMontgomery.A E.toMontgomery.B u₁ u₂ v₁ v₂ ≠ 0 := by
    rw [← sDY]
    exact mul_ne_zero hd2 hW
  have hxR : addX P Q * DX E.toMontgomery.A E.toMontgomery.B u₁ u₂ v₁ v₂ =
      NX E.toMontgomery.B u₁ u₂ v₁ v₂ := by
    rw [← sDX, ← sNX]
    unfold addX addDen₁
    rw [← mul_assoc, div_mul_cancel₀ _ hd1]
  have hyR : addY P Q * DY E.toMontgomery.A E.toMontgomery.B u₁ u₂ v₁ v₂ =
      NY E.toMontgomery.A E.toMontgomery.B u₁ u₂ v₁ v₂ := by
    rw [← sDY, ← sNY]
    unfold addY addDen₂
    rw [← mul_assoc, div_mul_cancel₀ _ hd2]
  rw [hP, hQ]
  by_cases hu : u₁ = u₂
  · have hy : P.y = Q.y := by
      have : (P.y - Q.y) * (u₂ + 1) = 0 := by
        rw [hu] at hy₁
        linear_combination hy₁ - hy₂
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hu₂1)
    by_cases hv : v₁ = -v₂
    · -- `Q = -P`: the sum is `(0, 1)`.
      rw [MontgomeryModel.some_add_some_eq_zero h₁ h₂ hu hv, MontgomeryModel.zero_def]
      have hx : P.x = -Q.x := by
        have : (P.x + Q.x) * v₁ = 0 := by linear_combination hx₁ - hx₂ + Q.x * hv + hu
        exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_right hv₁0)
      apply toMontgomeryEquivAux_apply_of_y_eq_one
      change addY P Q = 1
      unfold addY addDen₂
      rw [div_eq_one_iff_eq hd2]
      have hPe := P.equation
      unfold Equation at hPe
      rw [hx] at hPe ⊢
      rw [← hy]
      linear_combination hPe
    · -- `Q = P`: the tangent formula.
      have hvv : v₁ = v₂ := by
        have : (v₁ - v₂) * (v₁ + v₂) = 0 := by
          apply mul_left_cancel₀ hB
          rw [hu] at h₁'
          linear_combination h₁' - h₂'
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd (eq_neg_of_add_eq_zero_left h) hv
      have hx : P.x = Q.x := by
        have : (P.x - Q.x) * v₁ = 0 := by linear_combination hx₁ - hx₂ - Q.x * hvv + hu
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hv₁0)
      have hPQ : P = Q := Point.ext hx hy
      subst hPQ hu hvv
      rw [MontgomeryModel.some_add_some_of_v_ne h₁ h₂ rfl hv]
      have he : 2 * E.toMontgomery.B * v₁ ≠ 0 := mul_ne_zero (mul_ne_zero h2 hB) hv₁0
      have hl : E.toMontgomery.tangentSlope u₁ v₁ * (2 * E.toMontgomery.B * v₁) =
          3 * u₁ ^ 2 + 2 * E.toMontgomery.A * u₁ + 1 :=
        div_mul_cancel₀ _ he
      have key := finish E.toMontgomery.A E.toMontgomery.B (addX P P) (addY P P) _ _ _ _ _ u₁ u₁
        v₁ _ _ _ _ hl rfl rfl he hDX hDY hyR hxR (G3 _ _ u₁ v₁ h₁') (G4 _ _ u₁ v₁ h₁')
      exact toMontgomeryEquivAux_eq_some _ key.1 key.2 _
  · -- `u₁ ≠ u₂`: the chord formula.
    rw [MontgomeryModel.some_add_some_of_u_ne h₁ h₂ hu]
    have he : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have hl : MontgomeryModel.chordSlope u₁ v₁ u₂ v₂ * (u₂ - u₁) = v₂ - v₁ :=
      div_mul_cancel₀ _ he
    have key := finish E.toMontgomery.A E.toMontgomery.B (addX P Q) (addY P Q) _ _ _ _ _ u₁ u₂
      v₁ _ _ _ _ hl rfl rfl he hDX hDY hyR hxR (G1 _ _ u₁ u₂ v₁ v₂ h₁' h₂')
      (G2 _ _ u₁ u₂ v₁ v₂ h₁' h₂')
    exact toMontgomeryEquivAux_eq_some _ key.1 key.2 _

/-- The sum formula is compatible with the bijection `φ`: `φ ⟨addX P Q, addY P Q, _⟩ = φ P + φ Q`.
-/
private theorem toMontgomeryEquivAux_add (P Q : E.Point) :
    E.toMontgomeryEquivAux ⟨addX P Q, addY P Q, equation_addX_addY P Q⟩ =
      E.toMontgomeryEquivAux P + E.toMontgomeryEquivAux Q := by
  by_cases hPx : P.x = 0
  · exact toMontgomeryEquivAux_add_of_x_eq_zero P Q hPx
  by_cases hQx : Q.x = 0
  · have hR : (⟨addX P Q, addY P Q, equation_addX_addY P Q⟩ : E.Point) =
        ⟨addX Q P, addY Q P, equation_addX_addY Q P⟩ :=
      Point.ext (addX_comm P Q) (addY_comm P Q)
    rw [hR, toMontgomeryEquivAux_add_of_x_eq_zero Q P hQx, add_comm]
  exact toMontgomeryEquivAux_add_of_x_ne_zero P Q hPx hQx

/-- **The group law in coordinates**: the sum of two points of a complete model is given by
the addition formula. -/
theorem add_eq_mk (P Q : E.Point) :
    P + Q = ⟨addX P Q, addY P Q, equation_addX_addY P Q⟩ := by
  rw [add_eq, ← toMontgomeryEquivAux_add, Equiv.symm_apply_apply]

end TwistedEdwardsModel.Proofs
