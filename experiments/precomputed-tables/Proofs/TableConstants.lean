/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.CurveModels
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
public section

/-! # Table entries with known coordinates

The precomputed tables of `backend/serial/u64/constants.rs` store Niels forms of points whose
affine coordinates `(x, y)` are certified in `Curve25519.Proofs.Edwards.OddMultiples` and
`Curve25519.Proofs.Edwards.BasepointTable`. An affine Niels entry represents the point `(x, y)`
when its limbs' values are `y + x`, `y - x` and `2 d x y` modulo `p`; a projective Niels entry
with `Z ≠ 0` when they are `Z (y + x)`, `Z (y - x)` and `2 d Z x y`. The congruences are on
natural numbers, so that the constant proofs decide them by kernel computation, with `p` and `d`
as numerals. -/

open Aeneas Aeneas.Std curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.curve_models

/-- `d` as a natural number below `p` (`d_eq_natCast`). -/
abbrev dNat : ℕ := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- An affine Niels entry with limbs `y + x`, `y - x`, `2 d x y` (modulo `p`) represents the point
with coordinates `(x, y)`. -/
theorem AffineNielsPoint.«x86_64-tables».onCurve_toPoint_of_coords
    {e : AffineNielsPoint.«x86_64-tables»} {P : edwards.Point} {x y : ℕ}
    (hx : P.x = x) (hy : P.y = y) (ha : e.y_plus_x.asNat % p = (y + x) % p)
    (hb : (e.y_minus_x.asNat + x) % p = y % p)
    (hc : e.xy2d.asNat % p = 2 * dNat * x * y % p) :
    e.OnCurve ∧ e.toPoint = P := by
  have ha' : e.y_plus_x.toField = (y : ZMod p) + x := by
    rw [toField_def, natCast_eq_natCast_of_mod_eq ha, Nat.cast_add]
  have hb' : e.y_minus_x.toField = (y : ZMod p) - x := by
    have := natCast_eq_natCast_of_mod_eq hb
    push_cast at this
    rw [toField_def, ← this, add_sub_cancel_right]
  have hc' : e.xy2d.toField = 2 * d * x * y := by
    rw [toField_def, natCast_eq_natCast_of_mod_eq hc, d_eq_natCast]
    push_cast
    rfl
  have hX : e.toAffineNiels.x = x := by
    rw [AffineNielsPoint.«x86_64-tables».toAffineNiels_x, ha', hb']
    field_simp [two_ne_zero]
    ring
  have hY : e.toAffineNiels.y = y := by
    rw [AffineNielsPoint.«x86_64-tables».toAffineNiels_y, ha', hb']
    field_simp [two_ne_zero]
    ring
  have hon : e.OnCurve := by
    rw [AffineNielsPoint.«x86_64-tables».onCurve_iff_equation, hX, hY, hc', ← hx, ← hy]
    exact ⟨P.equation, rfl⟩
  refine ⟨hon, Point.ext ?_ ?_⟩
  · rw [AffineNielsPoint.«x86_64-tables».toPoint_x hon, hX, hx]
  · rw [AffineNielsPoint.«x86_64-tables».toPoint_y hon, hY, hy]

/-- A projective Niels entry with `Z ≠ 0` and limbs `Z (y + x)`, `Z (y - x)`, `2 d Z x y` (modulo
`p`) represents the point with coordinates `(x, y)`. -/
theorem ProjectiveNielsPoint.«x86_64-tables».onCurve_toPoint_of_coords
    {e : ProjectiveNielsPoint.«x86_64-tables»} {P : edwards.Point} {x y : ℕ}
    (hx : P.x = x) (hy : P.y = y) (hz : e.Z.asNat % p ≠ 0)
    (ha : e.Y_plus_X.asNat % p = e.Z.asNat * (y + x) % p)
    (hb : (e.Y_minus_X.asNat + e.Z.asNat * x) % p = e.Z.asNat * y % p)
    (hc : e.T2d.asNat % p = 2 * dNat * e.Z.asNat * x * y % p) :
    e.OnCurve ∧ e.toPoint = P := by
  have hz' : e.Z.toField ≠ 0 := toField_ne_zero_iff.mpr hz
  have ha' : e.Y_plus_X.toField = e.Z.toField * (y + x) := by
    have := natCast_eq_natCast_of_mod_eq ha
    push_cast at this
    rw [toField_def, toField_def, this]
  have hb' : e.Y_minus_X.toField = e.Z.toField * (y - x) := by
    have := natCast_eq_natCast_of_mod_eq hb
    push_cast at this
    rw [toField_def, toField_def, mul_sub, ← this, add_sub_cancel_right]
  have hc' : e.T2d.toField = 2 * d * e.Z.toField * x * y := by
    rw [toField_def, toField_def, natCast_eq_natCast_of_mod_eq hc, d_eq_natCast]
    push_cast
    rfl
  have hX : e.toProjectiveNiels.X = e.Z.toField * x := by
    rw [ProjectiveNielsPoint.«x86_64-tables».toProjectiveNiels_X, ha', hb']
    field_simp [two_ne_zero]
    ring
  have hY : e.toProjectiveNiels.Y = e.Z.toField * y := by
    rw [ProjectiveNielsPoint.«x86_64-tables».toProjectiveNiels_Y, ha', hb']
    field_simp [two_ne_zero]
    ring
  have hx' : e.toProjectiveNiels.X / e.Z.toField = x := by
    rw [hX, mul_div_cancel_left₀ _ hz']
  have hy' : e.toProjectiveNiels.Y / e.Z.toField = y := by
    rw [hY, mul_div_cancel_left₀ _ hz']
  have hon : e.OnCurve := by
    rw [ProjectiveNielsPoint.«x86_64-tables».onCurve_iff_equation, hx', hy', hc', hX, hY, ← hx,
      ← hy]
    exact ⟨hz', P.equation, by ring⟩
  refine ⟨hon, Point.ext ?_ ?_⟩
  · rw [ProjectiveNielsPoint.«x86_64-tables».toPoint_x hon, hx', hx]
  · rw [ProjectiveNielsPoint.«x86_64-tables».toPoint_y hon, hy', hy]

end Curve25519Dalek.backend.serial.curve_models
