/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Constants.EdwardsD2
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Field.Invert
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::as_affine_niels`: `(y + x, y - x, x y (2 d))` with `x = X Z⁻¹`, `y = Y Z⁻¹`
(`0⁻¹ = 0`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem as_affine_niels_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
      r.toAffineNiels = self.toExtended.toAffineNiels ∧ r.Bounded ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_affine_niels
  step as ⟨recip, hrecip1, hrecip0, hrecip_lt⟩
  step as ⟨x, hx, hx_lt⟩
  step as ⟨y, hy, hy_lt⟩
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨D2, hD2, hD2_lt⟩
  step as ⟨xy2d, hxy2d, hxy2d_lt⟩
  step as ⟨y_plus_x, hy_plus_x⟩
  step as ⟨y_minus_x, hy_minus_x, hy_minus_x_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«x86_64-tables».toAffineNiels_def,
      EdwardsPoint.«x86_64-tables».toExtended_def, Extended.toAffineNiels,
      toField_add_of_limbs hy_plus_x, toField_sub_of_mod hy_minus_x, toField_mul_of_mod hxy2d,
      toField_mul_of_mod hxy, toField_mul_of_mod hx, toField_mul_of_mod hy,
      toField_inv_of_mod hrecip1 hrecip0, toField_eq_two_mul_d_of_asNat hD2, edwards_d]
  · exact ⟨limbs_lt_of_le (by decide) (limbs_add_lt hy_plus_x hy_lt hx_lt),
      limbs_lt_of_le (by decide) hy_minus_x_lt, limbs_lt_of_le (by decide) hxy2d_lt⟩

/-- `EdwardsPoint::as_affine_niels` represents the same point. -/
theorem as_affine_niels_spec_point (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (as_affine_niels_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«x86_64-tables».onCurve_iff,
      AffineNielsPoint.«x86_64-tables».toPoint_def, hr,
      EdwardsPoint.«x86_64-tables».toPoint_def]
    exact ⟨Extended.onCurve_toAffineNiels two_ne_zero hon,
      Extended.toPoint_toAffineNiels hon, hb⟩

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::as_affine_niels`: `(y + x, y - x, x y (2 d))` with `x = X Z⁻¹`, `y = Y Z⁻¹`
(`0⁻¹ = 0`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem as_affine_niels_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«x86_64-no-tables») =>
      r.toAffineNiels = self.toExtended.toAffineNiels ∧ r.Bounded ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_affine_niels
  step as ⟨recip, hrecip1, hrecip0, hrecip_lt⟩
  step as ⟨x, hx, hx_lt⟩
  step as ⟨y, hy, hy_lt⟩
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨D2, hD2, hD2_lt⟩
  step as ⟨xy2d, hxy2d, hxy2d_lt⟩
  step as ⟨y_plus_x, hy_plus_x⟩
  step as ⟨y_minus_x, hy_minus_x, hy_minus_x_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«x86_64-no-tables».toAffineNiels_def,
      EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.toAffineNiels,
      toField_add_of_limbs hy_plus_x, toField_sub_of_mod hy_minus_x, toField_mul_of_mod hxy2d,
      toField_mul_of_mod hxy, toField_mul_of_mod hx, toField_mul_of_mod hy,
      toField_inv_of_mod hrecip1 hrecip0, toField_eq_two_mul_d_of_asNat hD2, edwards_d]
  · exact ⟨limbs_lt_of_le (by decide) (limbs_add_lt hy_plus_x hy_lt hx_lt),
      limbs_lt_of_le (by decide) hy_minus_x_lt, limbs_lt_of_le (by decide) hxy2d_lt⟩

/-- `EdwardsPoint::as_affine_niels` represents the same point. -/
theorem as_affine_niels_spec_point (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (as_affine_niels_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«x86_64-no-tables».onCurve_iff,
      AffineNielsPoint.«x86_64-no-tables».toPoint_def, hr,
      EdwardsPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Extended.onCurve_toAffineNiels two_ne_zero hon,
      Extended.toPoint_toAffineNiels hon, hb⟩

end «EdwardsPointx86_64-no-tables»

end Curve25519Dalek.edwards
