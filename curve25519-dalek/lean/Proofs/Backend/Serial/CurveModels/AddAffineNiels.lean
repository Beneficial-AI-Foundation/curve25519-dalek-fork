/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Sub
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

namespace «Shared0EdwardsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»

/-- `Add<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.addAffineNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem add_spec (self : edwards.EdwardsPoint.«x86_64-tables»)
    (other : AffineNielsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) :
    add self other ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.toCompleted = self.toExtended.addAffineNiels other.toAffineNiels ∧
        r.LimbsLt 54 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  obtain ⟨hypx, hymx, hxy2d⟩ := hother
  unfold add
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨PP, hPP, hPP_lt⟩
  step as ⟨MM, hMM, hMM_lt⟩
  step as ⟨Txy2d, hTxy2d, hTxy2d_lt⟩
  step as ⟨Z2, hZ2⟩
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨Y', hY'⟩
  step as ⟨Z', hZ'⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [CompletedPoint.«x86_64-tables».toCompleted_def,
      edwards.EdwardsPoint.«x86_64-tables».toExtended_def,
      AffineNielsPoint.«x86_64-tables».toAffineNiels_def, Extended.addAffineNiels,
      toField_sub_of_mod hX', toField_add_of_limbs hY', toField_add_of_limbs hZ',
      toField_sub_of_mod hT', toField_mul_of_mod hPP, toField_mul_of_mod hMM,
      toField_mul_of_mod hTxy2d, toField_add_of_limbs hZ2, toField_add_of_limbs hY_plus_X,
      toField_sub_of_mod hY_minus_X]
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt,
      limbs_lt_of_le (by decide) (limbs_add_lt hY' hPP_lt hMM_lt),
      limbs_add_lt hZ' (limbs_add_lt hZ2 hZ hZ) (limbs_lt_of_le (by decide) hTxy2d_lt),
      limbs_lt_of_le (by decide) hT'_lt⟩

/-- `Add<&AffineNielsPoint> for &EdwardsPoint` adds the represented points. -/
theorem add_spec_point (self : edwards.EdwardsPoint.«x86_64-tables»)
    (other : AffineNielsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    add self other ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (add_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-tables».onCurve_iff,
      CompletedPoint.«x86_64-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«x86_64-tables».toPoint_def,
      AffineNielsPoint.«x86_64-tables».toPoint_def]
    exact ⟨Extended.addAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_addAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithAddSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»
end «Shared0EdwardsPointx86_64-tables».Insts

namespace «Shared0EdwardsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»

/-- `Add<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.addAffineNiels`; limbs `< 2^26` and `< 2^27` in, `< 3 · 2^26` out. -/
@[step]
theorem add_spec (self : edwards.EdwardsPoint.«i686-tables»)
    (other : AffineNielsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) :
    add self other ⦃ (r : CompletedPoint.«i686-tables») =>
      r.toCompleted = self.toExtended.addAffineNiels other.toAffineNiels ∧
        r.MulBounded ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  obtain ⟨hypx, hymx, hxy2d⟩ := hother
  unfold add
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨PP, hPP, hPP_lt⟩
  step as ⟨MM, hMM, hMM_lt⟩
  step as ⟨Txy2d, hTxy2d, hTxy2d_lt⟩
  step as ⟨Z2, hZ2⟩
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨Y', hY'⟩
  step as ⟨Z', hZ'⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [CompletedPoint.«i686-tables».toCompleted_def,
      edwards.EdwardsPoint.«i686-tables».toExtended_def,
      AffineNielsPoint.«i686-tables».toAffineNiels_def, Extended.addAffineNiels,
      toField_sub_of_mod hX', toField_add_of_limbs hY', toField_add_of_limbs hZ',
      toField_sub_of_mod hT', toField_mul_of_mod hPP, toField_mul_of_mod hMM,
      toField_mul_of_mod hTxy2d, toField_add_of_limbs hZ2, toField_add_of_limbs hY_plus_X,
      toField_sub_of_mod hY_minus_X]
  · exact ⟨mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hX'_lt),
      mulBounded_of_limbsLt (limbs_add_lt hY' hPP_lt hMM_lt),
      mulBounded_add hZ' (limbs_add_lt hZ2 hZ hZ) hTxy2d_lt,
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hT'_lt)⟩

/-- `Add<&AffineNielsPoint> for &EdwardsPoint` adds the represented points. -/
theorem add_spec_point (self : edwards.EdwardsPoint.«i686-tables»)
    (other : AffineNielsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    add self other ⦃ (r : CompletedPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (add_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«i686-tables».onCurve_iff,
      CompletedPoint.«i686-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«i686-tables».toPoint_def,
      AffineNielsPoint.«i686-tables».toPoint_def]
    exact ⟨Extended.addAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_addAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithAddSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
end «Shared0EdwardsPointi686-tables».Insts

namespace «Shared0EdwardsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddSharedAAffineNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»

/-- `Add<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.addAffineNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem add_spec (self : edwards.EdwardsPoint.«x86_64-no-tables»)
    (other : AffineNielsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) :
    add self other ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.toCompleted = self.toExtended.addAffineNiels other.toAffineNiels ∧
        r.LimbsLt 54 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  obtain ⟨hypx, hymx, hxy2d⟩ := hother
  unfold add
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨PP, hPP, hPP_lt⟩
  step as ⟨MM, hMM, hMM_lt⟩
  step as ⟨Txy2d, hTxy2d, hTxy2d_lt⟩
  step as ⟨Z2, hZ2⟩
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨Y', hY'⟩
  step as ⟨Z', hZ'⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [CompletedPoint.«x86_64-no-tables».toCompleted_def,
      edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def,
      AffineNielsPoint.«x86_64-no-tables».toAffineNiels_def, Extended.addAffineNiels,
      toField_sub_of_mod hX', toField_add_of_limbs hY', toField_add_of_limbs hZ',
      toField_sub_of_mod hT', toField_mul_of_mod hPP, toField_mul_of_mod hMM,
      toField_mul_of_mod hTxy2d, toField_add_of_limbs hZ2, toField_add_of_limbs hY_plus_X,
      toField_sub_of_mod hY_minus_X]
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt,
      limbs_lt_of_le (by decide) (limbs_add_lt hY' hPP_lt hMM_lt),
      limbs_add_lt hZ' (limbs_add_lt hZ2 hZ hZ) (limbs_lt_of_le (by decide) hTxy2d_lt),
      limbs_lt_of_le (by decide) hT'_lt⟩

/-- `Add<&AffineNielsPoint> for &EdwardsPoint` adds the represented points. -/
theorem add_spec_point (self : edwards.EdwardsPoint.«x86_64-no-tables»)
    (other : AffineNielsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    add self other ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (add_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-no-tables».onCurve_iff,
      CompletedPoint.«x86_64-no-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def,
      AffineNielsPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Extended.addAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_addAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithAddSharedAAffineNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
end «Shared0EdwardsPointx86_64-no-tables».Insts

namespace «Shared0EdwardsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddSharedAAffineNielsPointi686-no-tablesCompletedPointi686-no-tables»

/-- `Add<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.addAffineNiels`; limbs `< 2^26` and `< 2^27` in, `< 3 · 2^26` out. -/
@[step]
theorem add_spec (self : edwards.EdwardsPoint.«i686-no-tables»)
    (other : AffineNielsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) :
    add self other ⦃ (r : CompletedPoint.«i686-no-tables») =>
      r.toCompleted = self.toExtended.addAffineNiels other.toAffineNiels ∧
        r.MulBounded ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  obtain ⟨hypx, hymx, hxy2d⟩ := hother
  unfold add
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨PP, hPP, hPP_lt⟩
  step as ⟨MM, hMM, hMM_lt⟩
  step as ⟨Txy2d, hTxy2d, hTxy2d_lt⟩
  step as ⟨Z2, hZ2⟩
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨Y', hY'⟩
  step as ⟨Z', hZ'⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [CompletedPoint.«i686-no-tables».toCompleted_def,
      edwards.EdwardsPoint.«i686-no-tables».toExtended_def,
      AffineNielsPoint.«i686-no-tables».toAffineNiels_def, Extended.addAffineNiels,
      toField_sub_of_mod hX', toField_add_of_limbs hY', toField_add_of_limbs hZ',
      toField_sub_of_mod hT', toField_mul_of_mod hPP, toField_mul_of_mod hMM,
      toField_mul_of_mod hTxy2d, toField_add_of_limbs hZ2, toField_add_of_limbs hY_plus_X,
      toField_sub_of_mod hY_minus_X]
  · exact ⟨mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hX'_lt),
      mulBounded_of_limbsLt (limbs_add_lt hY' hPP_lt hMM_lt),
      mulBounded_add hZ' (limbs_add_lt hZ2 hZ hZ) hTxy2d_lt,
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hT'_lt)⟩

/-- `Add<&AffineNielsPoint> for &EdwardsPoint` adds the represented points. -/
theorem add_spec_point (self : edwards.EdwardsPoint.«i686-no-tables»)
    (other : AffineNielsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    add self other ⦃ (r : CompletedPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (add_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«i686-no-tables».onCurve_iff,
      CompletedPoint.«i686-no-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«i686-no-tables».toPoint_def,
      AffineNielsPoint.«i686-no-tables».toPoint_def]
    exact ⟨Extended.addAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_addAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithAddSharedAAffineNielsPointi686-no-tablesCompletedPointi686-no-tables»
end «Shared0EdwardsPointi686-no-tables».Insts

end Curve25519Dalek
