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
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

namespace «Shared0EdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subProjectiveNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem sub_spec (self : edwards.EdwardsPoint.«x86_64-tables»)
    (other : ProjectiveNielsPoint.«x86_64-tables») (hself : self.Bounded)
    (hother : other.Bounded) :
    sub self other ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.toCompleted = self.toExtended.subProjectiveNiels other.toProjectiveNiels ∧
        r.Bounded ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  obtain ⟨hYpX, hYmX, hZo, hT2d⟩ := hother
  unfold sub
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨PM, hPM, hPM_lt⟩
  step as ⟨MP, hMP, hMP_lt⟩
  step as ⟨TT2d, hTT2d, hTT2d_lt⟩
  step as ⟨ZZ, hZZ, hZZ_lt⟩
  step as ⟨ZZ2, hZZ2⟩
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨Y', hY'⟩
  step as ⟨Z', hZ', hZ'_lt⟩
  step as ⟨T', hT'⟩
  refine ⟨?_, ?_⟩
  · simp only [CompletedPoint.«x86_64-tables».toCompleted_def,
      edwards.EdwardsPoint.«x86_64-tables».toExtended_def,
      ProjectiveNielsPoint.«x86_64-tables».toProjectiveNiels_def, Extended.subProjectiveNiels,
      toField_sub_of_mod hX', toField_add_of_limbs hY', toField_sub_of_mod hZ',
      toField_add_of_limbs hT', toField_mul_of_mod hPM, toField_mul_of_mod hMP,
      toField_mul_of_mod hTT2d, toField_mul_of_mod hZZ, toField_add_of_limbs hZZ2,
      toField_add_of_limbs hY_plus_X, toField_sub_of_mod hY_minus_X]
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt,
      limbs_lt_of_le (by decide) (limbs_add_lt hY' hPM_lt hMP_lt),
      limbs_lt_of_le (by decide) hZ'_lt,
      limbs_add_lt hT' (limbs_add_lt hZZ2 hZZ_lt hZZ_lt) (limbs_lt_of_le (by decide) hTT2d_lt)⟩

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec_point (self : edwards.EdwardsPoint.«x86_64-tables»)
    (other : ProjectiveNielsPoint.«x86_64-tables») (hself : self.Bounded)
    (hother : other.Bounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (sub_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-tables».onCurve_iff,
      CompletedPoint.«x86_64-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«x86_64-tables».toPoint_def,
      ProjectiveNielsPoint.«x86_64-tables».toPoint_def]
    exact ⟨Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
end «Shared0EdwardsPointx86_64-tables».Insts

namespace «Shared0EdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subProjectiveNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem sub_spec (self : edwards.EdwardsPoint.«x86_64-no-tables»)
    (other : ProjectiveNielsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hother : other.Bounded) :
    sub self other ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.toCompleted = self.toExtended.subProjectiveNiels other.toProjectiveNiels ∧
        r.Bounded ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  obtain ⟨hYpX, hYmX, hZo, hT2d⟩ := hother
  unfold sub
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨PM, hPM, hPM_lt⟩
  step as ⟨MP, hMP, hMP_lt⟩
  step as ⟨TT2d, hTT2d, hTT2d_lt⟩
  step as ⟨ZZ, hZZ, hZZ_lt⟩
  step as ⟨ZZ2, hZZ2⟩
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨Y', hY'⟩
  step as ⟨Z', hZ', hZ'_lt⟩
  step as ⟨T', hT'⟩
  refine ⟨?_, ?_⟩
  · simp only [CompletedPoint.«x86_64-no-tables».toCompleted_def,
      edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def,
      ProjectiveNielsPoint.«x86_64-no-tables».toProjectiveNiels_def, Extended.subProjectiveNiels,
      toField_sub_of_mod hX', toField_add_of_limbs hY', toField_sub_of_mod hZ',
      toField_add_of_limbs hT', toField_mul_of_mod hPM, toField_mul_of_mod hMP,
      toField_mul_of_mod hTT2d, toField_mul_of_mod hZZ, toField_add_of_limbs hZZ2,
      toField_add_of_limbs hY_plus_X, toField_sub_of_mod hY_minus_X]
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt,
      limbs_lt_of_le (by decide) (limbs_add_lt hY' hPM_lt hMP_lt),
      limbs_lt_of_le (by decide) hZ'_lt,
      limbs_add_lt hT' (limbs_add_lt hZZ2 hZZ_lt hZZ_lt) (limbs_lt_of_le (by decide) hTT2d_lt)⟩

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec_point (self : edwards.EdwardsPoint.«x86_64-no-tables»)
    (other : ProjectiveNielsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hother : other.Bounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (sub_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-no-tables».onCurve_iff,
      CompletedPoint.«x86_64-no-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def,
      ProjectiveNielsPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
end «Shared0EdwardsPointx86_64-no-tables».Insts

end Curve25519Dalek
