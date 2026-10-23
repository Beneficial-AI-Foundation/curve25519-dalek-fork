/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Square2
import Proofs.Backend.Serial.U64.Field.Sub
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.Square
import Proofs.Backend.Serial.U32.Field.Square2
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.curve_models

namespace «ProjectivePointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ProjectivePoint::double`: the "dbl-2008-bbjlp" formula `Projective.double`; limbs `< 2^52`
in, `< 2^54` out. -/
@[step]
theorem double_spec (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    double self ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.toCompleted = self.toProjective.double ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold double
  step as ⟨XX, hXX, hXX_lt⟩
  step as ⟨YY, hYY, hYY_lt⟩
  step as ⟨ZZ2, hZZ2, hZZ2_lt⟩
  step as ⟨X_plus_Y, hX_plus_Y⟩
  step as ⟨X_plus_Y_sq, hX_plus_Y_sq, hX_plus_Y_sq_lt⟩
  step as ⟨YY_plus_XX, hYY_plus_XX⟩
  step as ⟨YY_minus_XX, hYY_minus_XX, hYY_minus_XX_lt⟩
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [CompletedPoint.«x86_64-tables».toCompleted_def,
      ProjectivePoint.«x86_64-tables».toProjective_def, Projective.double,
      toField_sub_of_mod hX', toField_sq_of_mod hX_plus_Y_sq, toField_add_of_limbs hX_plus_Y,
      toField_add_of_limbs hYY_plus_XX, toField_sub_of_mod hYY_minus_XX,
      toField_sub_of_mod hT', toField_two_mul_sq_of_mod hZZ2, toField_sq_of_mod hXX,
      toField_sq_of_mod hYY]
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt,
      limbs_lt_of_le (by decide) (limbs_add_lt hYY_plus_XX hYY_lt hXX_lt),
      limbs_lt_of_le (by decide) hYY_minus_XX_lt, limbs_lt_of_le (by decide) hT'_lt⟩

/-- `ProjectivePoint::double` doubles the represented point. -/
theorem double_spec_point (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    double self ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (double_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-tables».onCurve_iff,
      CompletedPoint.«x86_64-tables».toPoint_def, hr,
      ProjectivePoint.«x86_64-tables».toPoint_def]
    exact ⟨Projective.double_onCurve edwards_a_eq_neg_one hon,
      Projective.toPoint_double edwards_a_eq_neg_one hon, hb⟩

end «ProjectivePointx86_64-tables»

namespace «ProjectivePointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ProjectivePoint::double`: the "dbl-2008-bbjlp" formula `Projective.double`; limbs `< 2^26`
in, `< 3 · 2^26` out. -/
@[step]
theorem double_spec (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26) :
    double self ⦃ (r : CompletedPoint.«i686-tables») =>
      r.toCompleted = self.toProjective.double ∧ r.MulBounded ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold double
  step as ⟨XX, hXX, hXX_lt⟩
  step as ⟨YY, hYY, hYY_lt⟩
  step as ⟨ZZ2, hZZ2, hZZ2_lt⟩
  step as ⟨X_plus_Y, hX_plus_Y⟩
  step as ⟨X_plus_Y_sq, hX_plus_Y_sq, hX_plus_Y_sq_lt⟩
  step as ⟨YY_plus_XX, hYY_plus_XX⟩
  step as ⟨YY_minus_XX, hYY_minus_XX, hYY_minus_XX_lt⟩
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [CompletedPoint.«i686-tables».toCompleted_def,
      ProjectivePoint.«i686-tables».toProjective_def, Projective.double,
      toField_sub_of_mod hX', toField_sq_of_mod hX_plus_Y_sq, toField_add_of_limbs hX_plus_Y,
      toField_add_of_limbs hYY_plus_XX, toField_sub_of_mod hYY_minus_XX,
      toField_sub_of_mod hT', toField_two_mul_sq_of_mod hZZ2, toField_sq_of_mod hXX,
      toField_sq_of_mod hYY]
  · exact ⟨mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hX'_lt),
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) (limbs_add_lt hYY_plus_XX hYY_lt hXX_lt)),
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hYY_minus_XX_lt),
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hT'_lt)⟩

/-- `ProjectivePoint::double` doubles the represented point. -/
theorem double_spec_point (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    double self ⦃ (r : CompletedPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (double_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«i686-tables».onCurve_iff,
      CompletedPoint.«i686-tables».toPoint_def, hr,
      ProjectivePoint.«i686-tables».toPoint_def]
    exact ⟨Projective.double_onCurve edwards_a_eq_neg_one hon,
      Projective.toPoint_double edwards_a_eq_neg_one hon, hb⟩

end «ProjectivePointi686-tables»

namespace «ProjectivePointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ProjectivePoint::double`: the "dbl-2008-bbjlp" formula `Projective.double`; limbs `< 2^52`
in, `< 2^54` out. -/
@[step]
theorem double_spec (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    double self ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.toCompleted = self.toProjective.double ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold double
  step as ⟨XX, hXX, hXX_lt⟩
  step as ⟨YY, hYY, hYY_lt⟩
  step as ⟨ZZ2, hZZ2, hZZ2_lt⟩
  step as ⟨X_plus_Y, hX_plus_Y⟩
  step as ⟨X_plus_Y_sq, hX_plus_Y_sq, hX_plus_Y_sq_lt⟩
  step as ⟨YY_plus_XX, hYY_plus_XX⟩
  step as ⟨YY_minus_XX, hYY_minus_XX, hYY_minus_XX_lt⟩
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [CompletedPoint.«x86_64-no-tables».toCompleted_def,
      ProjectivePoint.«x86_64-no-tables».toProjective_def, Projective.double,
      toField_sub_of_mod hX', toField_sq_of_mod hX_plus_Y_sq, toField_add_of_limbs hX_plus_Y,
      toField_add_of_limbs hYY_plus_XX, toField_sub_of_mod hYY_minus_XX,
      toField_sub_of_mod hT', toField_two_mul_sq_of_mod hZZ2, toField_sq_of_mod hXX,
      toField_sq_of_mod hYY]
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt,
      limbs_lt_of_le (by decide) (limbs_add_lt hYY_plus_XX hYY_lt hXX_lt),
      limbs_lt_of_le (by decide) hYY_minus_XX_lt, limbs_lt_of_le (by decide) hT'_lt⟩

/-- `ProjectivePoint::double` doubles the represented point. -/
theorem double_spec_point (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    double self ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (double_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-no-tables».onCurve_iff,
      CompletedPoint.«x86_64-no-tables».toPoint_def, hr,
      ProjectivePoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Projective.double_onCurve edwards_a_eq_neg_one hon,
      Projective.toPoint_double edwards_a_eq_neg_one hon, hb⟩

end «ProjectivePointx86_64-no-tables»

namespace «ProjectivePointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ProjectivePoint::double`: the "dbl-2008-bbjlp" formula `Projective.double`; limbs `< 2^26`
in, `< 3 · 2^26` out. -/
@[step]
theorem double_spec (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    double self ⦃ (r : CompletedPoint.«i686-no-tables») =>
      r.toCompleted = self.toProjective.double ∧ r.MulBounded ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold double
  step as ⟨XX, hXX, hXX_lt⟩
  step as ⟨YY, hYY, hYY_lt⟩
  step as ⟨ZZ2, hZZ2, hZZ2_lt⟩
  step as ⟨X_plus_Y, hX_plus_Y⟩
  step as ⟨X_plus_Y_sq, hX_plus_Y_sq, hX_plus_Y_sq_lt⟩
  step as ⟨YY_plus_XX, hYY_plus_XX⟩
  step as ⟨YY_minus_XX, hYY_minus_XX, hYY_minus_XX_lt⟩
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [CompletedPoint.«i686-no-tables».toCompleted_def,
      ProjectivePoint.«i686-no-tables».toProjective_def, Projective.double,
      toField_sub_of_mod hX', toField_sq_of_mod hX_plus_Y_sq, toField_add_of_limbs hX_plus_Y,
      toField_add_of_limbs hYY_plus_XX, toField_sub_of_mod hYY_minus_XX,
      toField_sub_of_mod hT', toField_two_mul_sq_of_mod hZZ2, toField_sq_of_mod hXX,
      toField_sq_of_mod hYY]
  · exact ⟨mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hX'_lt),
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) (limbs_add_lt hYY_plus_XX hYY_lt hXX_lt)),
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hYY_minus_XX_lt),
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hT'_lt)⟩

/-- `ProjectivePoint::double` doubles the represented point. -/
theorem double_spec_point (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    double self ⦃ (r : CompletedPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (double_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«i686-no-tables».onCurve_iff,
      CompletedPoint.«i686-no-tables».toPoint_def, hr,
      ProjectivePoint.«i686-no-tables».toPoint_def]
    exact ⟨Projective.double_onCurve edwards_a_eq_neg_one hon,
      Projective.toPoint_double edwards_a_eq_neg_one hon, hb⟩

end «ProjectivePointi686-no-tables»

end Curve25519Dalek.backend.serial.curve_models
