/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
import Proofs.Backend.Serial.U64.Field.Mul
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.curve_models

namespace «CompletedPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^52`. -/
@[step]
theorem as_projective_spec (self : CompletedPoint.«x86_64-tables») (hself : self.LimbsLt 54) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step as ⟨XT, hXT, hXT_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectivePoint.«x86_64-tables».toProjective_def,
      CompletedPoint.«x86_64-tables».toCompleted_def, Completed.toProjective,
      toField_mul_of_mod hXT, toField_mul_of_mod hYZ, toField_mul_of_mod hZT]
  · exact ⟨hXT_lt, hYZ_lt, hZT_lt⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : CompletedPoint.«x86_64-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«x86_64-tables».onCurve_iff,
      ProjectivePoint.«x86_64-tables».toPoint_def, hr,
      CompletedPoint.«x86_64-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPointx86_64-tables»

namespace «CompletedPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^26`. -/
@[step]
theorem as_projective_spec (self : CompletedPoint.«i686-tables») (hself : self.MulBounded) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step as ⟨XT, hXT, hXT_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectivePoint.«i686-tables».toProjective_def,
      CompletedPoint.«i686-tables».toCompleted_def, Completed.toProjective,
      toField_mul_of_mod hXT, toField_mul_of_mod hYZ, toField_mul_of_mod hZT]
  · exact ⟨hXT_lt, hYZ_lt, hZT_lt⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : CompletedPoint.«i686-tables») (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«i686-tables».onCurve_iff,
      ProjectivePoint.«i686-tables».toPoint_def, hr,
      CompletedPoint.«i686-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPointi686-tables»

namespace «CompletedPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^52`. -/
@[step]
theorem as_projective_spec (self : CompletedPoint.«x86_64-no-tables») (hself : self.LimbsLt 54) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-no-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step as ⟨XT, hXT, hXT_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectivePoint.«x86_64-no-tables».toProjective_def,
      CompletedPoint.«x86_64-no-tables».toCompleted_def, Completed.toProjective,
      toField_mul_of_mod hXT, toField_mul_of_mod hYZ, toField_mul_of_mod hZT]
  · exact ⟨hXT_lt, hYZ_lt, hZT_lt⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : CompletedPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«x86_64-no-tables».onCurve_iff,
      ProjectivePoint.«x86_64-no-tables».toPoint_def, hr,
      CompletedPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPointx86_64-no-tables»

namespace «CompletedPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^26`. -/
@[step]
theorem as_projective_spec (self : CompletedPoint.«i686-no-tables») (hself : self.MulBounded) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-no-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step as ⟨XT, hXT, hXT_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectivePoint.«i686-no-tables».toProjective_def,
      CompletedPoint.«i686-no-tables».toCompleted_def, Completed.toProjective,
      toField_mul_of_mod hXT, toField_mul_of_mod hYZ, toField_mul_of_mod hZT]
  · exact ⟨hXT_lt, hYZ_lt, hZT_lt⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : CompletedPoint.«i686-no-tables»)
    (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«i686-no-tables».onCurve_iff,
      ProjectivePoint.«i686-no-tables».toPoint_def, hr,
      CompletedPoint.«i686-no-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPointi686-no-tables»

end Curve25519Dalek.backend.serial.curve_models
