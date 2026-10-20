/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.curve_models

namespace «CompletedPointx86_64-tables»

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^52`. -/
@[step]
theorem as_projective_spec (self : CompletedPoint.«x86_64-tables») (hself : self.Bounded) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.Bounded ⦄ := by
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
theorem as_projective_spec_point (self : CompletedPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«x86_64-tables».onCurve_iff,
      ProjectivePoint.«x86_64-tables».toPoint_def, hr,
      CompletedPoint.«x86_64-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPointx86_64-tables»

namespace «CompletedPointx86_64-no-tables»

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^52`. -/
@[step]
theorem as_projective_spec (self : CompletedPoint.«x86_64-no-tables») (hself : self.Bounded) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-no-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.Bounded ⦄ := by
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
theorem as_projective_spec_point (self : CompletedPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«x86_64-no-tables».onCurve_iff,
      ProjectivePoint.«x86_64-no-tables».toPoint_def, hr,
      CompletedPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPointx86_64-no-tables»

end Curve25519Dalek.backend.serial.curve_models
