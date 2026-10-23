/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
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

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_spec (self : CompletedPoint.«x86_64-tables») (hself : self.LimbsLt 54) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_extended
  step as ⟨XT, hXT, hXT_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  step as ⟨XY, hXY, hXY_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«x86_64-tables».toExtended_def,
      CompletedPoint.«x86_64-tables».toCompleted_def, Completed.toExtended,
      toField_mul_of_mod hXT, toField_mul_of_mod hYZ, toField_mul_of_mod hZT,
      toField_mul_of_mod hXY]
  · exact ⟨hXT_lt, hYZ_lt, hZT_lt, hXY_lt⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : CompletedPoint.«x86_64-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
      edwards.EdwardsPoint.«x86_64-tables».toPoint_def, hr,
      CompletedPoint.«x86_64-tables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPointx86_64-tables»

namespace «CompletedPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_spec (self : CompletedPoint.«i686-tables») (hself : self.MulBounded) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_extended
  step as ⟨XT, hXT, hXT_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  step as ⟨XY, hXY, hXY_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«i686-tables».toExtended_def,
      CompletedPoint.«i686-tables».toCompleted_def, Completed.toExtended,
      toField_mul_of_mod hXT, toField_mul_of_mod hYZ, toField_mul_of_mod hZT,
      toField_mul_of_mod hXY]
  · exact ⟨hXT_lt, hYZ_lt, hZT_lt, hXY_lt⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : CompletedPoint.«i686-tables») (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-tables».toPoint_def, hr,
      CompletedPoint.«i686-tables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPointi686-tables»

namespace «CompletedPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_spec (self : CompletedPoint.«x86_64-no-tables») (hself : self.LimbsLt 54) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_extended
  step as ⟨XT, hXT, hXT_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  step as ⟨XY, hXY, hXY_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def,
      CompletedPoint.«x86_64-no-tables».toCompleted_def, Completed.toExtended,
      toField_mul_of_mod hXT, toField_mul_of_mod hYZ, toField_mul_of_mod hZT,
      toField_mul_of_mod hXY]
  · exact ⟨hXT_lt, hYZ_lt, hZT_lt, hXY_lt⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : CompletedPoint.«x86_64-no-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def, hr,
      CompletedPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPointx86_64-no-tables»

namespace «CompletedPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_spec (self : CompletedPoint.«i686-no-tables») (hself : self.MulBounded) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_extended
  step as ⟨XT, hXT, hXT_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  step as ⟨XY, hXY, hXY_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«i686-no-tables».toExtended_def,
      CompletedPoint.«i686-no-tables».toCompleted_def, Completed.toExtended,
      toField_mul_of_mod hXT, toField_mul_of_mod hYZ, toField_mul_of_mod hZT,
      toField_mul_of_mod hXY]
  · exact ⟨hXT_lt, hYZ_lt, hZT_lt, hXY_lt⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : CompletedPoint.«i686-no-tables») (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-no-tables».toPoint_def, hr,
      CompletedPoint.«i686-no-tables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPointi686-no-tables»

end Curve25519Dalek.backend.serial.curve_models
