/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Square
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Square
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.curve_models

namespace «ProjectivePointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_spec (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold as_extended
  step as ⟨XZ, hXZ, hXZ_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZZ, hZZ, hZZ_lt⟩
  step as ⟨XY, hXY, hXY_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«x86_64-tables».toExtended_def,
      ProjectivePoint.«x86_64-tables».toProjective_def, Projective.toExtended,
      toField_mul_of_mod hXZ, toField_mul_of_mod hYZ, toField_sq_of_mod hZZ,
      toField_mul_of_mod hXY]
  · exact ⟨hXZ_lt, hYZ_lt, hZZ_lt, hXY_lt⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
      edwards.EdwardsPoint.«x86_64-tables».toPoint_def, hr,
      ProjectivePoint.«x86_64-tables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePointx86_64-tables»

namespace «ProjectivePointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_spec (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold as_extended
  step as ⟨XZ, hXZ, hXZ_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZZ, hZZ, hZZ_lt⟩
  step as ⟨XY, hXY, hXY_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«i686-tables».toExtended_def,
      ProjectivePoint.«i686-tables».toProjective_def, Projective.toExtended,
      toField_mul_of_mod hXZ, toField_mul_of_mod hYZ, toField_sq_of_mod hZZ,
      toField_mul_of_mod hXY]
  · exact ⟨hXZ_lt, hYZ_lt, hZZ_lt, hXY_lt⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-tables».toPoint_def, hr,
      ProjectivePoint.«i686-tables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePointi686-tables»

namespace «ProjectivePointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_spec (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold as_extended
  step as ⟨XZ, hXZ, hXZ_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZZ, hZZ, hZZ_lt⟩
  step as ⟨XY, hXY, hXY_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def,
      ProjectivePoint.«x86_64-no-tables».toProjective_def, Projective.toExtended,
      toField_mul_of_mod hXZ, toField_mul_of_mod hYZ, toField_sq_of_mod hZZ,
      toField_mul_of_mod hXY]
  · exact ⟨hXZ_lt, hYZ_lt, hZZ_lt, hXY_lt⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def, hr,
      ProjectivePoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePointx86_64-no-tables»

namespace «ProjectivePointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_spec (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold as_extended
  step as ⟨XZ, hXZ, hXZ_lt⟩
  step as ⟨YZ, hYZ, hYZ_lt⟩
  step as ⟨ZZ, hZZ, hZZ_lt⟩
  step as ⟨XY, hXY, hXY_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«i686-no-tables».toExtended_def,
      ProjectivePoint.«i686-no-tables».toProjective_def, Projective.toExtended,
      toField_mul_of_mod hXZ, toField_mul_of_mod hYZ, toField_sq_of_mod hZZ,
      toField_mul_of_mod hXY]
  · exact ⟨hXZ_lt, hYZ_lt, hZZ_lt, hXY_lt⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-no-tables».toPoint_def, hr,
      ProjectivePoint.«i686-no-tables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePointi686-no-tables»

end Curve25519Dalek.backend.serial.curve_models
