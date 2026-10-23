/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U64.Constants.EdwardsD
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Field.Eq
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Constants.EdwardsD
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Square
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.curve_models

namespace ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsValidityCheck

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ValidityCheck for ProjectivePoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` (it does not check `Z ≠ 0`); limbs `< 2^52`. -/
@[step]
theorem is_valid_spec (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold is_valid
  step as ⟨XX, hXX, hXX_lt⟩
  step as ⟨YY, hYY, hYY_lt⟩
  step as ⟨ZZ, hZZ, hZZ_lt⟩
  step as ⟨ZZZZ, hZZZZ, hZZZZ_lt⟩
  step as ⟨YY_minus_XX, hYY_minus_XX, hYY_minus_XX_lt⟩
  step as ⟨lhs, hlhs, hlhs_lt⟩
  step as ⟨D, hD, hD_lt⟩
  step as ⟨XXYY, hXXYY, hXXYY_lt⟩
  step as ⟨DXXYY, hDXXYY, hDXXYY_lt⟩
  step as ⟨rhs, hrhs⟩
  step as ⟨b, hb⟩
  rw [hb, ← toField_eq_toField_iff, toField_mul_of_mod hlhs, toField_add_of_limbs hrhs,
    toField_sub_of_mod hYY_minus_XX, toField_mul_of_mod hDXXYY, toField_mul_of_mod hXXYY,
    toField_sq_of_mod hZZZZ, toField_sq_of_mod hZZ, toField_sq_of_mod hXX, toField_sq_of_mod hYY,
    toField_eq_d_of_asNat hD]
  constructor <;> intro h <;> linear_combination h

/-- `ValidityCheck for ProjectivePoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, ProjectivePoint.«x86_64-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor <;> intro h <;> linear_combination h

end ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsValidityCheck

namespace ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsValidityCheck

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ValidityCheck for ProjectivePoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` (it does not check `Z ≠ 0`); limbs `< 2^26`. -/
@[step]
theorem is_valid_spec (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold is_valid
  step as ⟨XX, hXX, hXX_lt⟩
  step as ⟨YY, hYY, hYY_lt⟩
  step as ⟨ZZ, hZZ, hZZ_lt⟩
  step as ⟨ZZZZ, hZZZZ, hZZZZ_lt⟩
  step as ⟨YY_minus_XX, hYY_minus_XX, hYY_minus_XX_lt⟩
  step as ⟨lhs, hlhs, hlhs_lt⟩
  step as ⟨D, hD, hD_lt⟩
  step as ⟨XXYY, hXXYY, hXXYY_lt⟩
  step as ⟨DXXYY, hDXXYY, hDXXYY_lt⟩
  step as ⟨rhs, hrhs⟩
  step as ⟨b, hb⟩
  rw [hb, ← toField_eq_toField_iff, toField_mul_of_mod hlhs, toField_add_of_limbs hrhs,
    toField_sub_of_mod hYY_minus_XX, toField_mul_of_mod hDXXYY, toField_mul_of_mod hXXYY,
    toField_sq_of_mod hZZZZ, toField_sq_of_mod hZZ, toField_sq_of_mod hXX, toField_sq_of_mod hYY,
    toField_eq_d_of_asNat hD]
  constructor <;> intro h <;> linear_combination h

/-- `ValidityCheck for ProjectivePoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, ProjectivePoint.«i686-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor <;> intro h <;> linear_combination h

end ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsValidityCheck

namespace ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ValidityCheck for ProjectivePoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` (it does not check `Z ≠ 0`); limbs `< 2^52`. -/
@[step]
theorem is_valid_spec (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold is_valid
  step as ⟨XX, hXX, hXX_lt⟩
  step as ⟨YY, hYY, hYY_lt⟩
  step as ⟨ZZ, hZZ, hZZ_lt⟩
  step as ⟨ZZZZ, hZZZZ, hZZZZ_lt⟩
  step as ⟨YY_minus_XX, hYY_minus_XX, hYY_minus_XX_lt⟩
  step as ⟨lhs, hlhs, hlhs_lt⟩
  step as ⟨D, hD, hD_lt⟩
  step as ⟨XXYY, hXXYY, hXXYY_lt⟩
  step as ⟨DXXYY, hDXXYY, hDXXYY_lt⟩
  step as ⟨rhs, hrhs⟩
  step as ⟨b, hb⟩
  rw [hb, ← toField_eq_toField_iff, toField_mul_of_mod hlhs, toField_add_of_limbs hrhs,
    toField_sub_of_mod hYY_minus_XX, toField_mul_of_mod hDXXYY, toField_mul_of_mod hXXYY,
    toField_sq_of_mod hZZZZ, toField_sq_of_mod hZZ, toField_sq_of_mod hXX, toField_sq_of_mod hYY,
    toField_eq_d_of_asNat hD]
  constructor <;> intro h <;> linear_combination h

/-- `ValidityCheck for ProjectivePoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, ProjectivePoint.«x86_64-no-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor <;> intro h <;> linear_combination h

end ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

namespace ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ValidityCheck for ProjectivePoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` (it does not check `Z ≠ 0`); limbs `< 2^26`. -/
@[step]
theorem is_valid_spec (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ⦄ := by
  obtain ⟨hX, hY, hZ⟩ := hself
  unfold is_valid
  step as ⟨XX, hXX, hXX_lt⟩
  step as ⟨YY, hYY, hYY_lt⟩
  step as ⟨ZZ, hZZ, hZZ_lt⟩
  step as ⟨ZZZZ, hZZZZ, hZZZZ_lt⟩
  step as ⟨YY_minus_XX, hYY_minus_XX, hYY_minus_XX_lt⟩
  step as ⟨lhs, hlhs, hlhs_lt⟩
  step as ⟨D, hD, hD_lt⟩
  step as ⟨XXYY, hXXYY, hXXYY_lt⟩
  step as ⟨DXXYY, hDXXYY, hDXXYY_lt⟩
  step as ⟨rhs, hrhs⟩
  step as ⟨b, hb⟩
  rw [hb, ← toField_eq_toField_iff, toField_mul_of_mod hlhs, toField_add_of_limbs hrhs,
    toField_sub_of_mod hYY_minus_XX, toField_mul_of_mod hDXXYY, toField_mul_of_mod hXXYY,
    toField_sq_of_mod hZZZZ, toField_sq_of_mod hZZ, toField_sq_of_mod hXX, toField_sq_of_mod hYY,
    toField_eq_d_of_asNat hD]
  constructor <;> intro h <;> linear_combination h

/-- `ValidityCheck for ProjectivePoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, ProjectivePoint.«i686-no-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor <;> intro h <;> linear_combination h

end ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

end Curve25519Dalek.backend.serial.curve_models
