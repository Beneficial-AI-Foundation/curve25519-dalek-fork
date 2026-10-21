/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Field.Invert
import Proofs.Helpers.ToField
public section

/-! # `ProjectivePoint::as_affine` (Montgomery) -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek

namespace montgomery.«ProjectivePointx86_64-tables»

/-- `ProjectivePoint::as_affine`: the canonical encoding of `U / W` (`0` at infinity). -/
@[step]
theorem as_affine_spec (self : montgomery.ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 54)
    :
    as_affine self ⦃ (r : montgomery.MontgomeryPoint) => r.asNat = encodeU self.toXZ.toU ⦄ := by
  obtain ⟨hU, hW⟩ := hself
  unfold as_affine
  step as ⟨w, hw1, hw0, hw_lt⟩
  step as ⟨u, hu, hu_lt⟩
  step as ⟨r, hr⟩
  rw [montgomery.MontgomeryPoint.asNat_def, hr, ← toField_val, toField_mul_of_mod hu,
    toField_inv_of_mod hw1 hw0, montgomery.ProjectivePoint.«x86_64-tables».toXZ_def,
    MontgomeryModel.XZ.toU, div_eq_mul_inv, encodeU]

end montgomery.«ProjectivePointx86_64-tables»

namespace montgomery.«ProjectivePointx86_64-no-tables»

/-- `ProjectivePoint::as_affine`: the canonical encoding of `U / W` (`0` at infinity). -/
@[step]
theorem as_affine_spec (self : montgomery.ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt
    54) :
    as_affine self ⦃ (r : montgomery.MontgomeryPoint) => r.asNat = encodeU self.toXZ.toU ⦄ := by
  obtain ⟨hU, hW⟩ := hself
  unfold as_affine
  step as ⟨w, hw1, hw0, hw_lt⟩
  step as ⟨u, hu, hu_lt⟩
  step as ⟨r, hr⟩
  rw [montgomery.MontgomeryPoint.asNat_def, hr, ← toField_val, toField_mul_of_mod hu,
    toField_inv_of_mod hw1 hw0, montgomery.ProjectivePoint.«x86_64-no-tables».toXZ_def,
    MontgomeryModel.XZ.toU, div_eq_mul_inv, encodeU]

end montgomery.«ProjectivePointx86_64-no-tables»

end Curve25519Dalek
