/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Backend.Serial.U64.Field.Zero
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.curve_models

namespace AffineNielsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for AffineNielsPoint`: `(1, 1, 0)`, limbs `< 2^54`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
      r.toAffineNiels = AffineNiels.identity ∧ r.Bounded ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«x86_64-tables».toAffineNiels_def, AffineNiels.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for AffineNielsPoint` represents the neutral element. -/
theorem identity_spec_point :
    identity ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.Bounded ⦄ :=
  spec_mono identity_spec fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«x86_64-tables».onCurve_iff,
      AffineNielsPoint.«x86_64-tables».toPoint_def, hr]
    exact ⟨AffineNiels.onCurve_identity two_ne_zero, AffineNiels.toPoint_identity, hb⟩

end AffineNielsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

namespace AffineNielsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for AffineNielsPoint`: `(1, 1, 0)`, limbs `< 2^54`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : AffineNielsPoint.«x86_64-no-tables») =>
      r.toAffineNiels = AffineNiels.identity ∧ r.Bounded ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«x86_64-no-tables».toAffineNiels_def, AffineNiels.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for AffineNielsPoint` represents the neutral element. -/
theorem identity_spec_point :
    identity ⦃ (r : AffineNielsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.Bounded ⦄ :=
  spec_mono identity_spec fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«x86_64-no-tables».onCurve_iff,
      AffineNielsPoint.«x86_64-no-tables».toPoint_def, hr]
    exact ⟨AffineNiels.onCurve_identity two_ne_zero, AffineNiels.toPoint_identity, hb⟩

end AffineNielsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

end Curve25519Dalek.backend.serial.curve_models
