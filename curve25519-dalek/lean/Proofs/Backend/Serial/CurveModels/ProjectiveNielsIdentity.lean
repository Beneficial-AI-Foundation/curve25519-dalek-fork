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

namespace ProjectiveNielsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for ProjectiveNielsPoint`: `(1 : 1 : 1 : 0)`, limbs `< 2^54`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.Bounded ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«x86_64-tables».toProjectiveNiels_def,
      ProjectiveNiels.identity, toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for ProjectiveNielsPoint` represents the neutral element. -/
theorem identity_spec_point :
    identity ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.Bounded ⦄ :=
  spec_mono identity_spec fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«x86_64-tables».onCurve_iff,
      ProjectiveNielsPoint.«x86_64-tables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity two_ne_zero, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ProjectiveNielsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for ProjectiveNielsPoint`: `(1 : 1 : 1 : 0)`, limbs `< 2^54`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.Bounded ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«x86_64-no-tables».toProjectiveNiels_def,
      ProjectiveNiels.identity, toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for ProjectiveNielsPoint` represents the neutral element. -/
theorem identity_spec_point :
    identity ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.Bounded ⦄ :=
  spec_mono identity_spec fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«x86_64-no-tables».onCurve_iff,
      ProjectiveNielsPoint.«x86_64-no-tables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity two_ne_zero, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

end Curve25519Dalek.backend.serial.curve_models
