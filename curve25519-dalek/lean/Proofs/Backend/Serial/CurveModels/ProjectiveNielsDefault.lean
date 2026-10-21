/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
import Proofs.Backend.Serial.CurveModels.ProjectiveNielsIdentity
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.curve_models

namespace ProjectiveNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault

/-- `Default for ProjectiveNielsPoint`: the identity `(1 : 1 : 1 : 0)`, limbs `< 2^54`. -/
@[step]
theorem default_spec :
    default ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.LimbsLt 54 ⦄ := by
  unfold default
  step*

/-- `Default for ProjectiveNielsPoint` represents the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 54 ⦄ :=
  spec_mono default_spec fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«x86_64-tables».onCurve_iff,
      ProjectiveNielsPoint.«x86_64-tables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity two_ne_zero, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault

namespace ProjectiveNielsPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

/-- `Default for ProjectiveNielsPoint`: the identity `(1 : 1 : 1 : 0)`, limbs `< 2^54`. -/
@[step]
theorem default_spec :
    default ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.LimbsLt 54 ⦄ := by
  unfold default
  step*

/-- `Default for ProjectiveNielsPoint` represents the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 54 ⦄ :=
  spec_mono default_spec fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«x86_64-no-tables».onCurve_iff,
      ProjectiveNielsPoint.«x86_64-no-tables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity two_ne_zero, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

end Curve25519Dalek.backend.serial.curve_models
