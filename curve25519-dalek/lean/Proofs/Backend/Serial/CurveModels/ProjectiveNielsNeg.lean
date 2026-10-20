/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
import Proofs.Backend.Serial.U64.Field.Neg
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

namespace «Shared0ProjectiveNielsPointx86_64-tables».Insts
namespace «CoreOpsArithNegProjectiveNielsPointx86_64-tables»

/-- `Neg for &ProjectiveNielsPoint`: swap `Y + X` and `Y - X`, negate `T2d`; limbs `< 2^54`. -/
@[step]
theorem neg_spec (self : ProjectiveNielsPoint.«x86_64-tables») (hself : self.Bounded) :
    neg self ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      r.toProjectiveNiels = self.toProjectiveNiels.neg ∧ r.Bounded ⦄ := by
  obtain ⟨hYpX, hYmX, hZ, hT2d⟩ := hself
  unfold neg
  step as ⟨T2d', hT2d', hT2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«x86_64-tables».toProjectiveNiels_def, ProjectiveNiels.neg,
      toField_neg_of_mod hT2d']
  · exact ⟨hYmX, hYpX, hZ, limbs_lt_of_le (by decide) hT2d'_lt⟩

/-- `Neg for &ProjectiveNielsPoint` negates the represented point. -/
theorem neg_spec_point (self : ProjectiveNielsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (neg_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«x86_64-tables».onCurve_iff,
      ProjectiveNielsPoint.«x86_64-tables».toPoint_def, hr,
      ProjectiveNielsPoint.«x86_64-tables».toPoint_def]
    exact ⟨ProjectiveNiels.onCurve_neg hon, ProjectiveNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegProjectiveNielsPointx86_64-tables»
end «Shared0ProjectiveNielsPointx86_64-tables».Insts

namespace «Shared0ProjectiveNielsPointx86_64-no-tables».Insts
namespace «CoreOpsArithNegProjectiveNielsPointx86_64-no-tables»

/-- `Neg for &ProjectiveNielsPoint`: swap `Y + X` and `Y - X`, negate `T2d`; limbs `< 2^54`. -/
@[step]
theorem neg_spec (self : ProjectiveNielsPoint.«x86_64-no-tables») (hself : self.Bounded) :
    neg self ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.toProjectiveNiels = self.toProjectiveNiels.neg ∧ r.Bounded ⦄ := by
  obtain ⟨hYpX, hYmX, hZ, hT2d⟩ := hself
  unfold neg
  step as ⟨T2d', hT2d', hT2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«x86_64-no-tables».toProjectiveNiels_def, ProjectiveNiels.neg,
      toField_neg_of_mod hT2d']
  · exact ⟨hYmX, hYpX, hZ, limbs_lt_of_le (by decide) hT2d'_lt⟩

/-- `Neg for &ProjectiveNielsPoint` negates the represented point. -/
theorem neg_spec_point (self : ProjectiveNielsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (neg_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«x86_64-no-tables».onCurve_iff,
      ProjectiveNielsPoint.«x86_64-no-tables».toPoint_def, hr,
      ProjectiveNielsPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨ProjectiveNiels.onCurve_neg hon, ProjectiveNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegProjectiveNielsPointx86_64-no-tables»
end «Shared0ProjectiveNielsPointx86_64-no-tables».Insts

end Curve25519Dalek
