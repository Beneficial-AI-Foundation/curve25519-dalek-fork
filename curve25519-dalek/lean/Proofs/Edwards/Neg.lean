/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Field.Neg
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

namespace «Shared0EdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithNegEdwardsPointx86_64-tables»

/-- `Neg for &EdwardsPoint`: `(-X : Y : Z : -T)`, limbs `< 2^52`. -/
@[step]
theorem neg_spec (self : edwards.EdwardsPoint.«x86_64-tables») (hself : self.Bounded) :
    neg self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.toExtended = self.toExtended.neg ∧ r.Bounded ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold neg
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«x86_64-tables».toExtended_def, Extended.neg,
      toField_neg_of_mod hX', toField_neg_of_mod hT']
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt, hY, hZ, limbs_lt_of_le (by decide) hT'_lt⟩

/-- The point-level reading of the postcondition of `neg_spec`. -/
private theorem point_of_post {self r : edwards.EdwardsPoint.«x86_64-tables»}
    (hon : self.OnCurve) (h : r.toExtended = self.toExtended.neg ∧ r.Bounded) :
    r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded := by
  obtain ⟨hr, hb⟩ := h
  rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«x86_64-tables».toPoint_def]
  exact ⟨Extended.onCurve_neg hon, Extended.toPoint_neg hon, hb⟩

/-- `Neg for &EdwardsPoint` negates the represented point. -/
theorem neg_spec_point (self : edwards.EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (neg_spec self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPointx86_64-tables»
end «Shared0EdwardsPointx86_64-tables».Insts

open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithNegEdwardsPointx86_64-tables» (point_of_post)

namespace edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithNegEdwardsPointx86_64-tables»

/-- `Neg for EdwardsPoint` (by value): `(-X : Y : Z : -T)`, limbs `< 2^52`. -/
@[step]
theorem neg_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded) :
    neg self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended = self.toExtended.neg ∧ r.Bounded ⦄ := by
  unfold neg
  step*

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
theorem neg_spec_point (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (neg_spec self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPointx86_64-tables»
end edwards.EdwardsPoint.«x86_64-tables».Insts

namespace «Shared0EdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithNegEdwardsPointx86_64-no-tables»

/-- `Neg for &EdwardsPoint`: `(-X : Y : Z : -T)`, limbs `< 2^52`. -/
@[step]
theorem neg_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded) :
    neg self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended = self.toExtended.neg ∧ r.Bounded ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold neg
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.neg,
      toField_neg_of_mod hX', toField_neg_of_mod hT']
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt, hY, hZ, limbs_lt_of_le (by decide) hT'_lt⟩

/-- The point-level reading of the postcondition of `neg_spec`. -/
private theorem point_of_post {self r : edwards.EdwardsPoint.«x86_64-no-tables»}
    (hon : self.OnCurve) (h : r.toExtended = self.toExtended.neg ∧ r.Bounded) :
    r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded := by
  obtain ⟨hr, hb⟩ := h
  rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def]
  exact ⟨Extended.onCurve_neg hon, Extended.toPoint_neg hon, hb⟩

/-- `Neg for &EdwardsPoint` negates the represented point. -/
theorem neg_spec_point (self : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (neg_spec self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPointx86_64-no-tables»
end «Shared0EdwardsPointx86_64-no-tables».Insts

open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithNegEdwardsPointx86_64-no-tables» (point_of_post)

namespace edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithNegEdwardsPointx86_64-no-tables»

/-- `Neg for EdwardsPoint` (by value): `(-X : Y : Z : -T)`, limbs `< 2^52`. -/
@[step]
theorem neg_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded) :
    neg self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended = self.toExtended.neg ∧ r.Bounded ⦄ := by
  unfold neg
  step*

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
theorem neg_spec_point (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (neg_spec self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPointx86_64-no-tables»
end edwards.EdwardsPoint.«x86_64-no-tables».Insts

end Curve25519Dalek
