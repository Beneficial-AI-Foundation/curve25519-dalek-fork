/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Edwards.AsProjectiveNiels
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

namespace «Shared0EdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `subProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^52`. -/
@[step]
theorem sub_spec (self other : edwards.EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hother : other.Bounded) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.Bounded ⦄ := by
  unfold sub
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `sub_spec`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«x86_64-tables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.Bounded) :
    r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.Bounded := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels two_ne_zero hother_on)
  rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«x86_64-tables».toPoint_def,
    edwards.EdwardsPoint.«x86_64-tables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels two_ne_zero hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self other : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.Bounded) (hother : other.Bounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (sub_spec self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end «Shared0EdwardsPointx86_64-tables».Insts

open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
  (point_of_post)

namespace edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.Bounded ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithSubSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.Bounded ⦄ := by
  unfold sub
  step*

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end edwards.EdwardsPoint.«x86_64-tables».Insts

namespace «SharedAEdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : edwards.EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.Bounded ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : edwards.EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end «SharedAEdwardsPointx86_64-tables».Insts

namespace «Shared0EdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `subProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^52`. -/
@[step]
theorem sub_spec (self other : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hother : other.Bounded) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.Bounded ⦄ := by
  unfold sub
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `sub_spec`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«x86_64-no-tables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.Bounded) :
    r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.Bounded := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels two_ne_zero hother_on)
  rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def,
    edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels two_ne_zero hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self other : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.Bounded) (hother : other.Bounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (sub_spec self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end «Shared0EdwardsPointx86_64-no-tables».Insts

open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
  (point_of_post)

namespace edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.Bounded ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithSubSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.Bounded ⦄ := by
  unfold sub
  step*

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace «SharedAEdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.Bounded ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end «SharedAEdwardsPointx86_64-no-tables».Insts

end Curve25519Dalek
