/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.edwards.affine

namespace «AffinePointx86_64-tables»

/-- `AffinePoint::to_edwards`: `(x : y : 1 : x y)`, limbs `< 2^52`. -/
@[step]
theorem to_edwards_spec (self : AffinePoint.«x86_64-tables») (hself : self.Bounded) :
    to_edwards self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended = ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ ∧
        r.Bounded ⦄ := by
  obtain ⟨hx, hy⟩ := hself
  unfold to_edwards
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«x86_64-tables».toExtended_def, toField_mul_of_mod hxy,
      toField_eq_one_of_asNat hone]
  · exact ⟨hx, hy, limbs_lt_of_le (by decide) hone_lt, hxy_lt⟩

/-- `AffinePoint::to_edwards` represents the same point. -/
theorem to_edwards_spec_point (self : AffinePoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    to_edwards self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (to_edwards_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«x86_64-tables».onCurve_iff,
      EdwardsPoint.«x86_64-tables».toPoint_def,
      hr,
      ← AffinePoint.«x86_64-tables».toExtended_toPoint hon]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «AffinePointx86_64-tables»

namespace «AffinePointx86_64-no-tables»

/-- `AffinePoint::to_edwards`: `(x : y : 1 : x y)`, limbs `< 2^52`. -/
@[step]
theorem to_edwards_spec (self : AffinePoint.«x86_64-no-tables») (hself : self.Bounded) :
    to_edwards self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended = ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ ∧
        r.Bounded ⦄ := by
  obtain ⟨hx, hy⟩ := hself
  unfold to_edwards
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, toField_mul_of_mod hxy,
      toField_eq_one_of_asNat hone]
  · exact ⟨hx, hy, limbs_lt_of_le (by decide) hone_lt, hxy_lt⟩

/-- `AffinePoint::to_edwards` represents the same point. -/
theorem to_edwards_spec_point (self : AffinePoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    to_edwards self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.Bounded ⦄ :=
  spec_mono (to_edwards_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«x86_64-no-tables».onCurve_iff,
      EdwardsPoint.«x86_64-no-tables».toPoint_def,
      hr,
      ← AffinePoint.«x86_64-no-tables».toExtended_toPoint hon]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «AffinePointx86_64-no-tables»

end Curve25519Dalek.edwards.affine
