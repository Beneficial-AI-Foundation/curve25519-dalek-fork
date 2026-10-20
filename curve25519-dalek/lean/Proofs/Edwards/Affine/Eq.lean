/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.Affine.CtEq
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.edwards.affine

namespace AffinePoint.«x86_64-tables».Insts.«CoreCmpPartialEqAffinePointx86_64-tables»

/-- `PartialEq for AffinePoint`: both coordinates agree modulo `p`. -/
@[step]
theorem eq_spec (self other : AffinePoint.«x86_64-tables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.x.toField = other.x.toField ∧ self.y.toField = other.y.toField ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for AffinePoint` on points: equality of the represented points. -/
theorem eq_spec_point (self other : AffinePoint.«x86_64-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_spec self other) fun _ hb => by
    rw [AffinePoint.«x86_64-tables».toPoint_eq_mk hself,
      AffinePoint.«x86_64-tables».toPoint_eq_mk hother, Point.ext_iff]
    exact hb

end AffinePoint.«x86_64-tables».Insts.«CoreCmpPartialEqAffinePointx86_64-tables»

namespace AffinePoint.«x86_64-no-tables».Insts.«CoreCmpPartialEqAffinePointx86_64-no-tables»

/-- `PartialEq for AffinePoint`: both coordinates agree modulo `p`. -/
@[step]
theorem eq_spec (self other : AffinePoint.«x86_64-no-tables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.x.toField = other.x.toField ∧ self.y.toField = other.y.toField ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for AffinePoint` on points: equality of the represented points. -/
theorem eq_spec_point (self other : AffinePoint.«x86_64-no-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_spec self other) fun _ hb => by
    rw [AffinePoint.«x86_64-no-tables».toPoint_eq_mk hself,
      AffinePoint.«x86_64-no-tables».toPoint_eq_mk hother, Point.ext_iff]
    exact hb

end AffinePoint.«x86_64-no-tables».Insts.«CoreCmpPartialEqAffinePointx86_64-no-tables»

end Curve25519Dalek.edwards.affine
