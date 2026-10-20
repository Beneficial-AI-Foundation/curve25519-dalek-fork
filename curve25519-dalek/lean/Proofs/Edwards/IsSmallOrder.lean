/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.IsIdentity
import Proofs.Edwards.MulByCofactor
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::is_small_order`: `8 • P = 0`; limbs `< 2^52`. -/
@[step]
theorem is_small_order_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    is_small_order self ⦃ (b : Bool) => b = true ↔ 8 • self.toPoint = 0 ⦄ := by
  unfold is_small_order
  step as ⟨ep, hepon, hep, hepb⟩
  step as ⟨b, hb⟩
  rw [hb, hep]

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::is_small_order`: `8 • P = 0`; limbs `< 2^52`. -/
@[step]
theorem is_small_order_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    is_small_order self ⦃ (b : Bool) => b = true ↔ 8 • self.toPoint = 0 ⦄ := by
  unfold is_small_order
  step as ⟨ep, hepon, hep, hepb⟩
  step as ⟨b, hb⟩
  rw [hb, hep]

end «EdwardsPointx86_64-no-tables»

end Curve25519Dalek.edwards
