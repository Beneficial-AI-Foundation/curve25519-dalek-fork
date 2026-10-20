/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.CtEq
import Proofs.Edwards.Identity
import Proofs.Traits.IsIdentity
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«x86_64-tables»

/-- `IsIdentity::is_identity` (the blanket implementation of `traits.rs`) at `EdwardsPoint`:
`ct_eq` with the identity; limbs `< 2^52`. -/
@[step]
theorem is_identity_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    traits.IsIdentity.Blanket.is_identity
      EdwardsPoint.«x86_64-tables».Insts.SubtleConstantTimeEq
      EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity self ⦃ (b : Bool) =>
      b = true ↔ self.toPoint = 0 ⦄ :=
  traits.IsIdentity.Blanket.is_identity_spec _ _ self _ _
    Insts.Curve25519_dalekTraitsIdentity.identity_spec_point fun e ⟨heon, he, heb⟩ =>
      spec_mono (Insts.SubtleConstantTimeEq.ct_eq_spec_point self e hself heb hon heon)
        fun _ ⟨hcv, hc⟩ => ⟨hcv, he ▸ hc⟩

end EdwardsPoint.«x86_64-tables»

namespace EdwardsPoint.«x86_64-no-tables»

/-- `IsIdentity::is_identity` (the blanket implementation of `traits.rs`) at `EdwardsPoint`:
`ct_eq` with the identity; limbs `< 2^52`. -/
@[step]
theorem is_identity_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    traits.IsIdentity.Blanket.is_identity
      EdwardsPoint.«x86_64-no-tables».Insts.SubtleConstantTimeEq
      EdwardsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity self ⦃ (b : Bool) =>
      b = true ↔ self.toPoint = 0 ⦄ :=
  traits.IsIdentity.Blanket.is_identity_spec _ _ self _ _
    Insts.Curve25519_dalekTraitsIdentity.identity_spec_point fun e ⟨heon, he, heb⟩ =>
      spec_mono (Insts.SubtleConstantTimeEq.ct_eq_spec_point self e hself heb hon heon)
        fun _ ⟨hcv, hc⟩ => ⟨hcv, he ▸ hc⟩

end EdwardsPoint.«x86_64-no-tables»

end Curve25519Dalek.edwards
