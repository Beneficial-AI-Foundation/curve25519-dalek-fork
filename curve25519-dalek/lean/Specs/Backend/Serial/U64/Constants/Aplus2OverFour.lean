/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Specs.Backend.Serial.U64.Field.FromLimbs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)

namespace Curve25519Dalek.backend.serial.u64.constants

@[step]
theorem APLUS2_OVER_FOUR_spec :
    APLUS2_OVER_FOUR ⦃ (r : FieldElement51) =>
      r.asNat * 4 = A + 2 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  unfold APLUS2_OVER_FOUR
  step*
  subst_vars
  decide

end Curve25519Dalek.backend.serial.u64.constants
