/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Field.SquareLimbs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51
@[step]
theorem square_spec (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    square self ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ 2 % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold square
  step*
end Curve25519Dalek.backend.serial.u64.field.FieldElement51
