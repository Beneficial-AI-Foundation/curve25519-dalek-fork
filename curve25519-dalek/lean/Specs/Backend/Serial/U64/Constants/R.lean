/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52 montgomeryRadix)
open curve25519 (p a d A)

namespace Curve25519Dalek.backend.serial.u64.constants

theorem R_spec :
    Scalar52.asNat R = montgomeryRadix % curve25519.L ∧ ∀ i < 5, R[i]!.val < 2 ^ 52 := by
  unfold R
  rw [scalar.montgomeryRadix_mod_L]
  decide

end Curve25519Dalek.backend.serial.u64.constants
