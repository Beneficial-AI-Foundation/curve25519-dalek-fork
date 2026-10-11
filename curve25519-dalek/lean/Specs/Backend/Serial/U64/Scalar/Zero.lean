/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

theorem ZERO_spec :
    Scalar52.asNat ZERO = 0 ∧ ∀ i < 5, ZERO[i]!.val < 2 ^ 52 := by
  unfold ZERO
  decide

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
