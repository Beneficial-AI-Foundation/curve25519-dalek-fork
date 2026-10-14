/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)
open curve25519 (L_eq_limbs)

namespace Curve25519Dalek.backend.serial.u64.constants

theorem L_spec :
    Scalar52.asNat L = curve25519.L ∧ ∀ i < 5, L[i]!.val < 2 ^ 52 := by
  unfold L
  refine ⟨?_, by decide⟩
  rw [L_eq_limbs]
  decide

end Curve25519Dalek.backend.serial.u64.constants
