/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
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
open curve25519 (mod_p_of_lt d_eq)

namespace Curve25519Dalek.backend.serial.u64.constants

@[step]
theorem EDWARDS_D_spec :
    EDWARDS_D ⦃ (r : FieldElement51) =>
      r.asNat = d.val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  unfold EDWARDS_D
  step*
  subst_vars
  refine ⟨?_, by decide⟩
  rw [d_eq, ZMod.val_natCast, mod_p_of_lt] <;> decide

end Curve25519Dalek.backend.serial.u64.constants
