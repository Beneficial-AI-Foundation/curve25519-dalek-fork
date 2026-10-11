/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Field.CtEq
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreCmpPartialEqFieldElement51

@[step]
theorem eq_spec (self other : FieldElement51) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔ self.asNat % p = other.asNat % p) ⦄ := by
  unfold eq
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨b, hb⟩
  subst hb
  by_cases h : self.asNat % p = other.asNat % p
  · simp [h, hc1 h]
  · simp [h, hc0 h]

end CoreCmpPartialEqFieldElement51
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
