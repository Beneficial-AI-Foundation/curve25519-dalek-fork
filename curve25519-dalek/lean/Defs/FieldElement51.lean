/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import Curve25519Dalek.Types
public import Defs.Array
public section

/-! # The value of a `FieldElement51` (audited) -/

open Aeneas.Std

namespace Curve25519Dalek.backend.serial.u64

/-- The natural number represented by the five radix-2^51 limbs. The limbs may exceed 51 bits. -/
def field.FieldElement51.asNat (self : field.FieldElement51) : ℕ :=
  Array.asNat 51 self

theorem field.FieldElement51.asNat_def (self : field.FieldElement51) :
    self.asNat = Array.asNat 51 self := by
  unfold field.FieldElement51.asNat
  rfl

end Curve25519Dalek.backend.serial.u64
