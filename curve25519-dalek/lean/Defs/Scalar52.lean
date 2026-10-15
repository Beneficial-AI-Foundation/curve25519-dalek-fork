/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import Curve25519Dalek.Types
public import Defs.Array
public section

/-! # The value of a `Scalar52` and the Montgomery radix (audited) -/

open Aeneas.Std

namespace Curve25519Dalek.backend.serial.u64

/-- The natural number represented by the five radix-2^52 limbs. -/
@[expose]
def scalar.Scalar52.asNat (self : scalar.Scalar52) : ℕ :=
  Array.asNat 52 self

/-- The Montgomery radix `2^260` of the scalar arithmetic; also the modulus at which the five
52-bit limbs of a `Scalar52` wrap around. Not exposed: use `montgomeryRadix_eq`. -/
def scalar.montgomeryRadix : ℕ := 2 ^ 260

theorem scalar.montgomeryRadix_eq : scalar.montgomeryRadix = 2 ^ 260 := by
  unfold scalar.montgomeryRadix
  rfl


end Curve25519Dalek.backend.serial.u64
