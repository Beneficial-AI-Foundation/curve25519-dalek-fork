/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Scalar.Unpack
public import Specs.Scalar.Scalar52Pack
public import Specs.Scalar.Scalar52Invert
public import Specs.Scalar.Lemmas
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert.«x86_64-tables_spec» (self : Scalar) :
    invert.«x86_64-tables» self ⦃ (r : Scalar) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄ := by
  unfold invert.«x86_64-tables»
  step as ⟨u, hu, hub⟩
  step as ⟨v, hv1, hv0, hvL, hvb⟩
  step with Scalar52.pack_spec v hvb (lt_two_pow_256_of_lt_L hvL) as ⟨r, hr⟩
  rw [hr, ← hu]
  exact ⟨hv1, hv0, hvL⟩

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert.«x86_64-no-tables_spec» (self : Scalar) :
    invert.«x86_64-no-tables» self ⦃ (r : Scalar) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄ :=
  invert.«x86_64-tables_spec» self

end Curve25519Dalek.scalar.Scalar
