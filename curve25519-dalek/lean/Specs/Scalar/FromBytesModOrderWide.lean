/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Curve25519.Basic
import Specs.Backend.Serial.U64.Scalar.FromBytesWide
import Specs.Scalar.Lemmas
import Specs.Scalar.Scalar52Pack
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem from_bytes_mod_order_wide.«x86_64-tables_spec» (input : Array U8 64#usize) :
    from_bytes_mod_order_wide.«x86_64-tables» input ⦃ (r : Scalar) =>
      r.asNat = input.asNat 8 % L ⦄ := by
  unfold from_bytes_mod_order_wide.«x86_64-tables»
  step as ⟨s, hs, hsb⟩
  step with Scalar52.pack_spec s hsb (lt_two_pow_256_of_lt_L (hs ▸ Nat.mod_lt _ L_pos))
    as ⟨r, hr⟩
  rw [hr, hs]

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem from_bytes_mod_order_wide.«x86_64-no-tables_spec» (input : Array U8 64#usize) :
    from_bytes_mod_order_wide.«x86_64-no-tables» input ⦃ (r : Scalar) =>
      r.asNat = input.asNat 8 % L ⦄ :=
  from_bytes_mod_order_wide.«x86_64-tables_spec» input

end Curve25519Dalek.scalar.Scalar
