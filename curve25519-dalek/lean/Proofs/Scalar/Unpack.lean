/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
public import Defs.Scalar
import Proofs.Backend.Serial.U64.Scalar.FromBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem unpack.«x86_64-tables_spec» (self : Scalar) :
    unpack.«x86_64-tables» self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat = self.asNat ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold unpack.«x86_64-tables»
  step as ⟨r, hr, hrb⟩
  exact ⟨hr, hrb⟩

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem unpack.«x86_64-no-tables_spec» (self : Scalar) :
    unpack.«x86_64-no-tables» self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat = self.asNat ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold unpack.«x86_64-no-tables»
  step as ⟨r, hr, hrb⟩
  exact ⟨hr, hrb⟩

end Curve25519Dalek.scalar.Scalar
