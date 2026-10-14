/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Curve25519.Basic
public import Defs.Scalar52
import Subtle
import Mathlib.Tactic.ReduceModChar
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

theorem ZERO_spec :
    Scalar.asNat ZERO = 0 := by
  simp [Scalar.asNat, Array.asNat, ZERO, Nat.ofDigits]

end Curve25519Dalek.scalar.Scalar
