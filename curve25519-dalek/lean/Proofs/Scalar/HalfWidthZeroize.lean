/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Zeroize.Instances
public import Curve25519.Basic
public import Defs.Scalar52
import Subtle
import Mathlib.Tactic.ReduceModChar
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.ZeroizeZeroize

@[step]
theorem zeroize_spec (self : HalfWidthScalar) :
    zeroize self ⦃ (r : HalfWidthScalar) =>
      r.asNat = 0 ⦄ := by
  unfold zeroize
  step*
  simp [HalfWidthScalar.asNat, Scalar.asNat, Array.asNat, Nat.ofDigits, *]

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.ZeroizeZeroize
