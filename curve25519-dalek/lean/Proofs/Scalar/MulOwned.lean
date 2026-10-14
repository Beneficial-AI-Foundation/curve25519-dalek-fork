/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Target
import Proofs.Scalar.Mul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar

/-- `Mul<&Scalar> for Scalar` (from `define_mul_variants!`): forwards to `&Scalar * &Scalar`. -/
@[step]
theorem mul_spec (self rhs : Scalar) (htgt : OnX86_64) :
    mul self rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * rhs.asNat % L ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar
