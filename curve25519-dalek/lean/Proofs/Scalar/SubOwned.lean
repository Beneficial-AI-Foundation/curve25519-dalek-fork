/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Target
import Proofs.Scalar.Sub
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar

/-- `Sub<&Scalar> for Scalar` (from `define_sub_variants!`): forwards to `&Scalar - &Scalar`. -/
@[step]
theorem sub_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L)
    (htgt : OnX86_64) :
    sub self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold sub
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar
