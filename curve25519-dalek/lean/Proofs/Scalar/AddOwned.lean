/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Target
import Proofs.Scalar.Add
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar

/-- `Add<&Scalar> for Scalar` (from `define_add_variants!`): forwards to `&Scalar + &Scalar`. -/
@[step]
theorem add_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L)
    (htgt : OnX86_64) :
    add self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ := by
  unfold add
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar
