/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Target
import Proofs.Scalar.Neg
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar

@[step]
theorem neg_spec (self : Scalar) (htgt : OnX86_64) :
    neg self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄ := by
  unfold neg
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar
