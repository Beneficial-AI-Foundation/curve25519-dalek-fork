/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Target
import Proofs.Scalar.AddOwned
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignSharedAScalar

@[step]
theorem add_assign_spec (self _rhs : Scalar) (hself : self.asNat < L) (hrhs : _rhs.asNat < L)
    (htgt : OnX86_64) :
    add_assign self _rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + _rhs.asNat) % L ⦄ := by
  unfold add_assign
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignSharedAScalar
