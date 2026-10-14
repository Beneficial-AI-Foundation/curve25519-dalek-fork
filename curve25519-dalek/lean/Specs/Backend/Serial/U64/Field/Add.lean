/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
import Specs.Backend.Serial.U64.Field.AddAssign
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithAddSharedAFieldElement51FieldElement51
@[step]
theorem add_spec (self _rhs : FieldElement51)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    add self _rhs ⦃ (r : FieldElement51) =>
      ∀ i < 5, r[i]!.val = self[i]!.val + _rhs[i]!.val ⦄ := by
  unfold add
  step*
end Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51
