/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Field.Sub
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreOpsArithSubAssignSharedAFieldElement51
@[step]
theorem sub_assign_spec (self _rhs : FieldElement51)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    sub_assign self _rhs ⦃ (r : FieldElement51) =>
      (r.asNat + _rhs.asNat) % p = self.asNat % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold sub_assign
  step*
end CoreOpsArithSubAssignSharedAFieldElement51
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
