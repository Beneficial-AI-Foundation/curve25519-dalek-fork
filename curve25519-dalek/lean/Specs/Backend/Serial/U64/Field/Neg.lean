/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
import Specs.Backend.Serial.U64.Field.Negate
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51
@[step]
theorem neg_spec (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    neg self ⦃ (r : FieldElement51) =>
      (r.asNat + self.asNat) % p = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold neg
  step*
end Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51
