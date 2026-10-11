/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Field.Zero
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.CoreDefaultDefault

@[step]
theorem default_spec :
    default ⦃ (r : FieldElement51) =>
      r.asNat = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  unfold default
  step*

end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.CoreDefaultDefault
