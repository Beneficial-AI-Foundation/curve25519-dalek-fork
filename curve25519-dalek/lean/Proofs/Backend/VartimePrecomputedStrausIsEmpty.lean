/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
public import Defs.ScalarMul
import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.IsEmpty
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «VartimePrecomputedStrausx86_64-tables»

set_option linter.style.longLine false in
/-- `VartimePrecomputedStraus::is_empty` (backend): whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«x86_64-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    is_empty self ⦃ (r : Bool) => r = decide (ps = []) ⦄ := by
  rcases self with ⟨inner⟩
  unfold is_empty
  exact
      serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-tables».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables».is_empty_spec
      inner ps hself

end «VartimePrecomputedStrausx86_64-tables»

namespace «VartimePrecomputedStrausx86_64-no-tables»

set_option linter.style.longLine false in
/-- `VartimePrecomputedStraus::is_empty` (backend): whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«x86_64-no-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    is_empty self ⦃ (r : Bool) => r = decide (ps = []) ⦄ := by
  rcases self with ⟨inner⟩
  unfold is_empty
  exact
      serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-no-tables».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables».is_empty_spec
      inner ps hself

end «VartimePrecomputedStrausx86_64-no-tables»

end Curve25519Dalek.backend
