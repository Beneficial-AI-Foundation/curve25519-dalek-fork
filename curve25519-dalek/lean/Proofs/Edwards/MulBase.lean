/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointPoint
import Proofs.Edwards.BasepointTableMul
import Proofs.Edwards.Mul
public section

/-! # `EdwardsPoint::mul_base`

In the `x86_64-no-tables` configuration `mul_base` is `scalar * ED25519_BASEPOINT_POINT`. The
`x86_64-tables` configuration multiplies with the precomputed `ED25519_BASEPOINT_TABLE` instead;
that statement is conditional on the constant being the table of `B` (`htable`), which is not
proved yet. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
limbs `< 2^52`. Conditional on the precomputed constant `ED25519_BASEPOINT_TABLE` being the
radix-`16` table of `B` (`htable`). -/
@[step]
theorem mul_base_spec_of_table
    (htable : backend.serial.u64.constants.ED25519_BASEPOINT_TABLE
      ⦃ (t : EdwardsBasepointTable.«x86_64-tables») => t.Represents basepoint ∧ t.Bounded ⦄)
    (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.Bounded ⦄ := by
  unfold mul_base
  step with htable as ⟨t, ht, htb⟩
  step*

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.Bounded ⦄ := by
  unfold mul_base
  step with backend.serial.u64.constants.«x86_64-no-tables».ED25519_BASEPOINT_POINT_spec_point
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «EdwardsPointx86_64-no-tables»

end Curve25519Dalek.edwards
