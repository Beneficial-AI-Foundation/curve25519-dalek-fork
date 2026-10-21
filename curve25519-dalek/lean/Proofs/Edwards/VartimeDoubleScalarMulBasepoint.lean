/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Backend.VartimeDoubleBaseMul
public section

/-! # `EdwardsPoint::vartime_double_scalar_mul_basepoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«x86_64-tables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.LimbsLt 52) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with backend.«x86_64-tables».vartime_double_base_mul_spec as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hr, hrb⟩

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«x86_64-no-tables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.LimbsLt 52) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step*

end «EdwardsPointx86_64-no-tables»

end Curve25519Dalek.edwards
