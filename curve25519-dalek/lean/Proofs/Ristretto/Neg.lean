/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
public import Curve25519.Edwards.Basepoint
public import Subtle
import Proofs.Edwards.Neg
public section

/-! # `Neg` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithNegRistrettoPointx86_64-tables»

open «Shared0EdwardsPointx86_64-tables» in
/-- `Neg for &RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold neg
  step with
    Insts.«CoreOpsArithNegEdwardsPointx86_64-tables».neg_spec_point
    self hself hon as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithNegRistrettoPointx86_64-tables»

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithNegRistrettoPointx86_64-tables»

/-- `Neg for RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold neg
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithNegRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace «Shared0RistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithNegRistrettoPointx86_64-no-tables»

open «Shared0EdwardsPointx86_64-no-tables» in
/-- `Neg for &RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold neg
  step with
    Insts.«CoreOpsArithNegEdwardsPointx86_64-no-tables».neg_spec_point
    self hself hon as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithNegRistrettoPointx86_64-no-tables»
end «Shared0RistrettoPointx86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithNegRistrettoPointx86_64-no-tables»

/-- `Neg for RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold neg
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithNegRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

end Curve25519Dalek
