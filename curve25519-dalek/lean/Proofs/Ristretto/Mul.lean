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
import Proofs.Edwards.Mul
public section

/-! # `Mul` between `RistrettoPoint` and `Scalar` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace «Shared0RistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables»

open edwards.EdwardsPoint in
/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    «x86_64-tables».Insts.«CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables».mul_spec
    self scalar hself hon hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables»
end «Shared0RistrettoPointx86_64-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace «SharedARistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointx86_64-tables»
end «SharedARistrettoPointx86_64-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 52) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    SharedAScalar.Insts.«CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».mul_spec
    self point hself hpoint hpoint_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end Shared0Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end scalar.Scalar.Insts

namespace SharedAScalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end SharedAScalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end scalar.Scalar.Insts

namespace «Shared0RistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables»

open edwards.EdwardsPoint in
/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    «x86_64-no-tables».Insts.«CoreOpsArithMulSharedBScalarEdwardsPointx86_64-no-tables».mul_spec
    self scalar hself hon hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables»
end «Shared0RistrettoPointx86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-no-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace «SharedARistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»
end «SharedARistrettoPointx86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

open SharedAScalar in
/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 52) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    Insts.«CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables».mul_spec
    self point hself hpoint hpoint_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end Shared0Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end scalar.Scalar.Insts

namespace SharedAScalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end SharedAScalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end scalar.Scalar.Insts

end Curve25519Dalek
