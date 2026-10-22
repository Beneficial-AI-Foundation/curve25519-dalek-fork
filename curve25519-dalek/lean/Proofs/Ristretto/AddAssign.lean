/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Ristretto.Add
public section

/-! # `AddAssign` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddAssignShared0RistrettoPointx86_64-tables»

/-- `AddAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignShared0RistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddAssignRistrettoPointx86_64-tables»

/-- `AddAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddAssignShared0RistrettoPointx86_64-no-tables»

/-- `AddAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignShared0RistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddAssignRistrettoPointx86_64-no-tables»

/-- `AddAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

end Curve25519Dalek
