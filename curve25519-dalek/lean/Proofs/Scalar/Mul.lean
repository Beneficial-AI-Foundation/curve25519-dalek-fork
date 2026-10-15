/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Target
import Proofs.Backend.Serial.U64.Scalar.Mul
import Proofs.Helpers.Scalar
import Proofs.Helpers.Target
import Proofs.Scalar.Scalar52Pack
import Proofs.Scalar.Unpack
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.MulShared0ScalarSharedAScalarScalar

@[step]
theorem mul.«x86_64-tables_spec» (self _rhs : Scalar) :
    mul.«x86_64-tables» self _rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * _rhs.asNat % L ⦄ := by
  unfold mul.«x86_64-tables»
  step as ⟨a, ha, hab⟩
  step as ⟨b, hb, hbb⟩
  step with backend.serial.u64.scalar.Scalar52.mul_spec a b hab hbb
    (ha ▸ hb ▸ mul_lt_montgomeryRadix_mul_L self.asNat_lt _rhs.asNat_lt) as ⟨c, hc, hcb⟩
  step with Scalar52.pack_spec c hcb (lt_two_pow_256_of_lt_L (hc ▸ Nat.mod_lt _ L_pos))
    as ⟨r, hr⟩
  rw [hr, hc, ha, hb]

end Curve25519Dalek.scalar.MulShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.MulShared0ScalarSharedAScalarScalar

@[step]
theorem mul.«x86_64-no-tables_spec» (self _rhs : Scalar) :
    mul.«x86_64-no-tables» self _rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * _rhs.asNat % L ⦄ :=
  mul.«x86_64-tables_spec» self _rhs

end Curve25519Dalek.scalar.MulShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar

@[step]
theorem mul_spec (self _rhs : Scalar) (htgt : OnX86_64) :
    mul self _rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * _rhs.asNat % L ⦄ := by
  unfold mul
  exact dispatch_spec htgt
    (scalar.MulShared0ScalarSharedAScalarScalar.mul.«x86_64-tables_spec» self _rhs)
    (scalar.MulShared0ScalarSharedAScalarScalar.mul.«x86_64-no-tables_spec» self _rhs)

end Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar

/-- `Mul<&Scalar> for Scalar` (from `define_mul_variants!`): forwards to `&Scalar * &Scalar`. -/
@[step]
theorem mul_spec (self rhs : Scalar) (htgt : OnX86_64) :
    mul self rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * rhs.asNat % L ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar

namespace Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar

/-- `Mul<Scalar> for &Scalar` (from `define_mul_variants!`): forwards to `&Scalar * &Scalar`. -/
@[step]
theorem mul_spec (self rhs : Scalar) (htgt : OnX86_64) :
    mul self rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * rhs.asNat % L ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar

/-- `Mul<Scalar> for Scalar` (from `define_mul_variants!`): forwards to `&Scalar * &Scalar`. -/
@[step]
theorem mul_spec (self rhs : Scalar) (htgt : OnX86_64) :
    mul self rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * rhs.asNat % L ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar
