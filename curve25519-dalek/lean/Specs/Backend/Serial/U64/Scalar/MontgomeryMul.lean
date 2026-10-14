/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
module
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
import Specs.Backend.Serial.U64.Scalar.MontgomeryReduce
import Specs.Backend.Serial.U64.Scalar.MulInternal
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

@[step]
theorem montgomery_mul_spec (a b : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) (hab : a.asNat * b.asNat < montgomeryRadix * L) :
    montgomery_mul a b ⦃ (r : Scalar52) =>
      r.asNat * montgomeryRadix % L = a.asNat * b.asNat % L ∧ r.asNat < L ∧
      ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold montgomery_mul
  step with mul_internal_spec a b ha hb as ⟨ab, hab_eq, hab_lt⟩
  step with montgomery_reduce_spec ab (fun i hi => (hab_lt i hi).trans (by decide))
    (hab_eq ▸ hab) as ⟨r, hr, hrL, hr_lt⟩
  exact ⟨hab_eq ▸ hr, hrL, hr_lt⟩

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
