/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.MulBase
import Proofs.Scalar.ClampInteger
public section

/-! # `EdwardsPoint::mul_base_clamped`

The `x86_64-tables` statement is conditional on `ED25519_BASEPOINT_TABLE` (see `MulBase.lean`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. Conditional on the precomputed constant
`ED25519_BASEPOINT_TABLE` being the radix-`16` table of `B` (`htable`). -/
@[step]
theorem mul_base_clamped_spec_of_table
    (htable : backend.serial.u64.constants.ED25519_BASEPOINT_TABLE
      ⦃ (t : EdwardsBasepointTable.«x86_64-tables») => t.Represents basepoint ∧ t.Bounded ⦄)
    (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = clamp (bytes.asNat 8) • basepoint ∧ r.Bounded ⦄ := by
  unfold mul_base_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  step with mul_base_spec_of_table htable _ (hca ▸ clamp_lt _) as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hca ▸ hr, hrb⟩

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. -/
@[step]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = clamp (bytes.asNat 8) • basepoint ∧ r.Bounded ⦄ := by
  unfold mul_base_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  step with mul_base_spec _ (hca ▸ clamp_lt _) as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hca ▸ hr, hrb⟩

end «EdwardsPointx86_64-no-tables»

end Curve25519Dalek.edwards
