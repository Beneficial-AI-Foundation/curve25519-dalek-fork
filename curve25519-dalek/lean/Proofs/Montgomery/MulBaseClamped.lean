/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Montgomery
public import Curve25519Dalek.Funs
public import Defs.Montgomery
import Proofs.Montgomery.MulBase
import Proofs.Scalar.ClampInteger
public section

/-! # `MontgomeryPoint::mul_base_clamped`

RFC 7748 `X25519(k, 9)` byte for byte, computed with the Edwards basepoint tables. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.montgomery.MontgomeryPoint

/-- `MontgomeryPoint::mul_base_clamped`: RFC 7748 `X25519(bytes, 9)`. -/
@[step]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : MontgomeryPoint) =>
      r.bytes = X25519 bytes.toVector (encodeUCoordinate 9) ⦄ := by
  simp only
      [curve25519.eq_X25519_iff,
      Curve25519Dalek.montgomery.MontgomeryPoint.decodeLittleEndian_bytes,
      Aeneas.Std.Array.decodeLittleEndian_toVector,
      curve25519.decodeLittleEndian_encodeUCoordinate, curve25519.encodeU_nine]
  unfold mul_base_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  step with mul_base_spec { bytes := a } (hca ▸ clamp_lt _) as ⟨r, hr⟩
  rw [curve25519.eq_encodeUCoordinate_iff, MontgomeryPoint.decodeLittleEndian_bytes] at hr
  rw [hr, hca, x25519Nat_basepoint]

end Curve25519Dalek.montgomery.MontgomeryPoint
