/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Constants.EdwardsD
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Neg
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Edwards.AsBytes
import Proofs.Field.SqrtRatioI
import Proofs.Helpers.Array
import Proofs.Helpers.Coords
import Proofs.Helpers.Edwards
import Proofs.Helpers.ToField
import Subtle.Lemmas
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.edwards

namespace decompress

/-- `conditional_negate` on field elements. -/
@[local step]
private theorem conditional_negate_spec (x : FieldElement51) (c : subtle.Choice)
    (hc : c.IsValid) (hx : ∀ i < 5, x[i]!.val < 2 ^ 54) :
    subtle.ConditionallyNegatable.Blanket.conditional_negate
      backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
      Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51 x c ⦃ (r : FieldElement51) =>
      (c = 0#u8 → r = x) ∧
      (c = 1#u8 → (r.asNat + x.asNat) % p = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52) ⦄ := by
  unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
  step as ⟨n, hn, hnb⟩
  step as ⟨r, hr0, hr1⟩
  exact ⟨hr0, fun hc => by rw [hr1 hc]; exact ⟨hn, hnb⟩⟩

/-- `d y² + 1 ≠ 0`: `-1/d` is not a square. -/
private theorem d_mul_sq_add_one_ne_zero (y : ZMod p) : curve25519.d * y ^ 2 + 1 ≠ 0 := by
  have h := d_mul_sq_sub_a_ne_zero (E := curve25519.edwards) y
  rwa [edwards_d, edwards_a_eq_neg_one, sub_neg_eq_add] at h

end decompress

namespace decompress.«x86_64-tables»

/-- `decompress::step_1`: `Y` from the low `255` bits, `Z = 1`, and `(c, X) = sqrt_ratio_i (Y² - 1)
(d Y² + 1)`: `c = 1` iff `xSq Y` is a square, and then `X` is its non-negative root. -/
private theorem step_1_spec (repr : CompressedEdwardsY) :
    step_1.«x86_64-tables» repr ⦃ (c : subtle.Choice) (X Y Z : FieldElement51) =>
      c.IsValid ∧ Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) ∧
      Z.toField = 1 ∧
      (c = 1#u8 ↔ IsSquare (curve25519.edwards.xSq Y.toField)) ∧
      (c = 1#u8 → X.toField ^ 2 = curve25519.edwards.xSq Y.toField) ∧ ¬ X.toField.isNeg ∧
      (∀ i < 5, X[i]!.val < 2 ^ 52) ∧ (∀ i < 5, Y[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, Z[i]!.val < 2 ^ 52) ⦄ := by
  unfold step_1.«x86_64-tables»
  step as ⟨a, ha⟩
  step as ⟨Y, hY, hY_lt⟩
  step as ⟨Z, hZ, hZ_lt⟩
  step as ⟨YY, hYY, hYY_lt⟩
  step as ⟨u, hu, hu_lt⟩
  step as ⟨D, hD, hD_lt⟩
  step as ⟨YYD, hYYD, hYYD_lt⟩
  step as ⟨v, hv⟩
  step as ⟨c, X, hcv, h0, h1, h2, h3, hpar, hX_lt⟩
  rw [ha] at hY
  have hYf : Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, hY, CompressedEdwardsY.asNat_def]
  have hZf : Z.toField = 1 := toField_eq_one_of_asNat hZ
  have huf : u.toField = Y.toField ^ 2 - 1 := by
    rw [toField_sub_of_mod hu, toField_sq_of_mod hYY, hZf]
  have hvf : v.toField = curve25519.d * Y.toField ^ 2 + 1 := by
    rw [toField_add_of_limbs hv, toField_mul_of_mod hYYD, toField_sq_of_mod hYY,
      toField_eq_d_of_asNat hD, hZf, mul_comm (Y.toField ^ 2) curve25519.d]
  have hxSq : curve25519.edwards.xSq Y.toField = u.toField / v.toField := by
    rw [edwards_xSq, huf, hvf]
  have hv0 : v.toField ≠ 0 := hvf ▸ decompress.d_mul_sq_add_one_ne_zero Y.toField
  have hv0' : v.asNat % p ≠ 0 := toField_ne_zero_iff.mp hv0
  have hsq : c = 1#u8 → ∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p := fun hc => by
    by_contra hns
    rw [(h3 hv0' hns).1] at hc
    exact absurd hc (by decide)
  refine ⟨hcv, hYf, hZf, ?_, fun hc => ?_, not_isNeg_toField_of_mod hpar, hX_lt,
    limbs_lt_of_le (by decide) hY_lt, limbs_lt_of_le (by decide) hZ_lt⟩
  · rw [hxSq, ← exists_sq_mul_mod_iff_isSquare_div hv0']
    exact ⟨hsq, fun ⟨x, hx⟩ => (h2 hv0' x hx).1⟩
  · obtain ⟨x, hx⟩ := hsq hc
    rw [hxSq, eq_div_iff hv0]
    exact toField_sq_mul_of_mod (h2 hv0' x hx).2

/-- `decompress::step_2`: `X` negated when bit `255` is set, `T = X Y`; limbs `< 2^52`. -/
private theorem step_2_spec (repr : CompressedEdwardsY) (X Y Z : FieldElement51)
    (hX : ∀ i < 5, X[i]!.val < 2 ^ 52) (hY : ∀ i < 5, Y[i]!.val < 2 ^ 52)
    (hZ : ∀ i < 5, Z[i]!.val < 2 ^ 52) :
    step_2.«x86_64-tables» repr X Y Z ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 0 →
        r.toExtended = ⟨X.toField, Y.toField, Z.toField, X.toField * Y.toField⟩) ∧
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 1 →
        r.toExtended = ⟨-X.toField, Y.toField, Z.toField, -X.toField * Y.toField⟩) ∧
      r.LimbsLt 52 ⦄ := by
  unfold step_2.«x86_64-tables»
  step as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  have hi1v : i1.val = CompressedEdwardsY.asNat repr / 2 ^ 255 := by
    rw [hi1, hi, ha, CompressedEdwardsY.getElem!_31_shiftRight_7]
  have hi1' : i1 = 0#u8 ∨ i1 = 1#u8 := by
    have hle := CompressedEdwardsY.asNat_div_two_pow_le_one repr
    rw [← hi1v] at hle
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · exact Or.inl (UScalar.eq_of_val_eq h)
    · exact Or.inr (UScalar.eq_of_val_eq h)
  step as ⟨csb, hcsbv, hcsb⟩
  step with decompress.conditional_negate_spec as ⟨X1, hX10, hX11⟩
  step as ⟨T, hT, hT_lt⟩
  rw [hcsb] at hX10 hX11
  refine ⟨fun h0 => ?_, fun h1 => ?_, ?_⟩
  · have h : i1 = 0#u8 := UScalar.eq_of_val_eq (by rw [hi1v, h0]; rfl)
    rw [hX10 h] at hT ⊢
    simp only [EdwardsPoint.«x86_64-tables».toExtended_def, toField_mul_of_mod hT]
  · have h : i1 = 1#u8 := UScalar.eq_of_val_eq (by rw [hi1v, h1]; rfl)
    simp only [EdwardsPoint.«x86_64-tables».toExtended_def, toField_mul_of_mod hT,
      toField_neg_of_mod (hX11 h).1]
  · refine ⟨?_, hY, hZ, hT_lt⟩
    rcases hi1' with h | h
    · rw [hX10 h]
      exact hX
    · exact (hX11 h).2

/-- The decompressed point `(x : y : 1 : x y)` with `x² = xSq y` is on the curve. -/
private theorem onCurve_and_toPoint_of_toExtended {ep : EdwardsPoint.«x86_64-tables»}
    {x y : ZMod p} (hx : x ^ 2 = curve25519.edwards.xSq y)
    (h : ep.toExtended = ⟨x, y, 1, x * y⟩) :
    ep.OnCurve ∧ ep.toPoint.x = x ∧ ep.toPoint.y = y := by
  have hon : ep.OnCurve := by
    rw [EdwardsPoint.«x86_64-tables».onCurve_iff, h]
    refine ⟨one_ne_zero, (one_mul _).symm, ?_⟩
    rw [div_one, div_one]
    exact equation_iff_sq_eq_xSq.mpr hx
  refine ⟨hon, ?_, ?_⟩
  · rw [EdwardsPoint.«x86_64-tables».toPoint_x hon]
    simp only [EdwardsPoint.«x86_64-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.1, h.2.2.1, div_one]
  · rw [EdwardsPoint.«x86_64-tables».toPoint_y hon]
    simp only [EdwardsPoint.«x86_64-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.2.1, h.2.2.1, div_one]

end decompress.«x86_64-tables»

namespace CompressedEdwardsY.«x86_64-tables»

/-- `CompressedEdwardsY::decompress`: dalek's lenient decoding `decodeLenient` of the bytes'
value (`y` reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve with
limbs `< 2^52`. -/
@[step]
theorem decompress_spec (self : CompressedEdwardsY) :
    decompress.«x86_64-tables» self ⦃ (r : Option (EdwardsPoint.«x86_64-tables»)) =>
      r.map EdwardsPoint.«x86_64-tables».toPoint = decodeLenient self.asNat ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  unfold decompress.«x86_64-tables»
  step with decompress.«x86_64-tables».step_1_spec
    as ⟨c, X, Y, Z, hcv, hYf, hZf, hc, hX, hXneg, hX_lt, hY_lt, hZ_lt⟩
  step as ⟨b, hb⟩
  rcases hcv with rfl | rfl
  · simp only [hb, bne_self_eq_false, Bool.false_eq_true, ite_false, WP.spec_ok]
    refine ⟨?_, fun q hq => by cases hq⟩
    rw [Option.map_none, eq_comm, decodeLenient_eq_none_iff, ← hYf]
    exact fun hs => absurd (hc.mpr hs) (by decide)
  · simp only [hb, show (1#u8 != 0#u8) = true from by decide, ite_true]
    step with decompress.«x86_64-tables».step_2_spec as ⟨ep, hep0, hep1, hepb⟩
    rw [hZf] at hep0 hep1
    have hsq := hX rfl
    have hle := self.asNat_div_two_pow_le_one
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«x86_64-tables».onCurve_and_toPoint_of_toExtended hsq (hep0 h0)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenient_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf]) (fun _ => hpx)
        (fun h => absurd (h0.symm.trans h) (by decide)) hle
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«x86_64-tables».onCurve_and_toPoint_of_toExtended
          (by rw [neg_sq]; exact hsq) (hep1 h1)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenient_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf])
        (fun h => absurd (h1.symm.trans h) (by decide)) (fun _ => hpx) hle

end CompressedEdwardsY.«x86_64-tables»

namespace decompress.«x86_64-no-tables»

/-- `decompress::step_1`: `Y` from the low `255` bits, `Z = 1`, and `(c, X) = sqrt_ratio_i (Y² - 1)
(d Y² + 1)`: `c = 1` iff `xSq Y` is a square, and then `X` is its non-negative root. -/
private theorem step_1_spec (repr : CompressedEdwardsY) :
    step_1.«x86_64-no-tables» repr ⦃ (c : subtle.Choice) (X Y Z : FieldElement51) =>
      c.IsValid ∧ Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) ∧
      Z.toField = 1 ∧
      (c = 1#u8 ↔ IsSquare (curve25519.edwards.xSq Y.toField)) ∧
      (c = 1#u8 → X.toField ^ 2 = curve25519.edwards.xSq Y.toField) ∧ ¬ X.toField.isNeg ∧
      (∀ i < 5, X[i]!.val < 2 ^ 52) ∧ (∀ i < 5, Y[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, Z[i]!.val < 2 ^ 52) ⦄ := by
  unfold step_1.«x86_64-no-tables»
  step as ⟨a, ha⟩
  step as ⟨Y, hY, hY_lt⟩
  step as ⟨Z, hZ, hZ_lt⟩
  step as ⟨YY, hYY, hYY_lt⟩
  step as ⟨u, hu, hu_lt⟩
  step as ⟨D, hD, hD_lt⟩
  step as ⟨YYD, hYYD, hYYD_lt⟩
  step as ⟨v, hv⟩
  step as ⟨c, X, hcv, h0, h1, h2, h3, hpar, hX_lt⟩
  rw [ha] at hY
  have hYf : Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, hY, CompressedEdwardsY.asNat_def]
  have hZf : Z.toField = 1 := toField_eq_one_of_asNat hZ
  have huf : u.toField = Y.toField ^ 2 - 1 := by
    rw [toField_sub_of_mod hu, toField_sq_of_mod hYY, hZf]
  have hvf : v.toField = curve25519.d * Y.toField ^ 2 + 1 := by
    rw [toField_add_of_limbs hv, toField_mul_of_mod hYYD, toField_sq_of_mod hYY,
      toField_eq_d_of_asNat hD, hZf, mul_comm (Y.toField ^ 2) curve25519.d]
  have hxSq : curve25519.edwards.xSq Y.toField = u.toField / v.toField := by
    rw [edwards_xSq, huf, hvf]
  have hv0 : v.toField ≠ 0 := hvf ▸ decompress.d_mul_sq_add_one_ne_zero Y.toField
  have hv0' : v.asNat % p ≠ 0 := toField_ne_zero_iff.mp hv0
  have hsq : c = 1#u8 → ∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p := fun hc => by
    by_contra hns
    rw [(h3 hv0' hns).1] at hc
    exact absurd hc (by decide)
  refine ⟨hcv, hYf, hZf, ?_, fun hc => ?_, not_isNeg_toField_of_mod hpar, hX_lt,
    limbs_lt_of_le (by decide) hY_lt, limbs_lt_of_le (by decide) hZ_lt⟩
  · rw [hxSq, ← exists_sq_mul_mod_iff_isSquare_div hv0']
    exact ⟨hsq, fun ⟨x, hx⟩ => (h2 hv0' x hx).1⟩
  · obtain ⟨x, hx⟩ := hsq hc
    rw [hxSq, eq_div_iff hv0]
    exact toField_sq_mul_of_mod (h2 hv0' x hx).2

/-- `decompress::step_2`: `X` negated when bit `255` is set, `T = X Y`; limbs `< 2^52`. -/
private theorem step_2_spec (repr : CompressedEdwardsY) (X Y Z : FieldElement51)
    (hX : ∀ i < 5, X[i]!.val < 2 ^ 52) (hY : ∀ i < 5, Y[i]!.val < 2 ^ 52)
    (hZ : ∀ i < 5, Z[i]!.val < 2 ^ 52) :
    step_2.«x86_64-no-tables» repr X Y Z ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 0 →
        r.toExtended = ⟨X.toField, Y.toField, Z.toField, X.toField * Y.toField⟩) ∧
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 1 →
        r.toExtended = ⟨-X.toField, Y.toField, Z.toField, -X.toField * Y.toField⟩) ∧
      r.LimbsLt 52 ⦄ := by
  unfold step_2.«x86_64-no-tables»
  step as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  have hi1v : i1.val = CompressedEdwardsY.asNat repr / 2 ^ 255 := by
    rw [hi1, hi, ha, CompressedEdwardsY.getElem!_31_shiftRight_7]
  have hi1' : i1 = 0#u8 ∨ i1 = 1#u8 := by
    have hle := CompressedEdwardsY.asNat_div_two_pow_le_one repr
    rw [← hi1v] at hle
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · exact Or.inl (UScalar.eq_of_val_eq h)
    · exact Or.inr (UScalar.eq_of_val_eq h)
  step as ⟨csb, hcsbv, hcsb⟩
  step with decompress.conditional_negate_spec as ⟨X1, hX10, hX11⟩
  step as ⟨T, hT, hT_lt⟩
  rw [hcsb] at hX10 hX11
  refine ⟨fun h0 => ?_, fun h1 => ?_, ?_⟩
  · have h : i1 = 0#u8 := UScalar.eq_of_val_eq (by rw [hi1v, h0]; rfl)
    rw [hX10 h] at hT ⊢
    simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, toField_mul_of_mod hT]
  · have h : i1 = 1#u8 := UScalar.eq_of_val_eq (by rw [hi1v, h1]; rfl)
    simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, toField_mul_of_mod hT,
      toField_neg_of_mod (hX11 h).1]
  · refine ⟨?_, hY, hZ, hT_lt⟩
    rcases hi1' with h | h
    · rw [hX10 h]
      exact hX
    · exact (hX11 h).2

/-- The decompressed point `(x : y : 1 : x y)` with `x² = xSq y` is on the curve. -/
private theorem onCurve_and_toPoint_of_toExtended {ep : EdwardsPoint.«x86_64-no-tables»}
    {x y : ZMod p} (hx : x ^ 2 = curve25519.edwards.xSq y)
    (h : ep.toExtended = ⟨x, y, 1, x * y⟩) :
    ep.OnCurve ∧ ep.toPoint.x = x ∧ ep.toPoint.y = y := by
  have hon : ep.OnCurve := by
    rw [EdwardsPoint.«x86_64-no-tables».onCurve_iff, h]
    refine ⟨one_ne_zero, (one_mul _).symm, ?_⟩
    rw [div_one, div_one]
    exact equation_iff_sq_eq_xSq.mpr hx
  refine ⟨hon, ?_, ?_⟩
  · rw [EdwardsPoint.«x86_64-no-tables».toPoint_x hon]
    simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.1, h.2.2.1, div_one]
  · rw [EdwardsPoint.«x86_64-no-tables».toPoint_y hon]
    simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.2.1, h.2.2.1, div_one]

end decompress.«x86_64-no-tables»

namespace CompressedEdwardsY.«x86_64-no-tables»

/-- `CompressedEdwardsY::decompress`: dalek's lenient decoding `decodeLenient` of the bytes'
value (`y` reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve with
limbs `< 2^52`. -/
@[step]
theorem decompress_spec (self : CompressedEdwardsY) :
    decompress.«x86_64-no-tables» self ⦃ (r : Option (EdwardsPoint.«x86_64-no-tables»)) =>
      r.map EdwardsPoint.«x86_64-no-tables».toPoint = decodeLenient self.asNat ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  unfold decompress.«x86_64-no-tables»
  step with decompress.«x86_64-no-tables».step_1_spec
    as ⟨c, X, Y, Z, hcv, hYf, hZf, hc, hX, hXneg, hX_lt, hY_lt, hZ_lt⟩
  step as ⟨b, hb⟩
  rcases hcv with rfl | rfl
  · simp only [hb, bne_self_eq_false, Bool.false_eq_true, ite_false, WP.spec_ok]
    refine ⟨?_, fun q hq => by cases hq⟩
    rw [Option.map_none, eq_comm, decodeLenient_eq_none_iff, ← hYf]
    exact fun hs => absurd (hc.mpr hs) (by decide)
  · simp only [hb, show (1#u8 != 0#u8) = true from by decide, ite_true]
    step with decompress.«x86_64-no-tables».step_2_spec as ⟨ep, hep0, hep1, hepb⟩
    rw [hZf] at hep0 hep1
    have hsq := hX rfl
    have hle := self.asNat_div_two_pow_le_one
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«x86_64-no-tables».onCurve_and_toPoint_of_toExtended hsq (hep0 h0)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenient_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf]) (fun _ => hpx)
        (fun h => absurd (h0.symm.trans h) (by decide)) hle
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«x86_64-no-tables».onCurve_and_toPoint_of_toExtended
          (by rw [neg_sq]; exact hsq) (hep1 h1)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenient_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf])
        (fun h => absurd (h1.symm.trans h) (by decide)) (fun _ => hpx) hle

end CompressedEdwardsY.«x86_64-no-tables»

end Curve25519Dalek.edwards
