/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Ristretto.Encoding
public import Defs.Edwards
public import Defs.Ristretto
import Proofs.Backend.Serial.U64.Constants.InvsqrtAMinusD
import Proofs.Backend.Serial.U64.Constants.SqrtM1
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U64.Field.ConditionalNegate
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Field.Invsqrt
import Proofs.Field.IsNegative
import Proofs.Helpers.Coords
import Proofs.Helpers.RistrettoCompress
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Constants.InvsqrtAMinusD
import Proofs.Backend.Serial.U32.Constants.SqrtM1
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.ConditionalAssign
import Proofs.Backend.Serial.U32.Field.ConditionalNegate
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Square
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Backend.Serial.U32.Field.ToBytes
import Proofs.Helpers.ToField2625
public section

/-! # `RistrettoPoint::compress`

The code is RFC 9496 §4.3.2 on the extended coordinates of the representative
(`RistrettoCompress.compressProj`), which equals `encodeRep` of the represented point
(`RistrettoCompress.compressProj_eq_encodeRep`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.ristretto

namespace «RistrettoPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

open edwards.EdwardsPoint.«x86_64-tables» in
/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point; limbs `< 2^52`. -/
@[step]
theorem compress_spec (self : RistrettoPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.asNat = Ristretto.encodeRep self.toPoint ⦄ := by
  obtain ⟨hZ0, hXYZT, -⟩ := (onCurve_iff_equation self).mp hon
  have hx := toPoint_x hon
  have hy := toPoint_y hon
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold compress
  step as ⟨fe, hfe⟩
  step as ⟨fe1, hfe1, hfe1b⟩
  step as ⟨u1, hu1, hu1b⟩
  step as ⟨u2, hu2, hu2b⟩
  step as ⟨fe2, hfe2, hfe2b⟩
  step as ⟨fe3, hfe3, hfe3b⟩
  step as ⟨c0, invsqrt, hc0v, hi0, hi1, hi2, hpar, hib⟩
  step as ⟨i1, hi1', hi1b⟩
  step as ⟨i2, hi2', hi2b⟩
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨z_inv, hz, hzb⟩
  step as ⟨fe5, hfe5, hfe5b⟩
  step as ⟨iX, hiX, hiXb⟩
  step as ⟨iY, hiY, hiYb⟩
  step as ⟨fe6, hfe6lt, hfe6, hfe6b⟩
  step as ⟨ench, hench, henchb⟩
  step as ⟨fe7, hfe7, hfe7b⟩
  step as ⟨rot, hrotv, hrot⟩
  step as ⟨X, hX0, hX1⟩
  step as ⟨Y, hY0, hY1⟩
  step as ⟨i21, hi210, hi211⟩
  have hXb : X.LimbsLt 54 := by
    rcases hrotv with h | h
    · rw [hX0 h]; exact limbs_lt_of_le (by decide) hX
    · rw [hX1 h]; exact limbs_lt_of_le (by decide) hiYb
  have hYb : Y.LimbsLt 54 := by
    rcases hrotv with h | h
    · rw [hY0 h]; exact limbs_lt_of_le (by decide) hY
    · rw [hY1 h]; exact limbs_lt_of_le (by decide) hiXb
  have hi21b : i21.LimbsLt 54 := by
    rcases hrotv with h | h
    · rw [hi210 h]; exact limbs_lt_of_le (by decide) hi2b
    · rw [hi211 h]; exact limbs_lt_of_le (by decide) henchb
  step as ⟨fe8, hfe8, hfe8b⟩
  step as ⟨cn, hcnv, hcn⟩
  step as ⟨Y1, hY10, hY11⟩
  have hY1b : Y1.LimbsLt 54 := by
    rcases hcnv with h | h
    · rw [hY10 h]; exact hYb
    · exact limbs_lt_of_le (by decide) (hY11 h).2
  step as ⟨fe9, hfe9, hfe9b⟩
  step as ⟨s, hs, hsb⟩
  step as ⟨sn, hsnv, hsn⟩
  have hsb' : s.LimbsLt 54 := limbs_lt_of_le (by decide) hsb
  step as ⟨s1, hs10, hs11⟩
  step as ⟨r, hr⟩
  -- the code's values as field elements
  have Fe : fe.toField = self.Z.toField + self.Y.toField := toField_add_of_limbs hfe
  have Fe1 : fe1.toField = self.Z.toField - self.Y.toField := toField_sub_of_mod hfe1
  have Inv : invsqrt.toField = (sqrtRatioM1 1 fe3.toField).2 := by
    rw [sqrtRatioM1_one_eq_of_spec hi0 (fun h ⟨x, hx⟩ => hi1 h x hx) hi2 hpar]
  have Fe5 : fe5.toField = sqrtM1 := by rw [toField_def, hfe5]
  have Fe6 : fe6.toField ^ 2 = (invsqrtAMinusD : ZMod p) ^ 2 := by
    have h := natCast_eq_natCast_of_mod_eq (hfe6.trans one_mod_p.symm)
    push_cast at h
    rw [ZMod.natCast_zmod_val, ← toField_def] at h
    have had : (a : ZMod p) - d ≠ 0 := fun h0 => by
      have h1 := invsqrtAMinusD_sq_mul
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    apply mul_right_cancel₀ had
    rw [h, invsqrtAMinusD_sq_mul]
  have Xsel : X.toField = if fe7.toField.isNeg then iY.toField else self.X.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hX0 h])
      (fun h => by rw [hX1 h])
  have Ysel : Y.toField = if fe7.toField.isNeg then iX.toField else self.Y.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hY0 h])
      (fun h => by rw [hY1 h])
  have I21sel : i21.toField = if fe7.toField.isNeg then ench.toField else i2.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hi210 h])
      (fun h => by rw [hi211 h])
  have Y1sel : Y1.toField = if fe8.toField.isNeg then -Y.toField else Y.toField :=
    eq_ite_of_choice hcnv (eq_one_iff_isNeg_toField hcn) (fun h => by rw [hY10 h])
      (fun h => toField_neg_of_mod (hY11 h).1)
  have S1 : s1.toField = s.toField.abs :=
    eq_ite_of_choice hsnv (eq_one_iff_isNeg_toField hsn) (fun h => by rw [hs10 h])
      (fun h => toField_neg_of_mod (hs11 h).1)
  rw [CompressedRistretto.asNat_def, hr, ← toField_val, S1,
    ← RistrettoCompress.compressProj_eq_encodeRep _ Fe6 hZ0 hXYZT hx hy]
  congr 1
  rw [toField_mul_of_mod hs, I21sel, toField_sub_of_mod hfe9, Y1sel, Ysel,
    toField_mul_of_mod hfe8, Xsel, toField_mul_of_mod hench, toField_mul_of_mod hfe7,
    toField_mul_of_mod hz,
    toField_mul_of_mod hfe4, toField_mul_of_mod hi1', toField_mul_of_mod hi2',
    toField_mul_of_mod hiY, toField_mul_of_mod hiX, Fe5, Inv, toField_mul_of_mod hfe3,
    toField_sq_of_mod hfe2, toField_mul_of_mod hu1, toField_mul_of_mod hu2, Fe, Fe1]
  rfl

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

open edwards.EdwardsPoint.«i686-tables» in
/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point; limbs `< 2^26`. -/
@[step]
theorem compress_spec (self : RistrettoPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.asNat = Ristretto.encodeRep self.toPoint ⦄ := by
  obtain ⟨hZ0, hXYZT, -⟩ := (onCurve_iff_equation self).mp hon
  have hx := toPoint_x hon
  have hy := toPoint_y hon
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold compress
  step as ⟨fe, hfe⟩
  step as ⟨fe1, hfe1, hfe1b⟩
  step as ⟨u1, hu1, hu1b⟩
  step as ⟨u2, hu2, hu2b⟩
  step as ⟨fe2, hfe2, hfe2b⟩
  step as ⟨fe3, hfe3, hfe3b⟩
  step as ⟨c0, invsqrt, hc0v, hi0, hi1, hi2, hpar, hib⟩
  step as ⟨i1, hi1', hi1b⟩
  step as ⟨i2, hi2', hi2b⟩
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨z_inv, hz, hzb⟩
  step as ⟨fe5, hfe5, hfe5b⟩
  step as ⟨iX, hiX, hiXb⟩
  step as ⟨iY, hiY, hiYb⟩
  step as ⟨fe6, hfe6lt, hfe6, hfe6b⟩
  step as ⟨ench, hench, henchb⟩
  step as ⟨fe7, hfe7, hfe7b⟩
  step as ⟨rot, hrotv, hrot⟩
  step as ⟨X, hX0, hX1⟩
  step as ⟨Y, hY0, hY1⟩
  step as ⟨i21, hi210, hi211⟩
  have hXb : X.LimbsLt 27 := by
    rcases hrotv with h | h
    · rw [hX0 h]; exact limbs_lt_of_le (by decide) hX
    · rw [hX1 h]; exact limbs_lt_of_le (by decide) hiYb
  have hYb : Y.LimbsLt 27 := by
    rcases hrotv with h | h
    · rw [hY0 h]; exact limbs_lt_of_le (by decide) hY
    · rw [hY1 h]; exact limbs_lt_of_le (by decide) hiXb
  have hi21b : i21.LimbsLt 27 := by
    rcases hrotv with h | h
    · rw [hi210 h]; exact limbs_lt_of_le (by decide) hi2b
    · rw [hi211 h]; exact limbs_lt_of_le (by decide) henchb
  step as ⟨fe8, hfe8, hfe8b⟩
  step as ⟨cn, hcnv, hcn⟩
  step as ⟨Y1, hY10, hY11⟩
  have hY1b : Y1.LimbsLt 27 := by
    rcases hcnv with h | h
    · rw [hY10 h]; exact hYb
    · exact limbs_lt_of_le (by decide) (hY11 h).2
  step as ⟨fe9, hfe9, hfe9b⟩
  step as ⟨s, hs, hsb⟩
  step as ⟨sn, hsnv, hsn⟩
  have hsb' : s.LimbsLt 28 := limbs_lt_of_le (by decide) hsb
  step as ⟨s1, hs10, hs11⟩
  step as ⟨r, hr⟩
  -- the code's values as field elements
  have Fe : fe.toField = self.Z.toField + self.Y.toField := toField_add_of_limbs hfe
  have Fe1 : fe1.toField = self.Z.toField - self.Y.toField := toField_sub_of_mod hfe1
  have Inv : invsqrt.toField = (sqrtRatioM1 1 fe3.toField).2 := by
    rw [sqrtRatioM1_one_eq_of_spec hi0 (fun h ⟨x, hx⟩ => hi1 h x hx) hi2 hpar]
  have Fe5 : fe5.toField = sqrtM1 := by rw [toField_def, hfe5]
  have Fe6 : fe6.toField ^ 2 = (invsqrtAMinusD : ZMod p) ^ 2 := by
    have h := natCast_eq_natCast_of_mod_eq (hfe6.trans one_mod_p.symm)
    push_cast at h
    rw [ZMod.natCast_zmod_val, ← toField_def] at h
    have had : (a : ZMod p) - d ≠ 0 := fun h0 => by
      have h1 := invsqrtAMinusD_sq_mul
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    apply mul_right_cancel₀ had
    rw [h, invsqrtAMinusD_sq_mul]
  have Xsel : X.toField = if fe7.toField.isNeg then iY.toField else self.X.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hX0 h])
      (fun h => by rw [hX1 h])
  have Ysel : Y.toField = if fe7.toField.isNeg then iX.toField else self.Y.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hY0 h])
      (fun h => by rw [hY1 h])
  have I21sel : i21.toField = if fe7.toField.isNeg then ench.toField else i2.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hi210 h])
      (fun h => by rw [hi211 h])
  have Y1sel : Y1.toField = if fe8.toField.isNeg then -Y.toField else Y.toField :=
    eq_ite_of_choice hcnv (eq_one_iff_isNeg_toField hcn) (fun h => by rw [hY10 h])
      (fun h => toField_neg_of_mod (hY11 h).1)
  have S1 : s1.toField = s.toField.abs :=
    eq_ite_of_choice hsnv (eq_one_iff_isNeg_toField hsn) (fun h => by rw [hs10 h])
      (fun h => toField_neg_of_mod (hs11 h).1)
  rw [CompressedRistretto.asNat_def, hr, ← toField_val, S1,
    ← RistrettoCompress.compressProj_eq_encodeRep _ Fe6 hZ0 hXYZT hx hy]
  congr 1
  rw [toField_mul_of_mod hs, I21sel, toField_sub_of_mod hfe9, Y1sel, Ysel,
    toField_mul_of_mod hfe8, Xsel, toField_mul_of_mod hench, toField_mul_of_mod hfe7,
    toField_mul_of_mod hz,
    toField_mul_of_mod hfe4, toField_mul_of_mod hi1', toField_mul_of_mod hi2',
    toField_mul_of_mod hiY, toField_mul_of_mod hiX, Fe5, Inv, toField_mul_of_mod hfe3,
    toField_sq_of_mod hfe2, toField_mul_of_mod hu1, toField_mul_of_mod hu2, Fe, Fe1]
  rfl

end «RistrettoPointi686-tables»

namespace «RistrettoPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

open edwards.EdwardsPoint.«x86_64-no-tables» in
/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point; limbs `< 2^52`. -/
@[step]
theorem compress_spec (self : RistrettoPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.asNat = Ristretto.encodeRep self.toPoint ⦄ := by
  obtain ⟨hZ0, hXYZT, -⟩ := (onCurve_iff_equation self).mp hon
  have hx := toPoint_x hon
  have hy := toPoint_y hon
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold compress
  step as ⟨fe, hfe⟩
  step as ⟨fe1, hfe1, hfe1b⟩
  step as ⟨u1, hu1, hu1b⟩
  step as ⟨u2, hu2, hu2b⟩
  step as ⟨fe2, hfe2, hfe2b⟩
  step as ⟨fe3, hfe3, hfe3b⟩
  step as ⟨c0, invsqrt, hc0v, hi0, hi1, hi2, hpar, hib⟩
  step as ⟨i1, hi1', hi1b⟩
  step as ⟨i2, hi2', hi2b⟩
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨z_inv, hz, hzb⟩
  step as ⟨fe5, hfe5, hfe5b⟩
  step as ⟨iX, hiX, hiXb⟩
  step as ⟨iY, hiY, hiYb⟩
  step as ⟨fe6, hfe6lt, hfe6, hfe6b⟩
  step as ⟨ench, hench, henchb⟩
  step as ⟨fe7, hfe7, hfe7b⟩
  step as ⟨rot, hrotv, hrot⟩
  step as ⟨X, hX0, hX1⟩
  step as ⟨Y, hY0, hY1⟩
  step as ⟨i21, hi210, hi211⟩
  have hXb : X.LimbsLt 54 := by
    rcases hrotv with h | h
    · rw [hX0 h]; exact limbs_lt_of_le (by decide) hX
    · rw [hX1 h]; exact limbs_lt_of_le (by decide) hiYb
  have hYb : Y.LimbsLt 54 := by
    rcases hrotv with h | h
    · rw [hY0 h]; exact limbs_lt_of_le (by decide) hY
    · rw [hY1 h]; exact limbs_lt_of_le (by decide) hiXb
  have hi21b : i21.LimbsLt 54 := by
    rcases hrotv with h | h
    · rw [hi210 h]; exact limbs_lt_of_le (by decide) hi2b
    · rw [hi211 h]; exact limbs_lt_of_le (by decide) henchb
  step as ⟨fe8, hfe8, hfe8b⟩
  step as ⟨cn, hcnv, hcn⟩
  step as ⟨Y1, hY10, hY11⟩
  have hY1b : Y1.LimbsLt 54 := by
    rcases hcnv with h | h
    · rw [hY10 h]; exact hYb
    · exact limbs_lt_of_le (by decide) (hY11 h).2
  step as ⟨fe9, hfe9, hfe9b⟩
  step as ⟨s, hs, hsb⟩
  step as ⟨sn, hsnv, hsn⟩
  have hsb' : s.LimbsLt 54 := limbs_lt_of_le (by decide) hsb
  step as ⟨s1, hs10, hs11⟩
  step as ⟨r, hr⟩
  -- the code's values as field elements
  have Fe : fe.toField = self.Z.toField + self.Y.toField := toField_add_of_limbs hfe
  have Fe1 : fe1.toField = self.Z.toField - self.Y.toField := toField_sub_of_mod hfe1
  have Inv : invsqrt.toField = (sqrtRatioM1 1 fe3.toField).2 := by
    rw [sqrtRatioM1_one_eq_of_spec hi0 (fun h ⟨x, hx⟩ => hi1 h x hx) hi2 hpar]
  have Fe5 : fe5.toField = sqrtM1 := by rw [toField_def, hfe5]
  have Fe6 : fe6.toField ^ 2 = (invsqrtAMinusD : ZMod p) ^ 2 := by
    have h := natCast_eq_natCast_of_mod_eq (hfe6.trans one_mod_p.symm)
    push_cast at h
    rw [ZMod.natCast_zmod_val, ← toField_def] at h
    have had : (a : ZMod p) - d ≠ 0 := fun h0 => by
      have h1 := invsqrtAMinusD_sq_mul
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    apply mul_right_cancel₀ had
    rw [h, invsqrtAMinusD_sq_mul]
  have Xsel : X.toField = if fe7.toField.isNeg then iY.toField else self.X.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hX0 h])
      (fun h => by rw [hX1 h])
  have Ysel : Y.toField = if fe7.toField.isNeg then iX.toField else self.Y.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hY0 h])
      (fun h => by rw [hY1 h])
  have I21sel : i21.toField = if fe7.toField.isNeg then ench.toField else i2.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hi210 h])
      (fun h => by rw [hi211 h])
  have Y1sel : Y1.toField = if fe8.toField.isNeg then -Y.toField else Y.toField :=
    eq_ite_of_choice hcnv (eq_one_iff_isNeg_toField hcn) (fun h => by rw [hY10 h])
      (fun h => toField_neg_of_mod (hY11 h).1)
  have S1 : s1.toField = s.toField.abs :=
    eq_ite_of_choice hsnv (eq_one_iff_isNeg_toField hsn) (fun h => by rw [hs10 h])
      (fun h => toField_neg_of_mod (hs11 h).1)
  rw [CompressedRistretto.asNat_def, hr, ← toField_val, S1,
    ← RistrettoCompress.compressProj_eq_encodeRep _ Fe6 hZ0 hXYZT hx hy]
  congr 1
  rw [toField_mul_of_mod hs, I21sel, toField_sub_of_mod hfe9, Y1sel, Ysel,
    toField_mul_of_mod hfe8, Xsel, toField_mul_of_mod hench, toField_mul_of_mod hfe7,
    toField_mul_of_mod hz,
    toField_mul_of_mod hfe4, toField_mul_of_mod hi1', toField_mul_of_mod hi2',
    toField_mul_of_mod hiY, toField_mul_of_mod hiX, Fe5, Inv, toField_mul_of_mod hfe3,
    toField_sq_of_mod hfe2, toField_mul_of_mod hu1, toField_mul_of_mod hu2, Fe, Fe1]
  rfl

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

open edwards.EdwardsPoint.«i686-no-tables» in
/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point; limbs `< 2^26`. -/
@[step]
theorem compress_spec (self : RistrettoPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.asNat = Ristretto.encodeRep self.toPoint ⦄ := by
  obtain ⟨hZ0, hXYZT, -⟩ := (onCurve_iff_equation self).mp hon
  have hx := toPoint_x hon
  have hy := toPoint_y hon
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold compress
  step as ⟨fe, hfe⟩
  step as ⟨fe1, hfe1, hfe1b⟩
  step as ⟨u1, hu1, hu1b⟩
  step as ⟨u2, hu2, hu2b⟩
  step as ⟨fe2, hfe2, hfe2b⟩
  step as ⟨fe3, hfe3, hfe3b⟩
  step as ⟨c0, invsqrt, hc0v, hi0, hi1, hi2, hpar, hib⟩
  step as ⟨i1, hi1', hi1b⟩
  step as ⟨i2, hi2', hi2b⟩
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨z_inv, hz, hzb⟩
  step as ⟨fe5, hfe5, hfe5b⟩
  step as ⟨iX, hiX, hiXb⟩
  step as ⟨iY, hiY, hiYb⟩
  step as ⟨fe6, hfe6lt, hfe6, hfe6b⟩
  step as ⟨ench, hench, henchb⟩
  step as ⟨fe7, hfe7, hfe7b⟩
  step as ⟨rot, hrotv, hrot⟩
  step as ⟨X, hX0, hX1⟩
  step as ⟨Y, hY0, hY1⟩
  step as ⟨i21, hi210, hi211⟩
  have hXb : X.LimbsLt 27 := by
    rcases hrotv with h | h
    · rw [hX0 h]; exact limbs_lt_of_le (by decide) hX
    · rw [hX1 h]; exact limbs_lt_of_le (by decide) hiYb
  have hYb : Y.LimbsLt 27 := by
    rcases hrotv with h | h
    · rw [hY0 h]; exact limbs_lt_of_le (by decide) hY
    · rw [hY1 h]; exact limbs_lt_of_le (by decide) hiXb
  have hi21b : i21.LimbsLt 27 := by
    rcases hrotv with h | h
    · rw [hi210 h]; exact limbs_lt_of_le (by decide) hi2b
    · rw [hi211 h]; exact limbs_lt_of_le (by decide) henchb
  step as ⟨fe8, hfe8, hfe8b⟩
  step as ⟨cn, hcnv, hcn⟩
  step as ⟨Y1, hY10, hY11⟩
  have hY1b : Y1.LimbsLt 27 := by
    rcases hcnv with h | h
    · rw [hY10 h]; exact hYb
    · exact limbs_lt_of_le (by decide) (hY11 h).2
  step as ⟨fe9, hfe9, hfe9b⟩
  step as ⟨s, hs, hsb⟩
  step as ⟨sn, hsnv, hsn⟩
  have hsb' : s.LimbsLt 28 := limbs_lt_of_le (by decide) hsb
  step as ⟨s1, hs10, hs11⟩
  step as ⟨r, hr⟩
  -- the code's values as field elements
  have Fe : fe.toField = self.Z.toField + self.Y.toField := toField_add_of_limbs hfe
  have Fe1 : fe1.toField = self.Z.toField - self.Y.toField := toField_sub_of_mod hfe1
  have Inv : invsqrt.toField = (sqrtRatioM1 1 fe3.toField).2 := by
    rw [sqrtRatioM1_one_eq_of_spec hi0 (fun h ⟨x, hx⟩ => hi1 h x hx) hi2 hpar]
  have Fe5 : fe5.toField = sqrtM1 := by rw [toField_def, hfe5]
  have Fe6 : fe6.toField ^ 2 = (invsqrtAMinusD : ZMod p) ^ 2 := by
    have h := natCast_eq_natCast_of_mod_eq (hfe6.trans one_mod_p.symm)
    push_cast at h
    rw [ZMod.natCast_zmod_val, ← toField_def] at h
    have had : (a : ZMod p) - d ≠ 0 := fun h0 => by
      have h1 := invsqrtAMinusD_sq_mul
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    apply mul_right_cancel₀ had
    rw [h, invsqrtAMinusD_sq_mul]
  have Xsel : X.toField = if fe7.toField.isNeg then iY.toField else self.X.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hX0 h])
      (fun h => by rw [hX1 h])
  have Ysel : Y.toField = if fe7.toField.isNeg then iX.toField else self.Y.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hY0 h])
      (fun h => by rw [hY1 h])
  have I21sel : i21.toField = if fe7.toField.isNeg then ench.toField else i2.toField :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg_toField hrot) (fun h => by rw [hi210 h])
      (fun h => by rw [hi211 h])
  have Y1sel : Y1.toField = if fe8.toField.isNeg then -Y.toField else Y.toField :=
    eq_ite_of_choice hcnv (eq_one_iff_isNeg_toField hcn) (fun h => by rw [hY10 h])
      (fun h => toField_neg_of_mod (hY11 h).1)
  have S1 : s1.toField = s.toField.abs :=
    eq_ite_of_choice hsnv (eq_one_iff_isNeg_toField hsn) (fun h => by rw [hs10 h])
      (fun h => toField_neg_of_mod (hs11 h).1)
  rw [CompressedRistretto.asNat_def, hr, ← toField_val, S1,
    ← RistrettoCompress.compressProj_eq_encodeRep _ Fe6 hZ0 hXYZT hx hy]
  congr 1
  rw [toField_mul_of_mod hs, I21sel, toField_sub_of_mod hfe9, Y1sel, Ysel,
    toField_mul_of_mod hfe8, Xsel, toField_mul_of_mod hench, toField_mul_of_mod hfe7,
    toField_mul_of_mod hz,
    toField_mul_of_mod hfe4, toField_mul_of_mod hi1', toField_mul_of_mod hi2',
    toField_mul_of_mod hiY, toField_mul_of_mod hiX, Fe5, Inv, toField_mul_of_mod hfe3,
    toField_sq_of_mod hfe2, toField_mul_of_mod hu1, toField_mul_of_mod hu2, Fe, Fe1]
  rfl

end «RistrettoPointi686-no-tables»

end Curve25519Dalek.ristretto
