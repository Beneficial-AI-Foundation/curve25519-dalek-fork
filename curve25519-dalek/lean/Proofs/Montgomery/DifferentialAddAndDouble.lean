/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
import Proofs.Backend.Serial.U64.Constants.Aplus2OverFour
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Constants.Aplus2OverFour
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Square
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Helpers.ToField2625
public section

/-! # `differential_add_and_double`

The step of the Montgomery ladder on the `x`-only projective points: `P ↦ xDBL P` and
`Q ↦ xADD P Q u(P - Q)`, matching RFC 7748's formulas `MontgomeryModel.XZ.dbl`,
`MontgomeryModel.XZ.add` exactly as field elements. The code's doubling uses
`APLUS2_OVER_FOUR = (A + 2) / 4` with `BB`, the RFC's `a24 = (A - 2) / 4` with `AA = BB + E`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.montgomery

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `APLUS2_OVER_FOUR = (A + 2) / 4` is the RFC's `a24 = (A - 2) / 4` plus one. -/
private theorem aplus2_toField {c : FieldElement51} (h : c.asNat * 4 = A + 2) :
    c.toField = montgomery.a24 + 1 := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero two_ne_zero two_ne_zero
  have hc : c.toField * 4 = (A : ZMod p) + 2 := by
    rw [toField_def]
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod p)) h
  rw [MontgomeryModel.a24, montgomery_A]
  field_simp
  rw [hc]
  ring

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `APLUS2_OVER_FOUR = (A + 2) / 4` is the RFC's `a24 = (A - 2) / 4` plus one. -/
private theorem aplus2_toField_u32 {c : FieldElement2625} (h : c.asNat * 4 = A + 2) :
    c.toField = montgomery.a24 + 1 := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero two_ne_zero two_ne_zero
  have hc : c.toField * 4 = (A : ZMod p) + 2 := by
    rw [toField_def]
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod p)) h
  rw [MontgomeryModel.a24, montgomery_A]
  field_simp
  rw [hc]
  ring

namespace «x86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `differential_add_and_double`: one step of the ladder on `(U : W)` coordinates,
`P ↦ xDBL P` and `Q ↦ xADD P Q u(P - Q)` exactly (RFC 7748 §5); limbs `< 2^52`. -/
@[step]
theorem differential_add_and_double_spec (P Q : ProjectivePoint.«x86_64-tables»)
    (affine_PmQ : FieldElement51) (hP : P.LimbsLt 52) (hQ : Q.LimbsLt 52)
    (haffine_PmQ : affine_PmQ.LimbsLt 54) :
    differential_add_and_double.«x86_64-tables» P Q affine_PmQ
      ⦃ (P' Q' : ProjectivePoint.«x86_64-tables») =>
        P'.toXZ = MontgomeryModel.XZ.dbl montgomery.a24 P.toXZ ∧
        Q'.toXZ = MontgomeryModel.XZ.add P.toXZ Q.toXZ affine_PmQ.toField ∧
        P'.LimbsLt 52 ∧ Q'.LimbsLt 52 ⦄ := by
  obtain ⟨hPU, hPW⟩ := hP
  obtain ⟨hQU, hQW⟩ := hQ
  unfold differential_add_and_double.«x86_64-tables»
  step as ⟨t0, ht0⟩
  step as ⟨t1, ht1, ht1_lt⟩
  step as ⟨t2, ht2⟩
  step as ⟨t3, ht3, ht3_lt⟩
  step as ⟨t4, ht4, ht4_lt⟩
  step as ⟨t5, ht5, ht5_lt⟩
  step as ⟨t6, ht6, ht6_lt⟩
  step as ⟨t7, ht7, ht7_lt⟩
  step as ⟨t8, ht8, ht8_lt⟩
  step as ⟨t9, ht9⟩
  step as ⟨t10, ht10, ht10_lt⟩
  step as ⟨t11, ht11, ht11_lt⟩
  step as ⟨t12, ht12, ht12_lt⟩
  step as ⟨c, hc, hc_lt⟩
  step as ⟨t13, ht13, ht13_lt⟩
  step as ⟨t14, ht14, ht14_lt⟩
  step as ⟨t15, ht15⟩
  step as ⟨t16, ht16, ht16_lt⟩
  step as ⟨t17, ht17, ht17_lt⟩
  refine ⟨?_, ?_, ⟨ht14_lt, ht16_lt⟩, ⟨ht11_lt, ht17_lt⟩⟩
  · simp only [ProjectivePoint.«x86_64-tables».toXZ_def, MontgomeryModel.XZ.dbl,
      toField_mul_of_mod ht14, toField_mul_of_mod ht16, toField_add_of_limbs ht15,
      toField_mul_of_mod ht13, toField_sub_of_mod ht6, toField_sq_of_mod ht4,
      toField_sq_of_mod ht5, toField_add_of_limbs ht0, toField_sub_of_mod ht1,
      aplus2_toField hc]
    ring_nf
  · simp only [ProjectivePoint.«x86_64-tables».toXZ_def, MontgomeryModel.XZ.add,
      toField_sq_of_mod ht11, toField_mul_of_mod ht17, toField_sq_of_mod ht12,
      toField_add_of_limbs ht9, toField_sub_of_mod ht10, toField_mul_of_mod ht7,
      toField_mul_of_mod ht8, toField_add_of_limbs ht0, toField_sub_of_mod ht1,
      toField_add_of_limbs ht2, toField_sub_of_mod ht3]
    ring_nf

end «x86_64-tables»

namespace «i686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `differential_add_and_double`: one step of the ladder on `(U : W)` coordinates,
`P ↦ xDBL P` and `Q ↦ xADD P Q u(P - Q)` exactly (RFC 7748 §5); limbs `< 2^26`. -/
@[step]
theorem differential_add_and_double_spec (P Q : ProjectivePoint.«i686-tables»)
    (affine_PmQ : FieldElement2625) (hP : P.LimbsLt 26) (hQ : Q.LimbsLt 26)
    (haffine_PmQ : affine_PmQ.LimbsLt 27) :
    differential_add_and_double.«i686-tables» P Q affine_PmQ
      ⦃ (P' Q' : ProjectivePoint.«i686-tables») =>
        P'.toXZ = MontgomeryModel.XZ.dbl montgomery.a24 P.toXZ ∧
        Q'.toXZ = MontgomeryModel.XZ.add P.toXZ Q.toXZ affine_PmQ.toField ∧
        P'.LimbsLt 26 ∧ Q'.LimbsLt 26 ⦄ := by
  obtain ⟨hPU, hPW⟩ := hP
  obtain ⟨hQU, hQW⟩ := hQ
  unfold differential_add_and_double.«i686-tables»
  step as ⟨t0, ht0⟩
  step as ⟨t1, ht1, ht1_lt⟩
  step as ⟨t2, ht2⟩
  step as ⟨t3, ht3, ht3_lt⟩
  step as ⟨t4, ht4, ht4_lt⟩
  step as ⟨t5, ht5, ht5_lt⟩
  step as ⟨t6, ht6, ht6_lt⟩
  step as ⟨t7, ht7, ht7_lt⟩
  step as ⟨t8, ht8, ht8_lt⟩
  step as ⟨t9, ht9⟩
  step as ⟨t10, ht10, ht10_lt⟩
  step as ⟨t11, ht11, ht11_lt⟩
  step as ⟨t12, ht12, ht12_lt⟩
  step as ⟨c, hc, hc_lt⟩
  step as ⟨t13, ht13, ht13_lt⟩
  step as ⟨t14, ht14, ht14_lt⟩
  step as ⟨t15, ht15⟩
  step as ⟨t16, ht16, ht16_lt⟩
  step as ⟨t17, ht17, ht17_lt⟩
  refine ⟨?_, ?_, ⟨ht14_lt, ht16_lt⟩, ⟨ht11_lt, ht17_lt⟩⟩
  · simp only [ProjectivePoint.«i686-tables».toXZ_def, MontgomeryModel.XZ.dbl,
      toField_mul_of_mod ht14, toField_mul_of_mod ht16, toField_add_of_limbs ht15,
      toField_mul_of_mod ht13, toField_sub_of_mod ht6, toField_sq_of_mod ht4,
      toField_sq_of_mod ht5, toField_add_of_limbs ht0, toField_sub_of_mod ht1,
      aplus2_toField_u32 hc]
    ring_nf
  · simp only [ProjectivePoint.«i686-tables».toXZ_def, MontgomeryModel.XZ.add,
      toField_sq_of_mod ht11, toField_mul_of_mod ht17, toField_sq_of_mod ht12,
      toField_add_of_limbs ht9, toField_sub_of_mod ht10, toField_mul_of_mod ht7,
      toField_mul_of_mod ht8, toField_add_of_limbs ht0, toField_sub_of_mod ht1,
      toField_add_of_limbs ht2, toField_sub_of_mod ht3]
    ring_nf

end «i686-tables»

namespace «x86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `differential_add_and_double`: one step of the ladder on `(U : W)` coordinates,
`P ↦ xDBL P` and `Q ↦ xADD P Q u(P - Q)` exactly (RFC 7748 §5); limbs `< 2^52`. -/
@[step]
theorem differential_add_and_double_spec (P Q : ProjectivePoint.«x86_64-no-tables»)
    (affine_PmQ : FieldElement51) (hP : P.LimbsLt 52) (hQ : Q.LimbsLt 52)
    (haffine_PmQ : affine_PmQ.LimbsLt 54) :
    differential_add_and_double.«x86_64-no-tables» P Q affine_PmQ
      ⦃ (P' Q' : ProjectivePoint.«x86_64-no-tables») =>
        P'.toXZ = MontgomeryModel.XZ.dbl montgomery.a24 P.toXZ ∧
        Q'.toXZ = MontgomeryModel.XZ.add P.toXZ Q.toXZ affine_PmQ.toField ∧
        P'.LimbsLt 52 ∧ Q'.LimbsLt 52 ⦄ := by
  obtain ⟨hPU, hPW⟩ := hP
  obtain ⟨hQU, hQW⟩ := hQ
  unfold differential_add_and_double.«x86_64-no-tables»
  step as ⟨t0, ht0⟩
  step as ⟨t1, ht1, ht1_lt⟩
  step as ⟨t2, ht2⟩
  step as ⟨t3, ht3, ht3_lt⟩
  step as ⟨t4, ht4, ht4_lt⟩
  step as ⟨t5, ht5, ht5_lt⟩
  step as ⟨t6, ht6, ht6_lt⟩
  step as ⟨t7, ht7, ht7_lt⟩
  step as ⟨t8, ht8, ht8_lt⟩
  step as ⟨t9, ht9⟩
  step as ⟨t10, ht10, ht10_lt⟩
  step as ⟨t11, ht11, ht11_lt⟩
  step as ⟨t12, ht12, ht12_lt⟩
  step as ⟨c, hc, hc_lt⟩
  step as ⟨t13, ht13, ht13_lt⟩
  step as ⟨t14, ht14, ht14_lt⟩
  step as ⟨t15, ht15⟩
  step as ⟨t16, ht16, ht16_lt⟩
  step as ⟨t17, ht17, ht17_lt⟩
  refine ⟨?_, ?_, ⟨ht14_lt, ht16_lt⟩, ⟨ht11_lt, ht17_lt⟩⟩
  · simp only [ProjectivePoint.«x86_64-no-tables».toXZ_def, MontgomeryModel.XZ.dbl,
      toField_mul_of_mod ht14, toField_mul_of_mod ht16, toField_add_of_limbs ht15,
      toField_mul_of_mod ht13, toField_sub_of_mod ht6, toField_sq_of_mod ht4,
      toField_sq_of_mod ht5, toField_add_of_limbs ht0, toField_sub_of_mod ht1,
      aplus2_toField hc]
    ring_nf
  · simp only [ProjectivePoint.«x86_64-no-tables».toXZ_def, MontgomeryModel.XZ.add,
      toField_sq_of_mod ht11, toField_mul_of_mod ht17, toField_sq_of_mod ht12,
      toField_add_of_limbs ht9, toField_sub_of_mod ht10, toField_mul_of_mod ht7,
      toField_mul_of_mod ht8, toField_add_of_limbs ht0, toField_sub_of_mod ht1,
      toField_add_of_limbs ht2, toField_sub_of_mod ht3]
    ring_nf

end «x86_64-no-tables»

namespace «i686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `differential_add_and_double`: one step of the ladder on `(U : W)` coordinates,
`P ↦ xDBL P` and `Q ↦ xADD P Q u(P - Q)` exactly (RFC 7748 §5); limbs `< 2^26`. -/
@[step]
theorem differential_add_and_double_spec (P Q : ProjectivePoint.«i686-no-tables»)
    (affine_PmQ : FieldElement2625) (hP : P.LimbsLt 26) (hQ : Q.LimbsLt 26)
    (haffine_PmQ : affine_PmQ.LimbsLt 27) :
    differential_add_and_double.«i686-no-tables» P Q affine_PmQ
      ⦃ (P' Q' : ProjectivePoint.«i686-no-tables») =>
        P'.toXZ = MontgomeryModel.XZ.dbl montgomery.a24 P.toXZ ∧
        Q'.toXZ = MontgomeryModel.XZ.add P.toXZ Q.toXZ affine_PmQ.toField ∧
        P'.LimbsLt 26 ∧ Q'.LimbsLt 26 ⦄ := by
  obtain ⟨hPU, hPW⟩ := hP
  obtain ⟨hQU, hQW⟩ := hQ
  unfold differential_add_and_double.«i686-no-tables»
  step as ⟨t0, ht0⟩
  step as ⟨t1, ht1, ht1_lt⟩
  step as ⟨t2, ht2⟩
  step as ⟨t3, ht3, ht3_lt⟩
  step as ⟨t4, ht4, ht4_lt⟩
  step as ⟨t5, ht5, ht5_lt⟩
  step as ⟨t6, ht6, ht6_lt⟩
  step as ⟨t7, ht7, ht7_lt⟩
  step as ⟨t8, ht8, ht8_lt⟩
  step as ⟨t9, ht9⟩
  step as ⟨t10, ht10, ht10_lt⟩
  step as ⟨t11, ht11, ht11_lt⟩
  step as ⟨t12, ht12, ht12_lt⟩
  step as ⟨c, hc, hc_lt⟩
  step as ⟨t13, ht13, ht13_lt⟩
  step as ⟨t14, ht14, ht14_lt⟩
  step as ⟨t15, ht15⟩
  step as ⟨t16, ht16, ht16_lt⟩
  step as ⟨t17, ht17, ht17_lt⟩
  refine ⟨?_, ?_, ⟨ht14_lt, ht16_lt⟩, ⟨ht11_lt, ht17_lt⟩⟩
  · simp only [ProjectivePoint.«i686-no-tables».toXZ_def, MontgomeryModel.XZ.dbl,
      toField_mul_of_mod ht14, toField_mul_of_mod ht16, toField_add_of_limbs ht15,
      toField_mul_of_mod ht13, toField_sub_of_mod ht6, toField_sq_of_mod ht4,
      toField_sq_of_mod ht5, toField_add_of_limbs ht0, toField_sub_of_mod ht1,
      aplus2_toField_u32 hc]
    ring_nf
  · simp only [ProjectivePoint.«i686-no-tables».toXZ_def, MontgomeryModel.XZ.add,
      toField_sq_of_mod ht11, toField_mul_of_mod ht17, toField_sq_of_mod ht12,
      toField_add_of_limbs ht9, toField_sub_of_mod ht10, toField_mul_of_mod ht7,
      toField_mul_of_mod ht8, toField_add_of_limbs ht0, toField_sub_of_mod ht1,
      toField_add_of_limbs ht2, toField_sub_of_mod ht3]
    ring_nf

end «i686-no-tables»

end Curve25519Dalek.montgomery
