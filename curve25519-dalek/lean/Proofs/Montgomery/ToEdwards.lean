/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Montgomery
import Proofs.Backend.Serial.U64.Field.MinusOne
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Edwards.Decompress
import Proofs.Field.Eq
import Proofs.Field.Invert
import Proofs.Helpers.AsNat
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.MinusOne
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.FromBytes
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Backend.Serial.U32.Field.ToBytes
import Proofs.Helpers.ToField2625
public section

/-! # `MontgomeryPoint::to_edwards`

The birational map `y = (u - 1) / (u + 1)` from the Montgomery `u`-line to the Edwards
`y`-line, followed by `CompressedEdwardsY::decompress` of the canonical bytes of `y` with the sign
bit set to `sign mod 2` (`sign << 7` keeps only bit `0` of `sign`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.montgomery.MontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- Changing only the top byte of 32 bytes changes their value by `2^248` times the change. -/
private theorem asNat_of_eq_but_top (a b : Array U8 32#usize) (h : ∀ j, j ≠ 31 → b[j]! = a[j]!) :
    b.asNat 8 + 2 ^ 248 * a[31]!.val = a.asNat 8 + 2 ^ 248 * b[31]!.val := by
  rw [Array.asNat_eq_sum, Array.asNat_eq_sum, show (32#usize).val = 31 + 1 from rfl,
    Finset.sum_range_succ (fun x => 2 ^ (8 * x) * b[x]!.val) 31,
    Finset.sum_range_succ (fun x => 2 ^ (8 * x) * a[x]!.val) 31]
  have hs : ∑ x ∈ Finset.range 31, 2 ^ (8 * x) * b[x]!.val =
      ∑ x ∈ Finset.range 31, 2 ^ (8 * x) * a[x]!.val :=
    Finset.sum_congr rfl fun x hx => by rw [h x (by simp at hx; omega)]
  rw [hs]
  ring

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The top byte of a value below `2^255` is below `2^7`. -/
private theorem top_byte_lt (a : Array U8 32#usize) (ha : a.asNat 8 < 2 ^ 255) :
    a[31]!.val < 2 ^ 7 := by
  rw [← Array.asNat_div_pow_mod 8 a (fun i _ => a[i]!.hBounds) 31]
  calc a.asNat 8 / 2 ^ (8 * 31) % 2 ^ 8 ≤ a.asNat 8 / 2 ^ (8 * 31) := Nat.mod_le _ _
    _ < 2 ^ 7 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; calc
        a.asNat 8 < 2 ^ 255 := ha
        _ = 2 ^ 7 * 2 ^ (8 * 31) := by norm_num

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- Setting bit `7` of a byte below `2^7` adds `2^7`. -/
private theorem xor_top_bit (b c : ℕ) (hb : b < 2 ^ 7) (hc : c < 2) :
    b ^^^ (2 ^ 7 * c) = b + 2 ^ 7 * c := by
  interval_cases c
  · simp
  · revert b; decide

open scoped Helpers.IndexStep Helpers.UpdateStep in
open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
@[step]
theorem to_edwards.«x86_64-tables_spec» (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«x86_64-tables» self sign ⦃ (r : Option (edwards.EdwardsPoint.«x86_64-tables»)) =>
      (self.u = -1 → r = none) ∧
      (self.u ≠ -1 → r.map edwards.EdwardsPoint.«x86_64-tables».toPoint =
        Curve25519Dalek.edwards.decodeLenient (encodeU ((self.u - 1) / (self.u + 1)) + 2 ^ 255 *
            (sign.val % 2))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  unfold to_edwards.«x86_64-tables»
  step as ⟨u, hu, hu_lt⟩
  step as ⟨m1, hm1, hm1_lt⟩
  step with backend.serial.u64.field.FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq_spec
    u m1 as ⟨b, hb⟩
  have hU : u.toField = self.u := by
    rw [MontgomeryPoint.u_def, decodeU, toField_def, hu, MontgomeryPoint.asNat_def]
  have hm1' : m1.toField = -1 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hm1
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h
    rw [toField_def]
    exact eq_neg_of_add_eq_zero_left h
  have hb' : b = true ↔ self.u = -1 := by
    rw [hb, ← hU, ← hm1', ← toField_eq_toField_iff]
  split
  · next hbt =>
    have hu1 : self.u = -1 := hb'.mp hbt
    rw [WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd hu1 h, fun q hq => by cases hq⟩
  · next hbf =>
    have hu1 : self.u ≠ -1 := fun h => hbf (hb'.mpr h)
    step as ⟨one, one_post, one_lt⟩
    step as ⟨fe1, fe1_post, fe1_lt⟩
    step as ⟨fe2, fe2_post⟩
    step as ⟨fe3, fe3_post, fe3_post1, fe3_lt⟩
    step as ⟨y, y_post, y_lt⟩
    step as ⟨y_bytes, y_bytes_post⟩
    step as ⟨i, i_post, i_bv⟩
    step as ⟨i1, i1_post⟩
    step as ⟨i2, i2_val, i2_bv⟩
    step as ⟨y_bytes1, y31, y_rest⟩
    step as ⟨r, r_post, r_post1⟩
    refine ⟨fun h => absurd h hu1, fun _ => ?_, r_post1⟩
    rw [r_post]
    congr 1
    -- the value of the bytes: the canonical `y` with the sign in bit `255`
    have hy : y.toField = (self.u - 1) / (self.u + 1) := by
      rw [toField_mul_of_mod y_post, toField_sub_of_mod fe1_post, toField_inv_of_mod fe3_post
          fe3_post1,
        toField_add_of_limbs fe2_post, toField_eq_one_of_asNat one_post, hU, div_eq_mul_inv]
    have hyb : y_bytes.asNat 8 = encodeU ((self.u - 1) / (self.u + 1)) := by
      rw [y_bytes_post, ← hy, encodeU, toField_val]
    have htop := top_byte_lt y_bytes (by rw [hyb]; exact lt_trans (encodeU_lt _) p_lt_two_pow_255)
    have hi : i.val = 2 ^ 7 * (sign.val % 2) := by
      rw [i_post, Nat.shiftLeft_eq, show U8.size = 2 ^ 7 * 2 by simp [U8.size, U8.numBits],
          Nat.mul_comm _ (2 ^ 7),
        Nat.mul_mod_mul_left]
    have hi2 : i2.val = y_bytes[31]!.val + 2 ^ 7 * (sign.val % 2) := by
      rw [i2_val, UScalar.val_xor, i1_post, hi]
      exact xor_top_bit _ _ htop (Nat.mod_lt _ (by norm_num))
    have hset := asNat_of_eq_but_top y_bytes y_bytes1 y_rest
    rw [y31, hi2] at hset
    rw [edwards.CompressedEdwardsY.asNat_def, ← hyb]
    omega

open scoped Helpers.IndexStep Helpers.UpdateStep in
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
@[step]
theorem to_edwards.«i686-tables_spec» (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«i686-tables» self sign ⦃ (r : Option (edwards.EdwardsPoint.«i686-tables»)) =>
      (self.u = -1 → r = none) ∧
      (self.u ≠ -1 → r.map edwards.EdwardsPoint.«i686-tables».toPoint =
        Curve25519Dalek.edwards.decodeLenient (encodeU ((self.u - 1) / (self.u + 1)) + 2 ^ 255 *
            (sign.val % 2))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄ := by
  unfold to_edwards.«i686-tables»
  step as ⟨u, hu, hu_lt⟩
  step as ⟨m1, hm1, hm1_lt⟩
  step with backend.serial.u32.field.FieldElement2625.Insts.CoreCmpPartialEqFieldElement2625.eq_spec
    u m1 as ⟨b, hb⟩
  have hU : u.toField = self.u := by
    rw [MontgomeryPoint.u_def, decodeU, toField_def, MontgomeryPoint.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hu
  have hm1' : m1.toField = -1 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hm1
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h
    rw [toField_def]
    exact eq_neg_of_add_eq_zero_left h
  have hb' : b = true ↔ self.u = -1 := by
    rw [hb, ← hU, ← hm1', ← toField_eq_toField_iff]
  split
  · next hbt =>
    have hu1 : self.u = -1 := hb'.mp hbt
    rw [WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd hu1 h, fun q hq => by cases hq⟩
  · next hbf =>
    have hu1 : self.u ≠ -1 := fun h => hbf (hb'.mpr h)
    step as ⟨one, one_post, one_lt⟩
    step as ⟨fe1, fe1_post, fe1_lt⟩
    step as ⟨fe2, fe2_post⟩
    step as ⟨fe3, fe3_post, fe3_post1, fe3_lt⟩
    step as ⟨y, y_post, y_lt⟩
    step as ⟨y_bytes, y_bytes_post⟩
    step as ⟨i, i_post, i_bv⟩
    step as ⟨i1, i1_post⟩
    step as ⟨i2, i2_val, i2_bv⟩
    step as ⟨y_bytes1, y31, y_rest⟩
    step as ⟨r, r_post, r_post1⟩
    refine ⟨fun h => absurd h hu1, fun _ => ?_, r_post1⟩
    rw [r_post]
    congr 1
    -- the value of the bytes: the canonical `y` with the sign in bit `255`
    have hy : y.toField = (self.u - 1) / (self.u + 1) := by
      rw [toField_mul_of_mod y_post, toField_sub_of_mod fe1_post, toField_inv_of_mod fe3_post
          fe3_post1,
        toField_add_of_limbs fe2_post, toField_eq_one_of_asNat one_post, hU, div_eq_mul_inv]
    have hyb : y_bytes.asNat 8 = encodeU ((self.u - 1) / (self.u + 1)) := by
      rw [y_bytes_post, ← hy, encodeU, toField_val]
    have htop := top_byte_lt y_bytes (by rw [hyb]; exact lt_trans (encodeU_lt _) p_lt_two_pow_255)
    have hi : i.val = 2 ^ 7 * (sign.val % 2) := by
      rw [i_post, Nat.shiftLeft_eq, show U8.size = 2 ^ 7 * 2 by simp [U8.size, U8.numBits],
          Nat.mul_comm _ (2 ^ 7),
        Nat.mul_mod_mul_left]
    have hi2 : i2.val = y_bytes[31]!.val + 2 ^ 7 * (sign.val % 2) := by
      rw [i2_val, UScalar.val_xor, i1_post, hi]
      exact xor_top_bit _ _ htop (Nat.mod_lt _ (by norm_num))
    have hset := asNat_of_eq_but_top y_bytes y_bytes1 y_rest
    rw [y31, hi2] at hset
    rw [edwards.CompressedEdwardsY.asNat_def, ← hyb]
    omega

open scoped Helpers.IndexStep Helpers.UpdateStep in
open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
@[step]
theorem to_edwards.«x86_64-no-tables_spec» (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«x86_64-no-tables» self sign ⦃ (r : Option (edwards.EdwardsPoint.«x86_64-no-tables»))
        =>
      (self.u = -1 → r = none) ∧
      (self.u ≠ -1 → r.map edwards.EdwardsPoint.«x86_64-no-tables».toPoint =
        Curve25519Dalek.edwards.decodeLenient (encodeU ((self.u - 1) / (self.u + 1)) + 2 ^ 255 *
            (sign.val % 2))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  unfold to_edwards.«x86_64-no-tables»
  step as ⟨u, hu, hu_lt⟩
  step as ⟨m1, hm1, hm1_lt⟩
  step with backend.serial.u64.field.FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq_spec
    u m1 as ⟨b, hb⟩
  have hU : u.toField = self.u := by
    rw [MontgomeryPoint.u_def, decodeU, toField_def, hu, MontgomeryPoint.asNat_def]
  have hm1' : m1.toField = -1 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hm1
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h
    rw [toField_def]
    exact eq_neg_of_add_eq_zero_left h
  have hb' : b = true ↔ self.u = -1 := by
    rw [hb, ← hU, ← hm1', ← toField_eq_toField_iff]
  split
  · next hbt =>
    have hu1 : self.u = -1 := hb'.mp hbt
    rw [WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd hu1 h, fun q hq => by cases hq⟩
  · next hbf =>
    have hu1 : self.u ≠ -1 := fun h => hbf (hb'.mpr h)
    step as ⟨one, one_post, one_lt⟩
    step as ⟨fe1, fe1_post, fe1_lt⟩
    step as ⟨fe2, fe2_post⟩
    step as ⟨fe3, fe3_post, fe3_post1, fe3_lt⟩
    step as ⟨y, y_post, y_lt⟩
    step as ⟨y_bytes, y_bytes_post⟩
    step as ⟨i, i_post, i_bv⟩
    step as ⟨i1, i1_post⟩
    step as ⟨i2, i2_val, i2_bv⟩
    step as ⟨y_bytes1, y31, y_rest⟩
    step as ⟨r, r_post, r_post1⟩
    refine ⟨fun h => absurd h hu1, fun _ => ?_, r_post1⟩
    rw [r_post]
    congr 1
    -- the value of the bytes: the canonical `y` with the sign in bit `255`
    have hy : y.toField = (self.u - 1) / (self.u + 1) := by
      rw [toField_mul_of_mod y_post, toField_sub_of_mod fe1_post, toField_inv_of_mod fe3_post
          fe3_post1,
        toField_add_of_limbs fe2_post, toField_eq_one_of_asNat one_post, hU, div_eq_mul_inv]
    have hyb : y_bytes.asNat 8 = encodeU ((self.u - 1) / (self.u + 1)) := by
      rw [y_bytes_post, ← hy, encodeU, toField_val]
    have htop := top_byte_lt y_bytes (by rw [hyb]; exact lt_trans (encodeU_lt _) p_lt_two_pow_255)
    have hi : i.val = 2 ^ 7 * (sign.val % 2) := by
      rw [i_post, Nat.shiftLeft_eq, show U8.size = 2 ^ 7 * 2 by simp [U8.size, U8.numBits],
          Nat.mul_comm _ (2 ^ 7),
        Nat.mul_mod_mul_left]
    have hi2 : i2.val = y_bytes[31]!.val + 2 ^ 7 * (sign.val % 2) := by
      rw [i2_val, UScalar.val_xor, i1_post, hi]
      exact xor_top_bit _ _ htop (Nat.mod_lt _ (by norm_num))
    have hset := asNat_of_eq_but_top y_bytes y_bytes1 y_rest
    rw [y31, hi2] at hset
    rw [edwards.CompressedEdwardsY.asNat_def, ← hyb]
    omega

open scoped Helpers.IndexStep Helpers.UpdateStep in
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
@[step]
theorem to_edwards.«i686-no-tables_spec» (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«i686-no-tables» self sign ⦃ (r : Option (edwards.EdwardsPoint.«i686-no-tables»))
        =>
      (self.u = -1 → r = none) ∧
      (self.u ≠ -1 → r.map edwards.EdwardsPoint.«i686-no-tables».toPoint =
        Curve25519Dalek.edwards.decodeLenient (encodeU ((self.u - 1) / (self.u + 1)) + 2 ^ 255 *
            (sign.val % 2))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄ := by
  unfold to_edwards.«i686-no-tables»
  step as ⟨u, hu, hu_lt⟩
  step as ⟨m1, hm1, hm1_lt⟩
  step with backend.serial.u32.field.FieldElement2625.Insts.CoreCmpPartialEqFieldElement2625.eq_spec
    u m1 as ⟨b, hb⟩
  have hU : u.toField = self.u := by
    rw [MontgomeryPoint.u_def, decodeU, toField_def, MontgomeryPoint.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hu
  have hm1' : m1.toField = -1 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hm1
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h
    rw [toField_def]
    exact eq_neg_of_add_eq_zero_left h
  have hb' : b = true ↔ self.u = -1 := by
    rw [hb, ← hU, ← hm1', ← toField_eq_toField_iff]
  split
  · next hbt =>
    have hu1 : self.u = -1 := hb'.mp hbt
    rw [WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd hu1 h, fun q hq => by cases hq⟩
  · next hbf =>
    have hu1 : self.u ≠ -1 := fun h => hbf (hb'.mpr h)
    step as ⟨one, one_post, one_lt⟩
    step as ⟨fe1, fe1_post, fe1_lt⟩
    step as ⟨fe2, fe2_post⟩
    step as ⟨fe3, fe3_post, fe3_post1, fe3_lt⟩
    step as ⟨y, y_post, y_lt⟩
    step as ⟨y_bytes, y_bytes_post⟩
    step as ⟨i, i_post, i_bv⟩
    step as ⟨i1, i1_post⟩
    step as ⟨i2, i2_val, i2_bv⟩
    step as ⟨y_bytes1, y31, y_rest⟩
    step as ⟨r, r_post, r_post1⟩
    refine ⟨fun h => absurd h hu1, fun _ => ?_, r_post1⟩
    rw [r_post]
    congr 1
    -- the value of the bytes: the canonical `y` with the sign in bit `255`
    have hy : y.toField = (self.u - 1) / (self.u + 1) := by
      rw [toField_mul_of_mod y_post, toField_sub_of_mod fe1_post, toField_inv_of_mod fe3_post
          fe3_post1,
        toField_add_of_limbs fe2_post, toField_eq_one_of_asNat one_post, hU, div_eq_mul_inv]
    have hyb : y_bytes.asNat 8 = encodeU ((self.u - 1) / (self.u + 1)) := by
      rw [y_bytes_post, ← hy, encodeU, toField_val]
    have htop := top_byte_lt y_bytes (by rw [hyb]; exact lt_trans (encodeU_lt _) p_lt_two_pow_255)
    have hi : i.val = 2 ^ 7 * (sign.val % 2) := by
      rw [i_post, Nat.shiftLeft_eq, show U8.size = 2 ^ 7 * 2 by simp [U8.size, U8.numBits],
          Nat.mul_comm _ (2 ^ 7),
        Nat.mul_mod_mul_left]
    have hi2 : i2.val = y_bytes[31]!.val + 2 ^ 7 * (sign.val % 2) := by
      rw [i2_val, UScalar.val_xor, i1_post, hi]
      exact xor_top_bit _ _ htop (Nat.mod_lt _ (by norm_num))
    have hset := asNat_of_eq_but_top y_bytes y_bytes1 y_rest
    rw [y31, hi2] at hset
    rw [edwards.CompressedEdwardsY.asNat_def, ← hyb]
    omega

end Curve25519Dalek.montgomery.MontgomeryPoint
