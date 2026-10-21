/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Edwards.Encoding
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Edwards.Affine.Compress
import Proofs.Field.InvertBatchAlloc
import Proofs.Helpers.Coords
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.ToField
import Proofs.Helpers.Vec
public section

/-! # `EdwardsPoint::compress_batch_alloc`

As `compress_batch`, on a slice: the `Z` coordinates are inverted in one batch
(`invert_batch_alloc`), then each point is compressed as the affine point `(X Z⁻¹, Y Z⁻¹)`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

open scoped Helpers.IndexStep in
/-- The first loop of `compress_batch_alloc`: the `Z` coordinates. -/
@[local step]
private theorem compress_batch_alloc_loop0_spec (inputs : Slice EdwardsPoint.«x86_64-tables»)
    (n : Usize) (hn : n.val = inputs.length) (zs : alloc.vec.Vec FieldElement51) (i : Usize)
    (hi : i.val ≤ n.val) (hlen : zs.length = i.val)
    (hzs : ∀ k < i.val, zs[k]! = inputs[k]!.Z) :
    compress_batch_alloc_loop0 inputs n zs i ⦃ (r : alloc.vec.Vec FieldElement51) =>
      r.length = inputs.length ∧ ∀ k < inputs.length, r[k]! = inputs[k]!.Z ⦄ := by
  unfold compress_batch_alloc_loop0
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (z, i') => i'.val ≤ n.val ∧ z.length = i'.val ∧ ∀ k < i'.val,
      z[k]! = inputs[k]!.Z)
  · rintro ⟨z, i'⟩ ⟨hi', hl, hz⟩
    unfold compress_batch_alloc_loop0.body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      step as ⟨ep, hep⟩
      step as ⟨z1, hz1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hz1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x => x = inputs[k]!.Z)
        hz1 (hl ▸ hz) (by rw [hep, hl])
    · simp only [hlt, ite_false, WP.spec_ok]
      have hin : i'.val = inputs.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ hz⟩
  · exact ⟨hi, hlen, hzs⟩

open scoped Helpers.IndexStep in
/-- The second loop of `compress_batch_alloc`: compress `(X z, Y z)` for the inverse `z` of
`Z`. -/
@[local step]
private theorem compress_batch_alloc_loop1_spec (inputs : Slice EdwardsPoint.«x86_64-tables»)
    (hinputs : ∀ k < inputs.length, inputs[k]!.LimbsLt 52) (n : Usize)
    (hn : n.val = inputs.length) (zs : alloc.vec.Vec FieldElement51)
    (hzslen : zs.length = inputs.length)
    (hzs : ∀ k < inputs.length,
      zs[k]!.toField = inputs[k]!.Z.toField⁻¹ ∧ ∀ j < 5, (zs[k]!)[j]!.val < 2 ^ 52)
    (out : alloc.vec.Vec CompressedEdwardsY) (i : Usize) (hi : i.val ≤ n.val)
    (hlen : out.length = i.val)
    (hout : ∀ k < i.val, out[k]!.asNat = (inputs[k]!.Y.toField / inputs[k]!.Z.toField).val +
      2 ^ 255 * (if (inputs[k]!.X.toField / inputs[k]!.Z.toField).isNeg then 1 else 0)) :
    compress_batch_alloc_loop1 inputs n zs out i ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧ ∀ k < inputs.length,
        r[k]!.asNat = (inputs[k]!.Y.toField / inputs[k]!.Z.toField).val +
          2 ^ 255 * (if (inputs[k]!.X.toField / inputs[k]!.Z.toField).isNeg then 1 else 0) ⦄ := by
  unfold compress_batch_alloc_loop1
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (o, i') => i'.val ≤ n.val ∧ o.length = i'.val ∧ ∀ k < i'.val,
      o[k]!.asNat = (inputs[k]!.Y.toField / inputs[k]!.Z.toField).val +
        2 ^ 255 * (if (inputs[k]!.X.toField / inputs[k]!.Z.toField).isNeg then 1 else 0))
  · rintro ⟨o, i'⟩ ⟨hi', hl, ho⟩
    unfold compress_batch_alloc_loop1.body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      step as ⟨ep, hep⟩
      have hik : i'.val < inputs.length := by scalar_tac
      obtain ⟨hX, hY, hZ, hT⟩ := hep ▸ hinputs i'.val hik
      obtain ⟨hzk, hzkb⟩ := hzs i'.val hik
      step as ⟨fe, hfe⟩
      have hfee : fe = zs[i'.val]! := by
        rw [hfe, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      rw [← hfee] at hzk hzkb
      step as ⟨x, hx, hxb⟩
      step as ⟨y, hy, hyb⟩
      step as ⟨cey, hcey⟩
      step as ⟨o1, ho1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x => x.asNat =
        (inputs[k]!.Y.toField / inputs[k]!.Z.toField).val +
          2 ^ 255 * (if (inputs[k]!.X.toField / inputs[k]!.Z.toField).isNeg then 1 else 0))
        ho1 (hl ▸ ho) ?_
      rw [hcey, toField_mul_of_mod hx, toField_mul_of_mod hy, hzk, hep, hl, div_eq_mul_inv,
        div_eq_mul_inv]
    · simp only [hlt, ite_false, WP.spec_ok]
      have hin : i'.val = inputs.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ ho⟩
  · exact ⟨hi, hlen, hout⟩

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is the canonical `y = Y / Z` of point `i`
with the sign of `x = X / Z` in bit `255`; limbs `< 2^52`. -/
@[step]
theorem compress_batch_alloc_spec (inputs : Slice EdwardsPoint.«x86_64-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 52) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧ ∀ i < inputs.length,
        r[i]!.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
          2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).isNeg then 1 else 0) ⦄ := by
  unfold compress_batch_alloc
  step with compress_batch_alloc_loop0_spec inputs _ (Slice.len_val inputs)
    (alloc.vec.Vec.with_capacity FieldElement51 (Slice.len inputs)) 0#usize (by scalar_tac)
    (by rfl) (fun k hk => absurd hk (Nat.not_lt_zero k)) as ⟨z1, hz1len, hz1⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  have hz1b : ∀ k < z1.slice.length, ∀ j < 5, (z1.slice[k]!)[j]!.val < 2 ^ 54 :=
    fun k hk j hj => by
      rw [alloc.vec.Vec.getElem!_slice, hz1 k (hz1len ▸ hk)]
      exact ((hinputs k (hz1len ▸ hk)).2.2.1 j hj).trans (by norm_num : (2 : ℕ) ^ 52 < 2 ^ 54)
  step as ⟨s1, hs1len, hs1⟩
  have hs1' : ∀ k < inputs.length,
      ({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!.toField =
        inputs[k]!.Z.toField⁻¹ ∧
      ∀ j < 5, (({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!)[j]!.val < 2 ^ 52 := by
    intro k hk
    obtain ⟨h0, h1⟩ := hs1 k (by rw [← hz1len] at hk; exact hk)
    rw [alloc.vec.Vec.getElem!_mk]
    rw [alloc.vec.Vec.getElem!_slice, hz1 k hk] at h0 h1
    exact toField_inv_of_batch h0 h1 (hinputs k hk).2.2.1
  step with compress_batch_alloc_loop1_spec inputs hinputs _ (Slice.len_val inputs) _
    (hs1len.trans hz1len) hs1' (alloc.vec.Vec.with_capacity CompressedEdwardsY
      (Slice.len inputs)) 0#usize (by scalar_tac) (by rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) as ⟨r, hrlen, hr⟩
  exact ⟨hrlen, hr⟩

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_alloc_spec_point (inputs : Slice EdwardsPoint.«x86_64-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 52)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄ :=
  spec_mono (compress_batch_alloc_spec inputs hinputs) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, encode_eq, EdwardsPoint.«x86_64-tables».toPoint_x (hinputs_on i hi),
      EdwardsPoint.«x86_64-tables».toPoint_y (hinputs_on i hi)]⟩

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointx86_64-no-tables»

open scoped Helpers.IndexStep in
/-- The first loop of `compress_batch_alloc`: the `Z` coordinates. -/
@[local step]
private theorem compress_batch_alloc_loop0_spec (inputs : Slice EdwardsPoint.«x86_64-no-tables»)
    (n : Usize) (hn : n.val = inputs.length) (zs : alloc.vec.Vec FieldElement51) (i : Usize)
    (hi : i.val ≤ n.val) (hlen : zs.length = i.val)
    (hzs : ∀ k < i.val, zs[k]! = inputs[k]!.Z) :
    compress_batch_alloc_loop0 inputs n zs i ⦃ (r : alloc.vec.Vec FieldElement51) =>
      r.length = inputs.length ∧ ∀ k < inputs.length, r[k]! = inputs[k]!.Z ⦄ := by
  unfold compress_batch_alloc_loop0
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (z, i') => i'.val ≤ n.val ∧ z.length = i'.val ∧ ∀ k < i'.val,
      z[k]! = inputs[k]!.Z)
  · rintro ⟨z, i'⟩ ⟨hi', hl, hz⟩
    unfold compress_batch_alloc_loop0.body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      step as ⟨ep, hep⟩
      step as ⟨z1, hz1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hz1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x => x = inputs[k]!.Z)
        hz1 (hl ▸ hz) (by rw [hep, hl])
    · simp only [hlt, ite_false, WP.spec_ok]
      have hin : i'.val = inputs.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ hz⟩
  · exact ⟨hi, hlen, hzs⟩

open scoped Helpers.IndexStep in
/-- The second loop of `compress_batch_alloc`: compress `(X z, Y z)` for the inverse `z` of
`Z`. -/
@[local step]
private theorem compress_batch_alloc_loop1_spec (inputs : Slice EdwardsPoint.«x86_64-no-tables»)
    (hinputs : ∀ k < inputs.length, inputs[k]!.LimbsLt 52) (n : Usize)
    (hn : n.val = inputs.length) (zs : alloc.vec.Vec FieldElement51)
    (hzslen : zs.length = inputs.length)
    (hzs : ∀ k < inputs.length,
      zs[k]!.toField = inputs[k]!.Z.toField⁻¹ ∧ ∀ j < 5, (zs[k]!)[j]!.val < 2 ^ 52)
    (out : alloc.vec.Vec CompressedEdwardsY) (i : Usize) (hi : i.val ≤ n.val)
    (hlen : out.length = i.val)
    (hout : ∀ k < i.val, out[k]!.asNat = (inputs[k]!.Y.toField / inputs[k]!.Z.toField).val +
      2 ^ 255 * (if (inputs[k]!.X.toField / inputs[k]!.Z.toField).isNeg then 1 else 0)) :
    compress_batch_alloc_loop1 inputs n zs out i ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧ ∀ k < inputs.length,
        r[k]!.asNat = (inputs[k]!.Y.toField / inputs[k]!.Z.toField).val +
          2 ^ 255 * (if (inputs[k]!.X.toField / inputs[k]!.Z.toField).isNeg then 1 else 0) ⦄ := by
  unfold compress_batch_alloc_loop1
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (o, i') => i'.val ≤ n.val ∧ o.length = i'.val ∧ ∀ k < i'.val,
      o[k]!.asNat = (inputs[k]!.Y.toField / inputs[k]!.Z.toField).val +
        2 ^ 255 * (if (inputs[k]!.X.toField / inputs[k]!.Z.toField).isNeg then 1 else 0))
  · rintro ⟨o, i'⟩ ⟨hi', hl, ho⟩
    unfold compress_batch_alloc_loop1.body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      step as ⟨ep, hep⟩
      have hik : i'.val < inputs.length := by scalar_tac
      obtain ⟨hX, hY, hZ, hT⟩ := hep ▸ hinputs i'.val hik
      obtain ⟨hzk, hzkb⟩ := hzs i'.val hik
      step as ⟨fe, hfe⟩
      have hfee : fe = zs[i'.val]! := by
        rw [hfe, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      rw [← hfee] at hzk hzkb
      step as ⟨x, hx, hxb⟩
      step as ⟨y, hy, hyb⟩
      step as ⟨cey, hcey⟩
      step as ⟨o1, ho1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x => x.asNat =
        (inputs[k]!.Y.toField / inputs[k]!.Z.toField).val +
          2 ^ 255 * (if (inputs[k]!.X.toField / inputs[k]!.Z.toField).isNeg then 1 else 0))
        ho1 (hl ▸ ho) ?_
      rw [hcey, toField_mul_of_mod hx, toField_mul_of_mod hy, hzk, hep, hl, div_eq_mul_inv,
        div_eq_mul_inv]
    · simp only [hlt, ite_false, WP.spec_ok]
      have hin : i'.val = inputs.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ ho⟩
  · exact ⟨hi, hlen, hout⟩

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is the canonical `y = Y / Z` of point `i`
with the sign of `x = X / Z` in bit `255`; limbs `< 2^52`. -/
@[step]
theorem compress_batch_alloc_spec (inputs : Slice EdwardsPoint.«x86_64-no-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 52) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧ ∀ i < inputs.length,
        r[i]!.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
          2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).isNeg then 1 else 0) ⦄ := by
  unfold compress_batch_alloc
  step with compress_batch_alloc_loop0_spec inputs _ (Slice.len_val inputs)
    (alloc.vec.Vec.with_capacity FieldElement51 (Slice.len inputs)) 0#usize (by scalar_tac)
    (by rfl) (fun k hk => absurd hk (Nat.not_lt_zero k)) as ⟨z1, hz1len, hz1⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  have hz1b : ∀ k < z1.slice.length, ∀ j < 5, (z1.slice[k]!)[j]!.val < 2 ^ 54 :=
    fun k hk j hj => by
      rw [alloc.vec.Vec.getElem!_slice, hz1 k (hz1len ▸ hk)]
      exact ((hinputs k (hz1len ▸ hk)).2.2.1 j hj).trans (by norm_num : (2 : ℕ) ^ 52 < 2 ^ 54)
  step as ⟨s1, hs1len, hs1⟩
  have hs1' : ∀ k < inputs.length,
      ({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!.toField =
        inputs[k]!.Z.toField⁻¹ ∧
      ∀ j < 5, (({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!)[j]!.val < 2 ^ 52 := by
    intro k hk
    obtain ⟨h0, h1⟩ := hs1 k (by rw [← hz1len] at hk; exact hk)
    rw [alloc.vec.Vec.getElem!_mk]
    rw [alloc.vec.Vec.getElem!_slice, hz1 k hk] at h0 h1
    exact toField_inv_of_batch h0 h1 (hinputs k hk).2.2.1
  step with compress_batch_alloc_loop1_spec inputs hinputs _ (Slice.len_val inputs) _
    (hs1len.trans hz1len) hs1' (alloc.vec.Vec.with_capacity CompressedEdwardsY
      (Slice.len inputs)) 0#usize (by scalar_tac) (by rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) as ⟨r, hrlen, hr⟩
  exact ⟨hrlen, hr⟩

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_alloc_spec_point (inputs : Slice EdwardsPoint.«x86_64-no-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 52)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄ :=
  spec_mono (compress_batch_alloc_spec inputs hinputs) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, encode_eq, EdwardsPoint.«x86_64-no-tables».toPoint_x (hinputs_on i hi),
      EdwardsPoint.«x86_64-no-tables».toPoint_y (hinputs_on i hi)]⟩

end «EdwardsPointx86_64-no-tables»

end Curve25519Dalek.edwards
