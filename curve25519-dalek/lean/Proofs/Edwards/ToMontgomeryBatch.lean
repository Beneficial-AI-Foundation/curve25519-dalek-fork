/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Montgomery
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Montgomery
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Field.InvertBatchAlloc
import Proofs.Helpers.EdwardsMontgomery
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.ToField
import Proofs.Helpers.Vec
public section

/-! # `EdwardsPoint::to_montgomery_batch`

The denominators `Z - Y` are inverted in one batch (`invert_batch_alloc`, which leaves zeros in
place, so `Z = Y` gives `u = 0` as in `to_montgomery`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

open scoped Helpers.IndexStep in
/-- The first loop of `to_montgomery_batch`: the denominators `Z - Y`. -/
@[local step]
private theorem to_montgomery_batch_loop0_spec (eds : Slice EdwardsPoint.«x86_64-tables»)
    (heds : ∀ k < eds.length, eds[k]!.LimbsLt 52) (n : Usize) (hn : n.val = eds.length)
    (den : alloc.vec.Vec FieldElement51) (i : Usize) (hi : i.val ≤ n.val)
    (hlen : den.length = i.val)
    (hden : ∀ k < i.val, den[k]!.toField = eds[k]!.Z.toField - eds[k]!.Y.toField ∧
      (den[k]!).LimbsLt 52) :
    to_montgomery_batch_loop0 eds n den i ⦃ (r : alloc.vec.Vec FieldElement51) =>
      r.length = eds.length ∧ ∀ k < eds.length,
        r[k]!.toField = eds[k]!.Z.toField - eds[k]!.Y.toField ∧
        (r[k]!).LimbsLt 52 ⦄ := by
  unfold to_montgomery_batch_loop0
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (d, i') => i'.val ≤ n.val ∧ d.length = i'.val ∧ ∀ k < i'.val,
      d[k]!.toField = eds[k]!.Z.toField - eds[k]!.Y.toField ∧ (d[k]!).LimbsLt 52)
  · rintro ⟨d, i'⟩ ⟨hi', hl, hd⟩
    unfold to_montgomery_batch_loop0.body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      step as ⟨ep, hep⟩
      obtain ⟨hX, hY, hZ, hT⟩ := hep ▸ heds i'.val (by scalar_tac)
      step as ⟨fe, hfe, hfeb⟩
      step as ⟨d1, hd1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hd1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
          x.toField = eds[k]!.Z.toField - eds[k]!.Y.toField ∧ x.LimbsLt 52)
        hd1 (hl ▸ hd) ⟨by rw [toField_sub_of_mod hfe, hep, hl], hfeb⟩
    · simp only [hlt, ite_false, WP.spec_ok]
      have hin : i'.val = eds.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ hd⟩
  · exact ⟨hi, hlen, hden⟩

open scoped Helpers.IndexStep in
/-- The second loop of `to_montgomery_batch`: `u = (Z + Y) · (Z - Y)⁻¹` as bytes. -/
@[local step]
private theorem to_montgomery_batch_loop1_spec (eds : Slice EdwardsPoint.«x86_64-tables»)
    (heds : ∀ k < eds.length, eds[k]!.LimbsLt 52) (n : Usize) (hn : n.val = eds.length)
    (den : alloc.vec.Vec FieldElement51) (hdenlen : den.length = eds.length)
    (hden : ∀ k < eds.length,
      den[k]!.toField = (eds[k]!.Z.toField - eds[k]!.Y.toField)⁻¹ ∧
      (den[k]!).LimbsLt 54)
    (ret : alloc.vec.Vec montgomery.MontgomeryPoint) (i : Usize) (hi : i.val ≤ n.val)
    (hlen : ret.length = i.val)
    (hret : ∀ k < i.val, ret[k]!.asNat = ((eds[k]!.Z.toField + eds[k]!.Y.toField) /
      (eds[k]!.Z.toField - eds[k]!.Y.toField)).val) :
    to_montgomery_batch_loop1 eds n den ret i
      ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
        r.length = eds.length ∧ ∀ k < eds.length, r[k]!.asNat =
          ((eds[k]!.Z.toField + eds[k]!.Y.toField) /
            (eds[k]!.Z.toField - eds[k]!.Y.toField)).val ⦄ := by
  unfold to_montgomery_batch_loop1
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (d, i') => i'.val ≤ n.val ∧ d.length = i'.val ∧ ∀ k < i'.val,
      d[k]!.asNat = ((eds[k]!.Z.toField + eds[k]!.Y.toField) /
        (eds[k]!.Z.toField - eds[k]!.Y.toField)).val)
  · rintro ⟨d, i'⟩ ⟨hi', hl, hd⟩
    unfold to_montgomery_batch_loop1.body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      step as ⟨ep, hep⟩
      obtain ⟨hX, hY, hZ, hT⟩ := hep ▸ heds i'.val (by scalar_tac)
      step as ⟨fe, hfe⟩
      have hik : i'.val < eds.length := by scalar_tac
      obtain ⟨hdk, hdkb⟩ := hden i'.val hik
      have hfe1' : den.val[i'.val]! = den[i'.val]! := rfl
      step as ⟨fe1, hfe1⟩
      have hfe1e : fe1 = den[i'.val]! := by
        rw [hfe1, ← hfe1', getElem!_pos]
      rw [← hfe1e] at hdk hdkb
      step as ⟨u, hu, hub⟩
      step as ⟨a, ha⟩
      step as ⟨d1, hd1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hd1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x => x.asNat =
        ((eds[k]!.Z.toField + eds[k]!.Y.toField) / (eds[k]!.Z.toField - eds[k]!.Y.toField)).val)
        hd1 (hl ▸ hd) ?_
      rw [montgomery.MontgomeryPoint.asNat_def, asNat_eq_val_of_mod ha, toField_mul_of_mod hu,
        hdk, toField_add_of_limbs hfe, hep, hl, div_eq_mul_inv]
    · simp only [hlt, ite_false, WP.spec_ok]
      have hin : i'.val = eds.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ hd⟩
  · exact ⟨hi, hlen, hret⟩

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is the canonical bytes of
`(Z + Y) / (Z - Y)` of point `i` (`0` if `Z = Y`); limbs `< 2^52`. -/
@[step]
theorem to_montgomery_batch_spec (eds : Slice EdwardsPoint.«x86_64-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 52) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧ ∀ i < eds.length, r[i]!.asNat =
        ((eds[i]!.Z.toField + eds[i]!.Y.toField) /
          (eds[i]!.Z.toField - eds[i]!.Y.toField)).val ⦄ := by
  unfold to_montgomery_batch
  step with to_montgomery_batch_loop0_spec eds heds _ (Slice.len_val eds)
    (alloc.vec.Vec.with_capacity FieldElement51 (Slice.len eds)) 0#usize (by scalar_tac) (by rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) as ⟨d1, hd1len, hd1⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  have hd1b : ∀ k < d1.slice.length, (d1.slice[k]!).LimbsLt 54 :=
    fun k hk j hj => by
      rw [alloc.vec.Vec.getElem!_slice]
      exact ((hd1 k (hd1len ▸ hk)).2 j hj).trans (by norm_num : (2 : ℕ) ^ 52 < 2 ^ 54)
  step as ⟨s1, hs1len, hs1⟩
  have hs1' : ∀ k < eds.length,
      ({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!.toField =
        (eds[k]!.Z.toField - eds[k]!.Y.toField)⁻¹ ∧
      (({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!).LimbsLt 54 := by
    intro k hk
    obtain ⟨hdk, hdkb⟩ := hd1 k hk
    obtain ⟨h0, h1⟩ := hs1 k (by rw [← hd1len] at hk; exact hk)
    rw [alloc.vec.Vec.getElem!_mk]
    rw [alloc.vec.Vec.getElem!_slice] at h0 h1
    rw [← hdk]
    exact (toField_inv_of_batch h0 h1 hdkb).imp_right fun hb j hj =>
      (hb j hj).trans (by norm_num : (2 : ℕ) ^ 52 < 2 ^ 54)
  step with to_montgomery_batch_loop1_spec eds heds _ (Slice.len_val eds) _
    (hs1len.trans hd1len) hs1' (alloc.vec.Vec.with_capacity montgomery.MontgomeryPoint
      (Slice.len eds)) 0#usize (by scalar_tac) (by rfl) (fun k hk => absurd hk (Nat.not_lt_zero k))
    as ⟨r, hrlen, hr⟩
  exact ⟨hrlen, hr⟩

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
theorem to_montgomery_batch_spec_point (eds : Slice EdwardsPoint.«x86_64-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 52) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.asNat = encodeU (edwardsToMontgomery eds[i]!.toPoint).u ⦄ :=
  spec_mono (to_montgomery_batch_spec eds heds) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, EdwardsPoint.«x86_64-tables».u_edwardsToMontgomery (heds_on i hi)]
    rfl⟩

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointx86_64-no-tables»

open scoped Helpers.IndexStep in
/-- The first loop of `to_montgomery_batch`: the denominators `Z - Y`. -/
@[local step]
private theorem to_montgomery_batch_loop0_spec (eds : Slice EdwardsPoint.«x86_64-no-tables»)
    (heds : ∀ k < eds.length, eds[k]!.LimbsLt 52) (n : Usize) (hn : n.val = eds.length)
    (den : alloc.vec.Vec FieldElement51) (i : Usize) (hi : i.val ≤ n.val)
    (hlen : den.length = i.val)
    (hden : ∀ k < i.val, den[k]!.toField = eds[k]!.Z.toField - eds[k]!.Y.toField ∧
      (den[k]!).LimbsLt 52) :
    to_montgomery_batch_loop0 eds n den i ⦃ (r : alloc.vec.Vec FieldElement51) =>
      r.length = eds.length ∧ ∀ k < eds.length,
        r[k]!.toField = eds[k]!.Z.toField - eds[k]!.Y.toField ∧
        (r[k]!).LimbsLt 52 ⦄ := by
  unfold to_montgomery_batch_loop0
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (d, i') => i'.val ≤ n.val ∧ d.length = i'.val ∧ ∀ k < i'.val,
      d[k]!.toField = eds[k]!.Z.toField - eds[k]!.Y.toField ∧ (d[k]!).LimbsLt 52)
  · rintro ⟨d, i'⟩ ⟨hi', hl, hd⟩
    unfold to_montgomery_batch_loop0.body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      step as ⟨ep, hep⟩
      obtain ⟨hX, hY, hZ, hT⟩ := hep ▸ heds i'.val (by scalar_tac)
      step as ⟨fe, hfe, hfeb⟩
      step as ⟨d1, hd1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hd1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
          x.toField = eds[k]!.Z.toField - eds[k]!.Y.toField ∧ x.LimbsLt 52)
        hd1 (hl ▸ hd) ⟨by rw [toField_sub_of_mod hfe, hep, hl], hfeb⟩
    · simp only [hlt, ite_false, WP.spec_ok]
      have hin : i'.val = eds.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ hd⟩
  · exact ⟨hi, hlen, hden⟩

open scoped Helpers.IndexStep in
/-- The second loop of `to_montgomery_batch`: `u = (Z + Y) · (Z - Y)⁻¹` as bytes. -/
@[local step]
private theorem to_montgomery_batch_loop1_spec (eds : Slice EdwardsPoint.«x86_64-no-tables»)
    (heds : ∀ k < eds.length, eds[k]!.LimbsLt 52) (n : Usize) (hn : n.val = eds.length)
    (den : alloc.vec.Vec FieldElement51) (hdenlen : den.length = eds.length)
    (hden : ∀ k < eds.length,
      den[k]!.toField = (eds[k]!.Z.toField - eds[k]!.Y.toField)⁻¹ ∧
      (den[k]!).LimbsLt 54)
    (ret : alloc.vec.Vec montgomery.MontgomeryPoint) (i : Usize) (hi : i.val ≤ n.val)
    (hlen : ret.length = i.val)
    (hret : ∀ k < i.val, ret[k]!.asNat = ((eds[k]!.Z.toField + eds[k]!.Y.toField) /
      (eds[k]!.Z.toField - eds[k]!.Y.toField)).val) :
    to_montgomery_batch_loop1 eds n den ret i
      ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
        r.length = eds.length ∧ ∀ k < eds.length, r[k]!.asNat =
          ((eds[k]!.Z.toField + eds[k]!.Y.toField) /
            (eds[k]!.Z.toField - eds[k]!.Y.toField)).val ⦄ := by
  unfold to_montgomery_batch_loop1
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (d, i') => i'.val ≤ n.val ∧ d.length = i'.val ∧ ∀ k < i'.val,
      d[k]!.asNat = ((eds[k]!.Z.toField + eds[k]!.Y.toField) /
        (eds[k]!.Z.toField - eds[k]!.Y.toField)).val)
  · rintro ⟨d, i'⟩ ⟨hi', hl, hd⟩
    unfold to_montgomery_batch_loop1.body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      step as ⟨ep, hep⟩
      obtain ⟨hX, hY, hZ, hT⟩ := hep ▸ heds i'.val (by scalar_tac)
      step as ⟨fe, hfe⟩
      have hik : i'.val < eds.length := by scalar_tac
      obtain ⟨hdk, hdkb⟩ := hden i'.val hik
      have hfe1' : den.val[i'.val]! = den[i'.val]! := rfl
      step as ⟨fe1, hfe1⟩
      have hfe1e : fe1 = den[i'.val]! := by
        rw [hfe1, ← hfe1', getElem!_pos]
      rw [← hfe1e] at hdk hdkb
      step as ⟨u, hu, hub⟩
      step as ⟨a, ha⟩
      step as ⟨d1, hd1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hd1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x => x.asNat =
        ((eds[k]!.Z.toField + eds[k]!.Y.toField) / (eds[k]!.Z.toField - eds[k]!.Y.toField)).val)
        hd1 (hl ▸ hd) ?_
      rw [montgomery.MontgomeryPoint.asNat_def, asNat_eq_val_of_mod ha, toField_mul_of_mod hu,
        hdk, toField_add_of_limbs hfe, hep, hl, div_eq_mul_inv]
    · simp only [hlt, ite_false, WP.spec_ok]
      have hin : i'.val = eds.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ hd⟩
  · exact ⟨hi, hlen, hret⟩

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is the canonical bytes of
`(Z + Y) / (Z - Y)` of point `i` (`0` if `Z = Y`); limbs `< 2^52`. -/
@[step]
theorem to_montgomery_batch_spec (eds : Slice EdwardsPoint.«x86_64-no-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 52) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧ ∀ i < eds.length, r[i]!.asNat =
        ((eds[i]!.Z.toField + eds[i]!.Y.toField) /
          (eds[i]!.Z.toField - eds[i]!.Y.toField)).val ⦄ := by
  unfold to_montgomery_batch
  step with to_montgomery_batch_loop0_spec eds heds _ (Slice.len_val eds)
    (alloc.vec.Vec.with_capacity FieldElement51 (Slice.len eds)) 0#usize (by scalar_tac) (by rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) as ⟨d1, hd1len, hd1⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  have hd1b : ∀ k < d1.slice.length, (d1.slice[k]!).LimbsLt 54 :=
    fun k hk j hj => by
      rw [alloc.vec.Vec.getElem!_slice]
      exact ((hd1 k (hd1len ▸ hk)).2 j hj).trans (by norm_num : (2 : ℕ) ^ 52 < 2 ^ 54)
  step as ⟨s1, hs1len, hs1⟩
  have hs1' : ∀ k < eds.length,
      ({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!.toField =
        (eds[k]!.Z.toField - eds[k]!.Y.toField)⁻¹ ∧
      (({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!).LimbsLt 54 := by
    intro k hk
    obtain ⟨hdk, hdkb⟩ := hd1 k hk
    obtain ⟨h0, h1⟩ := hs1 k (by rw [← hd1len] at hk; exact hk)
    rw [alloc.vec.Vec.getElem!_mk]
    rw [alloc.vec.Vec.getElem!_slice] at h0 h1
    rw [← hdk]
    exact (toField_inv_of_batch h0 h1 hdkb).imp_right fun hb j hj =>
      (hb j hj).trans (by norm_num : (2 : ℕ) ^ 52 < 2 ^ 54)
  step with to_montgomery_batch_loop1_spec eds heds _ (Slice.len_val eds) _
    (hs1len.trans hd1len) hs1' (alloc.vec.Vec.with_capacity montgomery.MontgomeryPoint
      (Slice.len eds)) 0#usize (by scalar_tac) (by rfl) (fun k hk => absurd hk (Nat.not_lt_zero k))
    as ⟨r, hrlen, hr⟩
  exact ⟨hrlen, hr⟩

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
theorem to_montgomery_batch_spec_point (eds : Slice EdwardsPoint.«x86_64-no-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 52) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.asNat = encodeU (edwardsToMontgomery eds[i]!.toPoint).u ⦄ :=
  spec_mono (to_montgomery_batch_spec eds heds) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, EdwardsPoint.«x86_64-no-tables».u_edwardsToMontgomery (heds_on i hi)]
    rfl⟩

end «EdwardsPointx86_64-no-tables»

end Curve25519Dalek.edwards
