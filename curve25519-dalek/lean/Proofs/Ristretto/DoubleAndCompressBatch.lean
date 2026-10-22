/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Ristretto.Encoding
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Ristretto
import Proofs.Backend.Serial.U64.Constants.EdwardsD
import Proofs.Backend.Serial.U64.Constants.InvsqrtAMinusD
import Proofs.Backend.Serial.U64.Constants.SqrtM1
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U64.Field.ConditionalNegate
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Neg
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Field.InvertBatchAlloc
import Proofs.Field.IsNegative
import Proofs.Helpers.Coords
import Proofs.Helpers.Collect
import Proofs.Helpers.RistrettoCompress
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.ToField
import Proofs.Helpers.Vec
public section

/-! # `RistrettoPoint::double_and_compress_batch`

The patched code collects a `BatchCompressState` per point (the doubling quantities
`e, f, g, h` and the products `e g`, `f h`), inverts the products `e g · f h` in one batch, and
encodes each doubled point from its state and inverse
(`RistrettoCompress.doubleCompress_eq_encodeRep`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.ristretto

namespace «RistrettoPointx86_64-tables».double_and_compress_batch

/-- The state of a point `P`: its doubling quantities as field elements, with their limb bounds. -/
private def StateOf (P : RistrettoPoint.«x86_64-tables») (st : BatchCompressState) : Prop :=
  st.e.toField = P.X.toField * (P.Y.toField + P.Y.toField) ∧
  st.f.toField = P.Z.toField ^ 2 + P.T.toField ^ 2 * d ∧
  st.g.toField = P.Y.toField ^ 2 + P.X.toField ^ 2 ∧
  st.h.toField = P.Z.toField ^ 2 - P.T.toField ^ 2 * d ∧
  st.eg.toField = st.e.toField * st.g.toField ∧ st.fh.toField = st.f.toField * st.h.toField ∧
  st.e.LimbsLt 54 ∧ st.f.LimbsLt 54 ∧ st.g.LimbsLt 54 ∧ st.h.LimbsLt 54 ∧ st.eg.LimbsLt 52 ∧
  st.fh.LimbsLt 52

open BatchCompressState.Insts in
/-- `BatchCompressState::from`: the doubling quantities of `P`. -/
private theorem from_spec (P : RistrettoPoint.«x86_64-tables») (hP : P.LimbsLt 52) :
    «CoreConvertFromSharedARistrettoPointx86_64-tables».from P
      ⦃ (st : BatchCompressState) => StateOf P st ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hP
  unfold «CoreConvertFromSharedARistrettoPointx86_64-tables».from
  step as ⟨XX, hXX, hXXb⟩
  step as ⟨YY, hYY, hYYb⟩
  step as ⟨ZZ, hZZ, hZZb⟩
  step as ⟨TT, hTT, hTTb⟩
  step as ⟨fd, hfd, hfdb⟩
  step as ⟨dTT, hdTT, hdTTb⟩
  step as ⟨Y2, hY2⟩
  step as ⟨e, he, heb⟩
  step as ⟨f, hf⟩
  step as ⟨g, hg⟩
  step as ⟨h, hh, hhb⟩
  step as ⟨eg, heg, hegb⟩
  step as ⟨fh, hfh, hfhb⟩
  refine ⟨?_, ?_, ?_, ?_, toField_mul_of_mod heg, toField_mul_of_mod hfh,
    limbs_lt_of_le (by decide) heb, ?_, ?_, limbs_lt_of_le (by decide) hhb, hegb, hfhb⟩
  · rw [toField_mul_of_mod he, toField_add_of_limbs hY2]
  · rw [toField_add_of_limbs hf, toField_sq_of_mod hZZ, toField_mul_of_mod hdTT,
      toField_sq_of_mod hTT, toField_eq_d_of_asNat hfd]
  · rw [toField_add_of_limbs hg, toField_sq_of_mod hYY, toField_sq_of_mod hXX]
  · rw [toField_sub_of_mod hh, toField_sq_of_mod hZZ, toField_mul_of_mod hdTT,
      toField_sq_of_mod hTT, toField_eq_d_of_asNat hfd]
  · exact limbs_lt_of_le (by decide) (limbs_add_lt hf hZZb hdTTb)
  · exact limbs_lt_of_le (by decide) (limbs_add_lt hg hYYb hXXb)

private instance : Inhabited BatchCompressState :=
  ⟨⟨default, default, default, default, default, default⟩⟩

/-- `Forall₂` entry by entry. -/
private theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (k : ℕ) (hk : k < l₁.length) :
    R l₁[k]! l₂[k]! := by
  obtain ⟨hlen, hR⟩ := List.forall₂_iff_get.mp h
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (hlen ▸ hk)]
  exact hR k hk (hlen ▸ hk)

/-- The collecting loop: one state per point. -/
private theorem states_loop_spec {It : Type}
    (iterInst : core.iter.traits.iterator.Iterator It RistrettoPoint.«x86_64-tables»)
    (it : It) (ps : List RistrettoPoint.«x86_64-tables») (hit : iterInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (out : alloc.vec.Vec BatchCompressState)
    (hlen : out.length + ps.length ≤ Usize.max) :
    states_loop iterInst it out ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      ∃ sts, v.val = out.val ++ sts ∧ List.Forall₂ StateOf ps sts ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold states_loop loop states_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' P ps' hnext _ ih =>
    unfold states_loop loop states_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with from_spec P (hps P List.mem_cons_self) as ⟨st, hst⟩
    step with alloc.vec.Vec.push_spec out st
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ)) out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    rintro r ⟨zs, hr, hzs⟩
    exact ⟨st :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
      List.Forall₂.cons hst hzs⟩

/-- `BatchCompressState::efgh`: the product `e g · f h`. -/
@[local step]
private theorem efgh_spec (st : BatchCompressState) (h1 : st.eg.LimbsLt 52)
    (h2 : st.fh.LimbsLt 52) :
    st.efgh ⦃ (r : FieldElement51) =>
      r.toField = st.eg.toField * st.fh.toField ∧ r.LimbsLt 52 ⦄ := by
  unfold BatchCompressState.efgh
  step as ⟨r, hr, hrb⟩
  exact ⟨toField_mul_of_mod hr, hrb⟩

/-- `states`: one state per point. -/
private theorem states_spec {It : Type}
    (iterInst : core.iter.traits.iterator.Iterator It RistrettoPoint.«x86_64-tables»)
    (it : It) (ps : List RistrettoPoint.«x86_64-tables») (hit : iterInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (hlen : ps.length ≤ Usize.max) :
    states iterInst it ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      List.Forall₂ StateOf ps v.val ⦄ := by
  unfold states
  apply spec_mono (states_loop_spec iterInst it ps hit hps (alloc.vec.Vec.new _)
    (by simpa using hlen))
  rintro v ⟨zs, hv, hzs⟩
  rw [hv]
  simpa using hzs

end «RistrettoPointx86_64-tables».double_and_compress_batch

namespace «RistrettoPointx86_64-tables»

open double_and_compress_batch

open scoped Helpers.IndexStep in
/-- The first loop: the products `e g · f h` of the states. -/
private theorem loop0_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 52 ∧ (states[k]!).fh.LimbsLt 52)
    (invs : alloc.vec.Vec FieldElement51) (i : Usize) (hi : i.val ≤ states.length)
    (hlen : invs.length = i.val)
    (hinvs : ∀ k < i.val, invs[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
      (invs[k]!).LimbsLt 52) :
    double_and_compress_batch_loop0 states invs i ⦃ (r : alloc.vec.Vec FieldElement51) =>
      r.length = states.length ∧ ∀ k < states.length,
        r[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
          (r[k]!).LimbsLt 52 ⦄ := by
  unfold double_and_compress_batch_loop0
  apply loop.spec_decr_nat (measure := fun (_, i') => states.length - i'.val)
    (inv := fun (z, i') => i'.val ≤ states.length ∧ z.length = i'.val ∧ ∀ k < i'.val,
      z[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧ (z[k]!).LimbsLt 52)
  · rintro ⟨z, i'⟩ ⟨hi', hl, hz⟩
    unfold double_and_compress_batch_loop0.body
    by_cases hlt : i'.val < states.length
    · have hlt' : i' < states.len := by
        rw [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact hlt
      simp only [hlt', ite_true]
      step as ⟨bcs, hbcs⟩
      replace hbcs : bcs = states[i'.val]! := by
        rw [hbcs, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      obtain ⟨h1, h2⟩ := hst i'.val hlt
      rw [← hbcs] at h1 h2
      step with efgh_spec bcs h1 h2 as ⟨fe, hfe, hfeb⟩
      step as ⟨z1, hz1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hz1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
        x.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧ x.LimbsLt 52)
        hz1 (hl ▸ hz) (by rw [hl, ← hbcs]; exact ⟨hfe, hfeb⟩)
    · have hlt' : ¬ i' < states.len := by
        rw [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact hlt
      simp only [hlt', ite_false, WP.spec_ok]
      have hin : i'.val = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ hz⟩
  · exact ⟨hi, hlen, hinvs⟩

set_option linter.hashCommand false in
#decompose double_and_compress_batch_loop1.body loop1_body_eq
  afterLets (branch 0 (letRange 2 23)) => compressState

/-- The encoding step of `double_and_compress_batch`'s second loop: the bytes of `2 P` from the
state of `P` and the inverse of `e g · f h`. -/
add_decl_doc compressState

/-- The encoding step of the second loop: from the state of `P` and the inverse of `e g · f h`,
the bytes of `2 P`. -/
private theorem compressState_spec (P : RistrettoPoint.«x86_64-tables») (hP : P.OnCurve)
    (st : BatchCompressState) (hst : StateOf P st) (inv : FieldElement51)
    (Inv : inv.toField = (st.eg.toField * st.fh.toField)⁻¹) (Invb : inv.LimbsLt 52) :
    compressState st inv ⦃ (bytes : CompressedRistretto) =>
      bytes.asNat = Ristretto.encodeRep (2 • P.toPoint) ⦄ := by
  obtain ⟨Se, Sf, Sg, Sh, Seg, Sfh, Seb, Sfb, Sgb, Shb, Segb, Sfhb⟩ := hst
  unfold compressState
  step as ⟨Zinv, hZinv, hZinvb⟩
  step as ⟨Tinv, hTinv, hTinvb⟩
  step as ⟨magic, hmlt, hm, hmb⟩
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨n1, hn1v, hn1⟩
  step as ⟨me, hme, hmeb⟩
  step as ⟨fi, hfi, hfib⟩
  step as ⟨fts, hfts, hftsb⟩
  step as ⟨e1, he10, he11⟩
  step as ⟨g1, hg10, hg11⟩
  step as ⟨h1, hh10, hh11⟩
  step as ⟨mg1, hmg10, hmg11⟩
  have he1b : e1.LimbsLt 54 := by
    rcases hn1v with h | h
    · rw [he10 h]; exact Seb
    · rw [he11 h]; exact Sgb
  have hg1b : g1.LimbsLt 54 := by
    rcases hn1v with h | h
    · rw [hg10 h]; exact Sgb
    · rw [hg11 h]; exact limbs_lt_of_le (by decide) hmeb
  have hh1b : h1.LimbsLt 54 := by
    rcases hn1v with h | h
    · rw [hh10 h]; exact Shb
    · rw [hh11 h]; exact limbs_lt_of_le (by decide) hftsb
  have hmg1b : mg1.LimbsLt 54 := by
    rcases hn1v with h | h
    · rw [hmg10 h]; exact limbs_lt_of_le (by decide) hmb
    · rw [hmg11 h]; exact limbs_lt_of_le (by decide) hfib
  step as ⟨fe2, hfe2, hfe2b⟩
  step as ⟨fe3, hfe3, hfe3b⟩
  step as ⟨n2, hn2v, hn2⟩
  step as ⟨g2, hg20, hg21⟩
  have hg2b : g2.LimbsLt 54 := by
    rcases hn2v with h | h
    · rw [hg20 h]; exact hg1b
    · exact limbs_lt_of_le (by decide) (hg21 h).2
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨fe5, hfe5, hfe5b⟩
  step as ⟨fe6, hfe6, hfe6b⟩
  step as ⟨sv, hsv, hsvb⟩
  step as ⟨sn, hsnv, hsn⟩
  have hsvb' : sv.LimbsLt 54 := limbs_lt_of_le (by decide) hsvb
  step as ⟨s1, hs10, hs11⟩
  step as ⟨bytes, hbytes⟩
  -- the field values
  have Fi : fi.toField = sqrtM1 := by rw [toField_def, hfi]
  have C : magic.toField ^ 2 * (a - d) = 1 := by
    have h := natCast_eq_natCast_of_mod_eq (hm.trans one_mod_p.symm)
    push_cast at h
    rwa [ZMod.natCast_zmod_val, ← toField_def] at h
  have Neg1 := eq_one_iff_isNeg_toField hn1
  have E1 : e1.toField = if fe.toField.isNeg then st.g.toField else st.e.toField :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [he10 h]) (fun h => by rw [he11 h])
  have G1 : g1.toField = if fe.toField.isNeg then -st.e.toField else st.g.toField :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [hg10 h])
      (fun h => by rw [hg11 h]; exact toField_neg_of_mod hme)
  have H1 : h1.toField = if fe.toField.isNeg then st.f.toField * sqrtM1 else st.h.toField :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [hh10 h])
      (fun h => by rw [hh11 h, toField_mul_of_mod hfts, Fi])
  have M1 : mg1.toField = if fe.toField.isNeg then (sqrtM1 : ZMod p) else magic.toField :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [hmg10 h]) (fun h => by rw [hmg11 h, Fi])
  have G2 : g2.toField = if fe3.toField.isNeg then -g1.toField else g1.toField :=
    eq_ite_of_choice hn2v (eq_one_iff_isNeg_toField hn2) (fun h => by rw [hg20 h])
      (fun h => toField_neg_of_mod (hg21 h).1)
  have S1 : s1.toField = sv.toField.abs :=
    eq_ite_of_choice hsnv (eq_one_iff_isNeg_toField hsn) (fun h => by rw [hs10 h])
      (fun h => toField_neg_of_mod (hs11 h).1)
  -- the point
  obtain ⟨hZ0, hXYZT, -⟩ :=
    (edwards.EdwardsPoint.«x86_64-tables».onCurve_iff_equation _).mp hP
  rw [CompressedRistretto.asNat_def, hbytes, ← toField_val, S1,
    ← RistrettoCompress.doubleCompress_eq_encodeRep _ C hZ0 hXYZT
      (edwards.EdwardsPoint.«x86_64-tables».toPoint_x hP)
      (edwards.EdwardsPoint.«x86_64-tables».toPoint_y hP), ← Se, ← Sf, ← Sg, ← Sh]
  congr 1
  dsimp only [RistrettoCompress.doubleCompress]
  rw [toField_mul_of_mod hsv, toField_sub_of_mod hfe4, toField_mul_of_mod hfe6,
    toField_mul_of_mod hfe5, G2, toField_mul_of_mod hfe3, toField_mul_of_mod hfe2, H1, E1, G1,
    M1, toField_mul_of_mod hfe, toField_mul_of_mod hZinv, toField_mul_of_mod hTinv, Inv, Seg,
    Sfh]


open scoped Helpers.IndexStep in
/-- The second loop: entry `k` encodes `2 P_k`, from the state and the inverse of `e g · f h`. -/
private theorem loop1_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (ps : List RistrettoPoint.«x86_64-tables») (hsts : List.Forall₂ StateOf ps states.val)
    (hon : ∀ P ∈ ps, P.OnCurve) (invs : alloc.vec.Vec FieldElement51)
    (hinvs : ∀ k < states.length, invs[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧ (invs[k]!).LimbsLt 52)
    (hinvlen : invs.length = states.length)
    (out : alloc.vec.Vec CompressedRistretto) (i : Usize) (hi : i.val ≤ states.length)
    (hlen : out.length = i.val)
    (hout : ∀ k < i.val, out[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) :
    double_and_compress_batch_loop1 states invs out i ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = states.length ∧
        ∀ k < states.length, r[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint) ⦄ := by
  have hpslen : ps.length = states.length := by
    rw [hsts.length_eq]
  unfold double_and_compress_batch_loop1
  apply loop.spec_decr_nat (measure := fun (_, i') => states.length - i'.val)
    (inv := fun (o, i') => i'.val ≤ states.length ∧ o.length = i'.val ∧ ∀ k < i'.val,
      o[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint))
  · rintro ⟨o, i'⟩ ⟨hi', hl, ho⟩
    dsimp only
    rw [loop1_body_eq]
    by_cases hlt : i'.val < states.length
    · have hlt' : i' < states.len := by
        rw [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact hlt
      simp only [hlt', ite_true]
      step as ⟨st, hst⟩
      replace hst : st = states[i'.val]! := by
        rw [hst, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      step as ⟨inv, hinv⟩
      replace hinv : inv = invs[i'.val]! := by
        rw [hinv, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      obtain ⟨Inv, Invb⟩ := hinvs i'.val hlt
      rw [← hst, ← hinv] at Inv
      rw [← hinv] at Invb
      rw [alloc.vec.Vec.getElem!_Nat_eq] at hst
      have hPmem : ps[i'.val]! ∈ ps := by
        rw [getElem!_pos ps i'.val (hpslen ▸ hlt)]
        exact List.getElem_mem _
      have hS := forall₂_getElem! hsts i'.val (hpslen ▸ hlt)
      rw [← hst] at hS
      step with compressState_spec _ (hon _ hPmem) st hS inv Inv Invb as ⟨bytes, hbytes⟩
      step as ⟨o1, ho1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
        x.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) ho1 (hl ▸ ho) ?_
      rw [hl]
      exact hbytes
    · have hlt' : ¬ i' < states.len := by
        rw [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact hlt
      simp only [hlt', ite_false, WP.spec_ok]
      have hin : i'.val = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ ho⟩
  · exact ⟨hi, hlen, hout⟩

/-- `RistrettoPoint::double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for
the points `P_i` the input yields; limbs `< 2^52`. -/
@[step]
theorem double_and_compress_batch_spec {I Clause0_IntoIter : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«x86_64-tables» Clause0_IntoIter)
    (points : I) (ps : List RistrettoPoint.«x86_64-tables»)
    (hpoints : pointsInst.Yields points ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = ps.length ∧
        ∀ i < ps.length, r[i]!.asNat = Ristretto.encodeRep (2 • (ps[i]!).toPoint) ⦄ := by
  unfold double_and_compress_batch
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ps ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  step with states_spec _ it ps hit (fun P hP => (hps P hP).1) hlen as ⟨states, hsts⟩
  have hpslen : ps.length = states.length := hsts.length_eq
  have hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 52 ∧ (states[k]!).fh.LimbsLt 52 :=
    fun k hk => by
      have h := forall₂_getElem! hsts k (hpslen ▸ hk)
      rw [alloc.vec.Vec.getElem!_Nat_eq]
      exact ⟨h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩
  step with loop0_spec states hst (alloc.vec.Vec.with_capacity FieldElement51 states.len) 0#usize
    (by simp) (by rfl) (fun k hk => absurd hk (by simp)) as ⟨invs1, hinvs1len, hinvs1⟩
  simp only [alloc.vec.Vec.index_mut, pure]
  have hsb : ∀ k < invs1.slice.length, (invs1.slice[k]!).LimbsLt 54 := fun k hk => by
    rw [alloc.vec.Vec.getElem!_slice]
    exact limbs_lt_of_le (by decide) (hinvs1 k (hinvs1len ▸ hk)).2
  step as ⟨s1, hs1len, hs1⟩
  have hslen : invs1.slice.length = states.length := hinvs1len
  have hinvs : ∀ k < states.length, ({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧
      (({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!).LimbsLt 52 := by
    intro k hk
    obtain ⟨h0, h1⟩ := hs1 k (hslen ▸ hk)
    obtain ⟨hv, hb⟩ := hinvs1 k hk
    rw [alloc.vec.Vec.getElem!_slice] at h0 h1
    rw [alloc.vec.Vec.getElem!_mk, ← hv]
    exact toField_inv_of_batch h0 h1 hb
  step with loop1_spec states ps hsts (fun P hP => (hps P hP).2) _ hinvs
    (by rw [alloc.vec.Vec.length]; exact hs1len.trans hslen)
    (alloc.vec.Vec.with_capacity CompressedRistretto states.len) 0#usize (by simp) (by rfl)
    (fun k hk => absurd hk (by simp)) as ⟨r, hrlen, hr⟩
  exact ⟨hrlen.trans hpslen.symm, fun k hk => hr k (hpslen ▸ hk)⟩

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointx86_64-no-tables».double_and_compress_batch

/-- The state of a point `P`: its doubling quantities as field elements, with their limb bounds. -/
private def StateOf (P : RistrettoPoint.«x86_64-no-tables») (st : BatchCompressState) : Prop :=
  st.e.toField = P.X.toField * (P.Y.toField + P.Y.toField) ∧
  st.f.toField = P.Z.toField ^ 2 + P.T.toField ^ 2 * d ∧
  st.g.toField = P.Y.toField ^ 2 + P.X.toField ^ 2 ∧
  st.h.toField = P.Z.toField ^ 2 - P.T.toField ^ 2 * d ∧
  st.eg.toField = st.e.toField * st.g.toField ∧ st.fh.toField = st.f.toField * st.h.toField ∧
  st.e.LimbsLt 54 ∧ st.f.LimbsLt 54 ∧ st.g.LimbsLt 54 ∧ st.h.LimbsLt 54 ∧ st.eg.LimbsLt 52 ∧
  st.fh.LimbsLt 52

open BatchCompressState.Insts in
/-- `BatchCompressState::from`: the doubling quantities of `P`. -/
private theorem from_spec (P : RistrettoPoint.«x86_64-no-tables») (hP : P.LimbsLt 52) :
    «CoreConvertFromSharedARistrettoPointx86_64-no-tables».from P
      ⦃ (st : BatchCompressState) => StateOf P st ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hP
  unfold «CoreConvertFromSharedARistrettoPointx86_64-no-tables».from
  step as ⟨XX, hXX, hXXb⟩
  step as ⟨YY, hYY, hYYb⟩
  step as ⟨ZZ, hZZ, hZZb⟩
  step as ⟨TT, hTT, hTTb⟩
  step as ⟨fd, hfd, hfdb⟩
  step as ⟨dTT, hdTT, hdTTb⟩
  step as ⟨Y2, hY2⟩
  step as ⟨e, he, heb⟩
  step as ⟨f, hf⟩
  step as ⟨g, hg⟩
  step as ⟨h, hh, hhb⟩
  step as ⟨eg, heg, hegb⟩
  step as ⟨fh, hfh, hfhb⟩
  refine ⟨?_, ?_, ?_, ?_, toField_mul_of_mod heg, toField_mul_of_mod hfh,
    limbs_lt_of_le (by decide) heb, ?_, ?_, limbs_lt_of_le (by decide) hhb, hegb, hfhb⟩
  · rw [toField_mul_of_mod he, toField_add_of_limbs hY2]
  · rw [toField_add_of_limbs hf, toField_sq_of_mod hZZ, toField_mul_of_mod hdTT,
      toField_sq_of_mod hTT, toField_eq_d_of_asNat hfd]
  · rw [toField_add_of_limbs hg, toField_sq_of_mod hYY, toField_sq_of_mod hXX]
  · rw [toField_sub_of_mod hh, toField_sq_of_mod hZZ, toField_mul_of_mod hdTT,
      toField_sq_of_mod hTT, toField_eq_d_of_asNat hfd]
  · exact limbs_lt_of_le (by decide) (limbs_add_lt hf hZZb hdTTb)
  · exact limbs_lt_of_le (by decide) (limbs_add_lt hg hYYb hXXb)

private instance : Inhabited BatchCompressState :=
  ⟨⟨default, default, default, default, default, default⟩⟩

/-- `Forall₂` entry by entry. -/
private theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (k : ℕ) (hk : k < l₁.length) :
    R l₁[k]! l₂[k]! := by
  obtain ⟨hlen, hR⟩ := List.forall₂_iff_get.mp h
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (hlen ▸ hk)]
  exact hR k hk (hlen ▸ hk)

/-- The collecting loop: one state per point. -/
private theorem states_loop_spec {It : Type}
    (iterInst : core.iter.traits.iterator.Iterator It RistrettoPoint.«x86_64-no-tables»)
    (it : It) (ps : List RistrettoPoint.«x86_64-no-tables») (hit : iterInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (out : alloc.vec.Vec BatchCompressState)
    (hlen : out.length + ps.length ≤ Usize.max) :
    states_loop iterInst it out ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      ∃ sts, v.val = out.val ++ sts ∧ List.Forall₂ StateOf ps sts ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold states_loop loop states_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' P ps' hnext _ ih =>
    unfold states_loop loop states_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with from_spec P (hps P List.mem_cons_self) as ⟨st, hst⟩
    step with alloc.vec.Vec.push_spec out st
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ)) out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    rintro r ⟨zs, hr, hzs⟩
    exact ⟨st :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
      List.Forall₂.cons hst hzs⟩

/-- `BatchCompressState::efgh`: the product `e g · f h`. -/
@[local step]
private theorem efgh_spec (st : BatchCompressState) (h1 : st.eg.LimbsLt 52)
    (h2 : st.fh.LimbsLt 52) :
    st.efgh ⦃ (r : FieldElement51) =>
      r.toField = st.eg.toField * st.fh.toField ∧ r.LimbsLt 52 ⦄ := by
  unfold BatchCompressState.efgh
  step as ⟨r, hr, hrb⟩
  exact ⟨toField_mul_of_mod hr, hrb⟩

/-- `states`: one state per point. -/
private theorem states_spec {It : Type}
    (iterInst : core.iter.traits.iterator.Iterator It RistrettoPoint.«x86_64-no-tables»)
    (it : It) (ps : List RistrettoPoint.«x86_64-no-tables») (hit : iterInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (hlen : ps.length ≤ Usize.max) :
    states iterInst it ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      List.Forall₂ StateOf ps v.val ⦄ := by
  unfold states
  apply spec_mono (states_loop_spec iterInst it ps hit hps (alloc.vec.Vec.new _)
    (by simpa using hlen))
  rintro v ⟨zs, hv, hzs⟩
  rw [hv]
  simpa using hzs

end «RistrettoPointx86_64-no-tables».double_and_compress_batch

namespace «RistrettoPointx86_64-no-tables»

open double_and_compress_batch

open scoped Helpers.IndexStep in
/-- The first loop: the products `e g · f h` of the states. -/
private theorem loop0_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 52 ∧ (states[k]!).fh.LimbsLt 52)
    (invs : alloc.vec.Vec FieldElement51) (i : Usize) (hi : i.val ≤ states.length)
    (hlen : invs.length = i.val)
    (hinvs : ∀ k < i.val, invs[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
      (invs[k]!).LimbsLt 52) :
    double_and_compress_batch_loop0 states invs i ⦃ (r : alloc.vec.Vec FieldElement51) =>
      r.length = states.length ∧ ∀ k < states.length,
        r[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
          (r[k]!).LimbsLt 52 ⦄ := by
  unfold double_and_compress_batch_loop0
  apply loop.spec_decr_nat (measure := fun (_, i') => states.length - i'.val)
    (inv := fun (z, i') => i'.val ≤ states.length ∧ z.length = i'.val ∧ ∀ k < i'.val,
      z[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧ (z[k]!).LimbsLt 52)
  · rintro ⟨z, i'⟩ ⟨hi', hl, hz⟩
    unfold double_and_compress_batch_loop0.body
    by_cases hlt : i'.val < states.length
    · have hlt' : i' < states.len := by
        rw [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact hlt
      simp only [hlt', ite_true]
      step as ⟨bcs, hbcs⟩
      replace hbcs : bcs = states[i'.val]! := by
        rw [hbcs, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      obtain ⟨h1, h2⟩ := hst i'.val hlt
      rw [← hbcs] at h1 h2
      step with efgh_spec bcs h1 h2 as ⟨fe, hfe, hfeb⟩
      step as ⟨z1, hz1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hz1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
        x.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧ x.LimbsLt 52)
        hz1 (hl ▸ hz) (by rw [hl, ← hbcs]; exact ⟨hfe, hfeb⟩)
    · have hlt' : ¬ i' < states.len := by
        rw [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact hlt
      simp only [hlt', ite_false, WP.spec_ok]
      have hin : i'.val = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ hz⟩
  · exact ⟨hi, hlen, hinvs⟩

set_option linter.hashCommand false in
#decompose double_and_compress_batch_loop1.body loop1_body_eq
  afterLets (branch 0 (letRange 2 23)) => compressState

/-- The encoding step of `double_and_compress_batch`'s second loop: the bytes of `2 P` from the
state of `P` and the inverse of `e g · f h`. -/
add_decl_doc compressState

/-- The encoding step of the second loop: from the state of `P` and the inverse of `e g · f h`,
the bytes of `2 P`. -/
private theorem compressState_spec (P : RistrettoPoint.«x86_64-no-tables») (hP : P.OnCurve)
    (st : BatchCompressState) (hst : StateOf P st) (inv : FieldElement51)
    (Inv : inv.toField = (st.eg.toField * st.fh.toField)⁻¹) (Invb : inv.LimbsLt 52) :
    compressState st inv ⦃ (bytes : CompressedRistretto) =>
      bytes.asNat = Ristretto.encodeRep (2 • P.toPoint) ⦄ := by
  obtain ⟨Se, Sf, Sg, Sh, Seg, Sfh, Seb, Sfb, Sgb, Shb, Segb, Sfhb⟩ := hst
  unfold compressState
  step as ⟨Zinv, hZinv, hZinvb⟩
  step as ⟨Tinv, hTinv, hTinvb⟩
  step as ⟨magic, hmlt, hm, hmb⟩
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨n1, hn1v, hn1⟩
  step as ⟨me, hme, hmeb⟩
  step as ⟨fi, hfi, hfib⟩
  step as ⟨fts, hfts, hftsb⟩
  step as ⟨e1, he10, he11⟩
  step as ⟨g1, hg10, hg11⟩
  step as ⟨h1, hh10, hh11⟩
  step as ⟨mg1, hmg10, hmg11⟩
  have he1b : e1.LimbsLt 54 := by
    rcases hn1v with h | h
    · rw [he10 h]; exact Seb
    · rw [he11 h]; exact Sgb
  have hg1b : g1.LimbsLt 54 := by
    rcases hn1v with h | h
    · rw [hg10 h]; exact Sgb
    · rw [hg11 h]; exact limbs_lt_of_le (by decide) hmeb
  have hh1b : h1.LimbsLt 54 := by
    rcases hn1v with h | h
    · rw [hh10 h]; exact Shb
    · rw [hh11 h]; exact limbs_lt_of_le (by decide) hftsb
  have hmg1b : mg1.LimbsLt 54 := by
    rcases hn1v with h | h
    · rw [hmg10 h]; exact limbs_lt_of_le (by decide) hmb
    · rw [hmg11 h]; exact limbs_lt_of_le (by decide) hfib
  step as ⟨fe2, hfe2, hfe2b⟩
  step as ⟨fe3, hfe3, hfe3b⟩
  step as ⟨n2, hn2v, hn2⟩
  step as ⟨g2, hg20, hg21⟩
  have hg2b : g2.LimbsLt 54 := by
    rcases hn2v with h | h
    · rw [hg20 h]; exact hg1b
    · exact limbs_lt_of_le (by decide) (hg21 h).2
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨fe5, hfe5, hfe5b⟩
  step as ⟨fe6, hfe6, hfe6b⟩
  step as ⟨sv, hsv, hsvb⟩
  step as ⟨sn, hsnv, hsn⟩
  have hsvb' : sv.LimbsLt 54 := limbs_lt_of_le (by decide) hsvb
  step as ⟨s1, hs10, hs11⟩
  step as ⟨bytes, hbytes⟩
  -- the field values
  have Fi : fi.toField = sqrtM1 := by rw [toField_def, hfi]
  have C : magic.toField ^ 2 * (a - d) = 1 := by
    have h := natCast_eq_natCast_of_mod_eq (hm.trans one_mod_p.symm)
    push_cast at h
    rwa [ZMod.natCast_zmod_val, ← toField_def] at h
  have Neg1 := eq_one_iff_isNeg_toField hn1
  have E1 : e1.toField = if fe.toField.isNeg then st.g.toField else st.e.toField :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [he10 h]) (fun h => by rw [he11 h])
  have G1 : g1.toField = if fe.toField.isNeg then -st.e.toField else st.g.toField :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [hg10 h])
      (fun h => by rw [hg11 h]; exact toField_neg_of_mod hme)
  have H1 : h1.toField = if fe.toField.isNeg then st.f.toField * sqrtM1 else st.h.toField :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [hh10 h])
      (fun h => by rw [hh11 h, toField_mul_of_mod hfts, Fi])
  have M1 : mg1.toField = if fe.toField.isNeg then (sqrtM1 : ZMod p) else magic.toField :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [hmg10 h]) (fun h => by rw [hmg11 h, Fi])
  have G2 : g2.toField = if fe3.toField.isNeg then -g1.toField else g1.toField :=
    eq_ite_of_choice hn2v (eq_one_iff_isNeg_toField hn2) (fun h => by rw [hg20 h])
      (fun h => toField_neg_of_mod (hg21 h).1)
  have S1 : s1.toField = sv.toField.abs :=
    eq_ite_of_choice hsnv (eq_one_iff_isNeg_toField hsn) (fun h => by rw [hs10 h])
      (fun h => toField_neg_of_mod (hs11 h).1)
  -- the point
  obtain ⟨hZ0, hXYZT, -⟩ :=
    (edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff_equation _).mp hP
  rw [CompressedRistretto.asNat_def, hbytes, ← toField_val, S1,
    ← RistrettoCompress.doubleCompress_eq_encodeRep _ C hZ0 hXYZT
      (edwards.EdwardsPoint.«x86_64-no-tables».toPoint_x hP)
      (edwards.EdwardsPoint.«x86_64-no-tables».toPoint_y hP), ← Se, ← Sf, ← Sg, ← Sh]
  congr 1
  dsimp only [RistrettoCompress.doubleCompress]
  rw [toField_mul_of_mod hsv, toField_sub_of_mod hfe4, toField_mul_of_mod hfe6,
    toField_mul_of_mod hfe5, G2, toField_mul_of_mod hfe3, toField_mul_of_mod hfe2, H1, E1, G1,
    M1, toField_mul_of_mod hfe, toField_mul_of_mod hZinv, toField_mul_of_mod hTinv, Inv, Seg,
    Sfh]


open scoped Helpers.IndexStep in
/-- The second loop: entry `k` encodes `2 P_k`, from the state and the inverse of `e g · f h`. -/
private theorem loop1_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (ps : List RistrettoPoint.«x86_64-no-tables») (hsts : List.Forall₂ StateOf ps states.val)
    (hon : ∀ P ∈ ps, P.OnCurve) (invs : alloc.vec.Vec FieldElement51)
    (hinvs : ∀ k < states.length, invs[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧ (invs[k]!).LimbsLt 52)
    (hinvlen : invs.length = states.length)
    (out : alloc.vec.Vec CompressedRistretto) (i : Usize) (hi : i.val ≤ states.length)
    (hlen : out.length = i.val)
    (hout : ∀ k < i.val, out[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) :
    double_and_compress_batch_loop1 states invs out i ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = states.length ∧
        ∀ k < states.length, r[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint) ⦄ := by
  have hpslen : ps.length = states.length := by
    rw [hsts.length_eq]
  unfold double_and_compress_batch_loop1
  apply loop.spec_decr_nat (measure := fun (_, i') => states.length - i'.val)
    (inv := fun (o, i') => i'.val ≤ states.length ∧ o.length = i'.val ∧ ∀ k < i'.val,
      o[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint))
  · rintro ⟨o, i'⟩ ⟨hi', hl, ho⟩
    dsimp only
    rw [loop1_body_eq]
    by_cases hlt : i'.val < states.length
    · have hlt' : i' < states.len := by
        rw [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact hlt
      simp only [hlt', ite_true]
      step as ⟨st, hst⟩
      replace hst : st = states[i'.val]! := by
        rw [hst, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      step as ⟨inv, hinv⟩
      replace hinv : inv = invs[i'.val]! := by
        rw [hinv, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      obtain ⟨Inv, Invb⟩ := hinvs i'.val hlt
      rw [← hst, ← hinv] at Inv
      rw [← hinv] at Invb
      rw [alloc.vec.Vec.getElem!_Nat_eq] at hst
      have hPmem : ps[i'.val]! ∈ ps := by
        rw [getElem!_pos ps i'.val (hpslen ▸ hlt)]
        exact List.getElem_mem _
      have hS := forall₂_getElem! hsts i'.val (hpslen ▸ hlt)
      rw [← hst] at hS
      step with compressState_spec _ (hon _ hPmem) st hS inv Inv Invb as ⟨bytes, hbytes⟩
      step as ⟨o1, ho1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
        x.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) ho1 (hl ▸ ho) ?_
      rw [hl]
      exact hbytes
    · have hlt' : ¬ i' < states.len := by
        rw [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact hlt
      simp only [hlt', ite_false, WP.spec_ok]
      have hin : i'.val = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ ho⟩
  · exact ⟨hi, hlen, hout⟩

/-- `RistrettoPoint::double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for
the points `P_i` the input yields; limbs `< 2^52`. -/
@[step]
theorem double_and_compress_batch_spec {I Clause0_IntoIter : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«x86_64-no-tables» Clause0_IntoIter)
    (points : I) (ps : List RistrettoPoint.«x86_64-no-tables»)
    (hpoints : pointsInst.Yields points ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = ps.length ∧
        ∀ i < ps.length, r[i]!.asNat = Ristretto.encodeRep (2 • (ps[i]!).toPoint) ⦄ := by
  unfold double_and_compress_batch
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ps ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  step with states_spec _ it ps hit (fun P hP => (hps P hP).1) hlen as ⟨states, hsts⟩
  have hpslen : ps.length = states.length := hsts.length_eq
  have hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 52 ∧ (states[k]!).fh.LimbsLt 52 :=
    fun k hk => by
      have h := forall₂_getElem! hsts k (hpslen ▸ hk)
      rw [alloc.vec.Vec.getElem!_Nat_eq]
      exact ⟨h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩
  step with loop0_spec states hst (alloc.vec.Vec.with_capacity FieldElement51 states.len) 0#usize
    (by simp) (by rfl) (fun k hk => absurd hk (by simp)) as ⟨invs1, hinvs1len, hinvs1⟩
  simp only [alloc.vec.Vec.index_mut, pure]
  have hsb : ∀ k < invs1.slice.length, (invs1.slice[k]!).LimbsLt 54 := fun k hk => by
    rw [alloc.vec.Vec.getElem!_slice]
    exact limbs_lt_of_le (by decide) (hinvs1 k (hinvs1len ▸ hk)).2
  step as ⟨s1, hs1len, hs1⟩
  have hslen : invs1.slice.length = states.length := hinvs1len
  have hinvs : ∀ k < states.length, ({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧
      (({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!).LimbsLt 52 := by
    intro k hk
    obtain ⟨h0, h1⟩ := hs1 k (hslen ▸ hk)
    obtain ⟨hv, hb⟩ := hinvs1 k hk
    rw [alloc.vec.Vec.getElem!_slice] at h0 h1
    rw [alloc.vec.Vec.getElem!_mk, ← hv]
    exact toField_inv_of_batch h0 h1 hb
  step with loop1_spec states ps hsts (fun P hP => (hps P hP).2) _ hinvs
    (by rw [alloc.vec.Vec.length]; exact hs1len.trans hslen)
    (alloc.vec.Vec.with_capacity CompressedRistretto states.len) 0#usize (by simp) (by rfl)
    (fun k hk => absurd hk (by simp)) as ⟨r, hrlen, hr⟩
  exact ⟨hrlen.trans hpslen.symm, fun k hk => hr k (hpslen ▸ hk)⟩

end «RistrettoPointx86_64-no-tables»

end Curve25519Dalek.ristretto
