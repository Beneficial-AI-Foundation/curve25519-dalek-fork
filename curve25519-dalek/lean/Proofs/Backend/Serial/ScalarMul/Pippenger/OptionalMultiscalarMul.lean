/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Edwards.Add
import Proofs.Edwards.AddAssign
import Proofs.Edwards.AsProjectiveNiels
import Proofs.Edwards.Identity
import Proofs.Edwards.MulByPow2
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.AsInt
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.AsRadix2w
import Proofs.Scalar.ToRadix2wSizeHint
public section

/-! # `Pippenger::optional_multiscalar_mul`

Pippenger's bucket method with radix-`2^w` digits (`w ∈ {6, 7, 8}` by the input size): for each
digit position `e` from the top, the points are added into the buckets `1, …, 2^(w-1)` by the
absolute value of their digit (subtracted for a negative digit), the buckets are combined into
`∑_b b • bucket_b = ∑_i d_i[e] • P_i` by two running sums, and the column is added to `2^w •` the
total. Only the first `min(|scalars|, |points|)` pairs are used (the patched zip); a `None`
among them gives `None`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.pippenger

/-- `Forall₂` as a statement about the entries `getElem!`. -/
private theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    l₁.length = l₂.length ∧ ∀ k < l₁.length, R l₁[k]! l₂[k]! := by
  refine ⟨h.length_eq, fun k hk => ?_⟩
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (h.length_eq ▸ hk)]
  exact (List.forall₂_iff_get.mp h).2 k hk _

/-- The pairs actually used: with no `none` among the first `|ss|` points, the sum over the
`zipWith` with the `some` points is the sum over the first `min |ss| |ops|` indices. -/
private theorem sum_zipWith_filterMap {α β G : Type} [Inhabited α] [Inhabited β]
    [AddCommMonoid G] (f : α → β → G) (ss : List α) (ops : List (Option β))
    (h : none ∉ ops.take ss.length) :
    (List.zipWith f ss (ops.filterMap id)).sum =
      ∑ k ∈ Finset.range (min ss.length ops.length), f ss[k]! (ops[k]!.getD default) := by
  induction ss generalizing ops with
  | nil => simp
  | cons s ss ih =>
    cases ops with
    | nil => simp
    | cons o ops =>
      rcases o with _ | b
      · simp at h
      · rw [List.filterMap_cons_some (by rfl), List.zipWith_cons_cons, List.sum_cons,
          ih ops (by simpa using h), List.length_cons, List.length_cons, Nat.add_min_add_right,
          Finset.sum_range_succ']
        simp [add_comm]

/-- The digits of position `< dc` give the value, if the others vanish. -/
private theorem sum_digits (d : Array I8 64#usize) (w dc : ℕ) (hdc : dc ≤ 64)
    (hz : ∀ j < 64, dc ≤ j → d[j]!.val = 0) :
    ∑ j ∈ Finset.range dc, 2 ^ (w * j) * d[j]!.val = d.asInt w := by
  rw [Array.asInt_eq_sum, show (64#usize).val = 64 from rfl,
    ← Finset.sum_range_add_sum_Ico _ hdc]
  have h0 : ∑ j ∈ Finset.Ico dc 64, (2 : ℤ) ^ (w * j) * d[j]!.val = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have := Finset.mem_Ico.mp hj
      rw [hz j this.2 this.1, mul_zero]
  rw [h0, add_zero]

/-- Exchanging the sums over the digit positions and the points. -/
private theorem sum_columns (m dc w : ℕ) (d : ℕ → Array I8 64#usize)
    (P : ℕ → curve25519.edwards.Point) :
    ∑ j ∈ Finset.range dc, 2 ^ (w * j) • ∑ k ∈ Finset.range m, ((d k)[j]!.val : ℤ) • P k =
      ∑ k ∈ Finset.range m, (∑ j ∈ Finset.range dc, 2 ^ (w * j) * (d k)[j]!.val) • P k := by
  simp_rw [Finset.smul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← natCast_zsmul, smul_smul]
  push_cast
  rfl

/-- The weighted sum `∑_{b < n} (b + 1) • f l[b]` of the buckets `l`. -/
private noncomputable def wsum {α : Type} [Inhabited α] (f : α → curve25519.edwards.Point)
    (l : List α)
    (n : ℕ) : curve25519.edwards.Point :=
  ∑ b ∈ Finset.range n, (b + 1) • f l[b]!

private theorem getElem!_set_ne' {α : Type} [Inhabited α] (l : List α) (b j : ℕ) (x : α)
    (h : j ≠ b) : (l.set b x)[j]! = l[j]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.getElem?_set_ne (Ne.symm h)]

private theorem getElem!_set_eq' {α : Type} [Inhabited α] (l : List α) (b : ℕ) (x : α)
    (h : b < l.length) : (l.set b x)[b]! = x := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

/-- Changing bucket `b` changes the weighted sum by `(b + 1) •` the change. -/
private theorem wsum_set {α : Type} [Inhabited α] (f : α → curve25519.edwards.Point)
    (l : List α) (n b : ℕ) (hb : b < n) (hl : l.length = n) (x : α) :
    wsum f (l.set b x) n = wsum f l n + (b + 1) • (f x - f l[b]!) := by
  unfold wsum
  have hmem : b ∈ Finset.range n := Finset.mem_range.mpr hb
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem,
    getElem!_set_eq' l b x (hl ▸ hb)]
  have hrest : ∑ j ∈ (Finset.range n).erase b, (j + 1) • f (l.set b x)[j]! =
      ∑ j ∈ (Finset.range n).erase b, (j + 1) • f l[j]! :=
    Finset.sum_congr rfl fun j hj => by
      rw [getElem!_set_ne' l b j x (Finset.ne_of_mem_erase hj)]
  rw [hrest, smul_sub]
  abel

/-- The running sums of `optional_multiscalar_mul`: `∑_{b ∈ [i, n)} (b - i + 1) • B b`. -/
private theorem running_sum_step (B : ℕ → curve25519.edwards.Point) (i n : ℕ) (hi : i < n) :
    (∑ b ∈ Finset.Ico (i + 1) n, (b - (i + 1) + 1) • B b) + ∑ b ∈ Finset.Ico i n, B b =
      ∑ b ∈ Finset.Ico i n, (b - i + 1) • B b := by
  rw [Finset.sum_eq_sum_Ico_succ_bot hi, Finset.sum_eq_sum_Ico_succ_bot hi,
    show i - i + 1 = 1 by omega, one_smul]
  have h : ∀ b ∈ Finset.Ico (i + 1) n, (b - i + 1) • B b = (b - (i + 1) + 1) • B b + B b :=
    fun b hb => by
      have := (Finset.mem_Ico.mp hb).1
      rw [show b - i + 1 = (b - (i + 1) + 1) + 1 by omega, succ_nsmul]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  abel

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
    (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
    (sub_spec_point)

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

/-- The buckets of `optional_multiscalar_mul`: `n` points on the curve within the limb bounds. -/
private def BucketsOK (v : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables») (n : ℕ) : Prop :=
  v.length = n ∧ ∀ j < n, v.val[j]!.OnCurve ∧ v.val[j]!.LimbsLt 52

open edwards.EdwardsPoint.«x86_64-tables».Insts in
/-- The first loop: `buckets_count` identities. -/
@[local step]
private theorem optional_multiscalar_mul_loop0_spec (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables») (b : Usize) (hbc : bc.val ≤ 128)
    (hb : b.val ≤ bc.val) (hlen : buckets.length = b.val)
    (hbk : ∀ j < b.val, buckets.val[j]!.OnCurve ∧ buckets.val[j]!.LimbsLt 52 ∧
      buckets.val[j]!.toPoint = 0) :
    optional_multiscalar_mul_loop0 bc buckets b
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables») => BucketsOK r bc.val ⦄ := by
  unfold optional_multiscalar_mul_loop0
  apply loop.spec_decr_nat (measure := fun (_, b') => bc.val - b'.val)
    (inv := fun (v, b') => b'.val ≤ bc.val ∧ v.length = b'.val ∧
      ∀ j < b'.val, v.val[j]!.OnCurve ∧ v.val[j]!.LimbsLt 52 ∧ v.val[j]!.toPoint = 0)
  · rintro ⟨v, b'⟩ ⟨hb', hl, hv⟩
    unfold optional_multiscalar_mul_loop0.body
    by_cases hlt : b' < bc
    · simp only [hlt, ite_true]
      step with Curve25519_dalekTraitsIdentity.identity_spec_point
        as ⟨e, heon, he, heb⟩
      step as ⟨v1, hv1⟩
      step as ⟨b1, hb1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hv1, hl, hb1], ?_,
        by scalar_tac⟩
      rw [hb1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append
        (P := fun _ x => x.OnCurve ∧ x.LimbsLt 52 ∧ x.toPoint = 0) hv1 (hl ▸ hv) ⟨heon, heb, he⟩
    · simp only [hlt, ite_false, WP.spec_ok]
      have : b'.val = bc.val := by scalar_tac
      exact ⟨this ▸ hl, fun j hj => ⟨(hv j (this ▸ hj)).1, (hv j (this ▸ hj)).2.1⟩⟩
  · exact ⟨hb, hlen, hbk⟩

open edwards.EdwardsPoint.«x86_64-tables».Insts in
/-- The reset loop: every bucket becomes the identity. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop0_spec (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables») (b : Usize)
    (hok : BucketsOK buckets bc.val) (hb : b.val ≤ bc.val)
    (hz : ∀ j < b.val, buckets.val[j]!.toPoint = 0) :
    optional_multiscalar_mul_loop1_loop0 bc buckets b
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables») =>
        BucketsOK r bc.val ∧ ∀ j < bc.val, r.val[j]!.toPoint = 0 ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop0
  apply loop.spec_decr_nat (measure := fun (_, b') => bc.val - b'.val)
    (inv := fun (v, b') => b'.val ≤ bc.val ∧ BucketsOK v bc.val ∧
      ∀ j < b'.val, v.val[j]!.toPoint = 0)
  · rintro ⟨v, b'⟩ ⟨hb', ⟨hl, hv⟩, hvz⟩
    unfold optional_multiscalar_mul_loop1_loop0.body
    by_cases hlt : b' < bc
    · simp only [hlt, ite_true]
      step with Curve25519_dalekTraitsIdentity.identity_spec_point
        as ⟨e, heon, he, heb⟩
      step as ⟨x, back, hx, hback⟩
      step as ⟨b1, hb1⟩
      have hbl : b'.val < v.val.length := by
        rw [show v.val.length = v.length from rfl, hl]; scalar_tac
      refine ⟨by scalar_tac, ⟨?_, fun j hj => ?_⟩, fun j hj => ?_, by scalar_tac⟩
      · rw [hback, alloc.vec.Vec.set_length, hl]
      · rw [hback, alloc.vec.Vec.set_val_eq]
        rcases eq_or_ne j b'.val with rfl | hne
        · rw [getElem!_set_eq' _ _ _ hbl]; exact ⟨heon, heb⟩
        · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
      · rw [hback, alloc.vec.Vec.set_val_eq]
        rcases eq_or_ne j b'.val with rfl | hne
        · rw [getElem!_set_eq' _ _ _ hbl]; exact he
        · rw [getElem!_set_ne' _ _ _ _ hne]; exact hvz j (by scalar_tac)
    · simp only [hlt, ite_false, WP.spec_ok]
      have : b'.val = bc.val := by scalar_tac
      exact ⟨⟨hl, hv⟩, fun j hj => hvz j (this ▸ hj)⟩
  · exact ⟨hb, hok, hz⟩

open edwards.EdwardsPoint.«x86_64-tables».Insts in
/-- The running sums: `buckets_sum` ends as `∑_b (b + 1) • bucket_b`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop2_spec
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables») (bc : ℕ)
    (hok : BucketsOK buckets bc) (inter sum : edwards.EdwardsPoint.«x86_64-tables») (i : Usize)
    (hi : i.val < bc) (hinter : inter.OnCurve ∧ inter.LimbsLt 52 ∧
      inter.toPoint = ∑ b ∈ Finset.Ico i.val bc, buckets.val[b]!.toPoint)
    (hsum : sum.OnCurve ∧ sum.LimbsLt 52 ∧
      sum.toPoint = ∑ b ∈ Finset.Ico i.val bc, (b - i.val + 1) • buckets.val[b]!.toPoint) :
    optional_multiscalar_mul_loop1_loop2 buckets inter sum i
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») => r.OnCurve ∧ r.LimbsLt 52 ∧
        r.toPoint = wsum edwards.EdwardsPoint.«x86_64-tables».toPoint buckets.val bc ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop2
  apply loop.spec_decr_nat (measure := fun (_, _, i') => i'.val)
    (inv := fun (it, sm, i') => i'.val < bc ∧
      it.OnCurve ∧ it.LimbsLt 52 ∧
        it.toPoint = ∑ b ∈ Finset.Ico i'.val bc, buckets.val[b]!.toPoint ∧
      sm.OnCurve ∧ sm.LimbsLt 52 ∧
        sm.toPoint = ∑ b ∈ Finset.Ico i'.val bc, (b - i'.val + 1) • buckets.val[b]!.toPoint)
  · rintro ⟨it, sm, i'⟩ ⟨hi', hiton, hitb, hitp, hsmon, hsmb, hsmp⟩
    unfold optional_multiscalar_mul_loop1_loop2.body
    by_cases hpos : i' > 0#usize
    · simp only [hpos, ite_true]
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < bc := by scalar_tac
      step as ⟨ep, hep⟩
      rw [← getElem!_pos] at hep
      obtain ⟨hepon, hepb⟩ := hok.2 i1.val hi1b
      rw [← hep] at hepon hepb
      step with «CoreOpsArithAddAssignEdwardsPointx86_64-tables».add_assign_spec_point
        it ep hitb hepb hiton hepon as ⟨it1, hit1on, hit1, hit1b⟩
      step with «CoreOpsArithAddAssignEdwardsPointx86_64-tables».add_assign_spec_point
        sm it1 hsmb hit1b hsmon hit1on as ⟨sm1, hsm1on, hsm1, hsm1b⟩
      have hii : i'.val = i1.val + 1 := by scalar_tac
      have hsum1 : ∑ b ∈ Finset.Ico i1.val bc, buckets.val[b]!.toPoint =
          ∑ b ∈ Finset.Ico i'.val bc, buckets.val[b]!.toPoint + ep.toPoint := by
        rw [Finset.sum_eq_sum_Ico_succ_bot hi1b, hii, hep, add_comm]
      refine ⟨hi1b, hit1on, hit1b, by rw [hit1, hitp, hsum1], hsm1on, hsm1b, ?_,
        by rw [hii]; exact Nat.lt_succ_self _⟩
      rw [hsm1, hit1, hsmp, hitp, ← hsum1, hii]
      exact running_sum_step (fun b => buckets.val[b]!.toPoint) i1.val bc hi1b
    · simp only [hpos, ite_false, WP.spec_ok]
      have h0 : i'.val = 0 := by scalar_tac
      refine ⟨hsmon, hsmb, ?_⟩
      rw [hsmp, h0, wsum, Finset.range_eq_Ico]
      exact Finset.sum_congr rfl fun b _ => by rw [Nat.sub_zero]
  · exact ⟨hi, hinter.1, hinter.2.1, hinter.2.2, hsum.1, hsum.2.1, hsum.2.2⟩

open scoped Helpers.IndexStep in
/-- The accumulation loop: point `k` (from `si` on) is added to bucket `d_k[e] - 1`, or subtracted
from bucket `-d_k[e] - 1`; the weighted sum of the buckets grows by `d_k[e] • P_k`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop1_spec
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables») (e si : Usize) (bc : ℕ)
    (P : ℕ → curve25519.edwards.Point) (he : e.val < 64) (hbc : bc ≤ 128)
    (hsp : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 54 ∧
      (sp.val[k]!).2.toPoint = P k)
    (hdig : ∀ k < sp.length, -(bc : ℤ) ≤ (sp.val[k]!).1[e.val]!.val ∧
      (sp.val[k]!).1[e.val]!.val ≤ bc)
    (hok : BucketsOK buckets bc) (hsi : si.val ≤ sp.length) :
    optional_multiscalar_mul_loop1_loop1 sp buckets e si
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables») => BucketsOK r bc ∧
        wsum edwards.EdwardsPoint.«x86_64-tables».toPoint r.val bc =
          wsum edwards.EdwardsPoint.«x86_64-tables».toPoint buckets.val bc +
            ∑ k ∈ Finset.Ico si.val sp.length, (sp.val[k]!).1[e.val]!.val • P k ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop1
  apply loop.spec_decr_nat (measure := fun (_, si') => sp.length - si'.val)
    (inv := fun (v, si') => si.val ≤ si'.val ∧ si'.val ≤ sp.length ∧ BucketsOK v bc ∧
      wsum edwards.EdwardsPoint.«x86_64-tables».toPoint v.val bc =
        wsum edwards.EdwardsPoint.«x86_64-tables».toPoint buckets.val bc +
          ∑ k ∈ Finset.Ico si.val si'.val, (sp.val[k]!).1[e.val]!.val • P k)
  · rintro ⟨v, si'⟩ ⟨hss, hsl, ⟨hvl, hv⟩, hw⟩
    unfold optional_multiscalar_mul_loop1_loop1.body
    by_cases hlt : si'.val < sp.length
    · have hlt' : si' < alloc.vec.Vec.len sp := by scalar_tac
      simp only [hlt', ite_true]
      step as ⟨digits, pt, hdp⟩
      rw [← getElem!_pos] at hdp
      obtain ⟨hpton, hptb, hptp⟩ := hsp si'.val hlt
      obtain ⟨hdl, hdu⟩ := hdig si'.val hlt
      rw [← hdp] at hpton hptb hptp hdl hdu
      simp only at hpton hptb hptp hdl hdu
      step as ⟨d8, hd8⟩
      step with IScalar.cast_inBounds_spec as ⟨d, hd⟩
      rw [show lift (core.cmp.impls.OrdI16.cmp d 0#i16) = ok (compare d.val 0) from rfl, bind_ok]
      apply spec_bind (Pₘ := fun v1 => BucketsOK v1 bc ∧
        wsum edwards.EdwardsPoint.«x86_64-tables».toPoint v1.val bc =
          wsum edwards.EdwardsPoint.«x86_64-tables».toPoint v.val bc + d.val • P si'.val)
      · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
        · rw [(compare_lt_iff_lt).mpr hneg]
          simp only
          step as ⟨i2, hi2⟩
          step as ⟨i3, hi3⟩
          step with IScalar.hcast_inBounds_spec as ⟨b, hb⟩
          have hbv : b.val + 1 = (-d.val).toNat := by scalar_tac
          have hbl : b.val < bc := by scalar_tac
          step as ⟨ep, hep⟩
          rw [← getElem!_pos] at hep
          obtain ⟨hepon, hepb⟩ := hv b.val hbl
          rw [← hep] at hepon hepb
          step with sub_spec_point ep pt hepb hptb hepon hpton as ⟨c, hcon, hc, hcb⟩
          step with «CompletedPointx86_64-tables».as_extended_spec_point as
              ⟨ep1, hep1on, hep1, hep1b⟩
          step as ⟨y, back, hy, hback⟩
          have hbl' : b.val < v.val.length := by
            rw [show v.val.length = v.length from rfl, hvl]; exact hbl
          refine ⟨⟨by rw [hback, alloc.vec.Vec.set_length, hvl], fun j hj => ?_⟩, ?_⟩
          · rw [hback, alloc.vec.Vec.set_val_eq]
            rcases eq_or_ne j b.val with rfl | hne
            · rw [getElem!_set_eq' _ _ _ hbl']; exact ⟨hep1on, hep1b⟩
            · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
          · rw [hback, alloc.vec.Vec.set_val_eq, wsum_set _ _ _ _ hbl hvl, hep1, hc, ← hep, hptp]
            congr 1
            rw [sub_sub_cancel_left, smul_neg, ← natCast_zsmul, ← neg_zsmul]
            congr 1
            push_cast
            omega
        · rw [(compare_eq_iff_eq).mpr hzero]
          simp only [WP.spec_ok]
          rw [hzero, zero_smul, add_zero]
          exact ⟨⟨hvl, hv⟩, rfl⟩
        · rw [(compare_gt_iff_gt).mpr hpos]
          simp only
          step as ⟨i2, hi2⟩
          step with IScalar.hcast_inBounds_spec as ⟨b, hb⟩
          have hbv : b.val + 1 = d.val.toNat := by scalar_tac
          have hbl : b.val < bc := by scalar_tac
          step as ⟨ep, hep⟩
          rw [← getElem!_pos] at hep
          obtain ⟨hepon, hepb⟩ := hv b.val hbl
          rw [← hep] at hepon hepb
          step with add_spec_point ep pt hepb hptb hepon hpton as ⟨c, hcon, hc, hcb⟩
          step with «CompletedPointx86_64-tables».as_extended_spec_point as
              ⟨ep1, hep1on, hep1, hep1b⟩
          step as ⟨y, back, hy, hback⟩
          have hbl' : b.val < v.val.length := by
            rw [show v.val.length = v.length from rfl, hvl]; exact hbl
          refine ⟨⟨by rw [hback, alloc.vec.Vec.set_length, hvl], fun j hj => ?_⟩, ?_⟩
          · rw [hback, alloc.vec.Vec.set_val_eq]
            rcases eq_or_ne j b.val with rfl | hne
            · rw [getElem!_set_eq' _ _ _ hbl']; exact ⟨hep1on, hep1b⟩
            · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
          · rw [hback, alloc.vec.Vec.set_val_eq, wsum_set _ _ _ _ hbl hvl, hep1, hc, ← hep, hptp]
            congr 1
            rw [add_sub_cancel_left, ← natCast_zsmul]
            congr 1
            push_cast
            omega
      · rintro v1 ⟨hok1, hw1⟩
        step as ⟨si1, hsi1⟩
        refine ⟨by scalar_tac, by scalar_tac, hok1, ?_, by scalar_tac⟩
        rw [hw1, hw, show si1.val = si'.val + 1 by scalar_tac, Finset.sum_Ico_succ_top hss,
          add_assoc, hd, hd8, ← hdp]
    · have hge : ¬ si' < alloc.vec.Vec.len sp := by scalar_tac
      simp only [hge, ite_false, WP.spec_ok]
      have : si'.val = sp.length := by scalar_tac
      exact ⟨⟨hvl, hv⟩, this ▸ hw⟩
  · exact ⟨le_refl _, hsi, hok, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The column of digit position `e`: `∑_k d_k[e] • P_k`. -/
private noncomputable def column
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-tables»))
    (P : ℕ → curve25519.edwards.Point) (e : ℕ) : curve25519.edwards.Point :=
  ∑ k ∈ Finset.range sp.length, ((sp.val[k]!).1[e]!.val : ℤ) • P k

open edwards.EdwardsPoint.«x86_64-tables».Insts in
open scoped Helpers.IndexStep in
/-- The outer loop over the digit positions, from the top: the total is
`∑_{j} 2^(w j) • column (di + j)` over the positions processed. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_spec (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables»)
    (total : Option edwards.EdwardsPoint.«x86_64-tables») (di : Usize)
    (P : ℕ → curve25519.edwards.Point) (dc : ℕ) (hw : 0 < w.val ∧ w.val ≤ 8)
    (hbc1 : 1 ≤ bc.val) (hbc : bc.val ≤ 128) (hdc : dc ≤ 64)
    (hsp : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 54 ∧
      (sp.val[k]!).2.toPoint = P k)
    (hdig : ∀ k < sp.length, ∀ e < 64, -(bc.val : ℤ) ≤ (sp.val[k]!).1[e]!.val ∧
      (sp.val[k]!).1[e]!.val ≤ (bc.val : ℤ))
    (hok : BucketsOK buckets bc.val) (hdi : di.val ≤ dc)
    (hnone : total = none ↔ di.val = dc)
    (hsome : ∀ T, total = some T → T.OnCurve ∧ T.LimbsLt 52 ∧
      T.toPoint = ∑ j ∈ Finset.range (dc - di.val), 2 ^ (w.val * j) • column sp P (di.val + j)) :
    optional_multiscalar_mul_loop1 w bc sp buckets total di
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (r = none ↔ dc = 0) ∧
        ∀ T, r = some T → T.OnCurve ∧ T.LimbsLt 52 ∧
          T.toPoint = ∑ j ∈ Finset.range dc, 2 ^ (w.val * j) • column sp P j ⦄ := by
  unfold optional_multiscalar_mul_loop1
  apply loop.spec_decr_nat (measure := fun (_, _, d) => d.val)
    (inv := fun (v, t, d) => BucketsOK v bc.val ∧ d.val ≤ dc ∧ (t = none ↔ d.val = dc) ∧
      ∀ T, t = some T → T.OnCurve ∧ T.LimbsLt 52 ∧
        T.toPoint = ∑ j ∈ Finset.range (dc - d.val), 2 ^ (w.val * j) • column sp P (d.val + j))
  · rintro ⟨v, t, d⟩ ⟨hv, hd, htn, hts⟩
    unfold optional_multiscalar_mul_loop1.body
    by_cases hpos : d > 0#usize
    · simp only [hpos, ite_true]
      step as ⟨d1, hd1⟩
      have hdpos : 0 < d.val := hpos
      have hdd : d.val = d1.val + 1 := by rw [hd1]; exact (Nat.sub_add_cancel hdpos).symm
      have hd1lt : d1.val < dc := by
        rw [hd1]; exact lt_of_lt_of_le (Nat.sub_lt hdpos Nat.one_pos) hd
      have hd164 : d1.val < 64 := lt_of_lt_of_le hd1lt hdc
      step with optional_multiscalar_mul_loop1_loop0_spec bc v 0#usize hv (Nat.zero_le _)
        (fun j hj => absurd hj (Nat.not_lt_zero j)) as ⟨v1, hv1, hv1z⟩
      step with optional_multiscalar_mul_loop1_loop1_spec sp v1 d1 0#usize bc.val P
        hd164 hbc hsp (fun k hk => hdig k hk d1.val hd164) hv1
        (Nat.zero_le _) as ⟨v2, hv2, hw2⟩
      step as ⟨i, hi⟩
      have hib : i.val < bc.val := by
        rw [hi]; exact Nat.sub_lt (lt_of_lt_of_le Nat.one_pos hbc1) Nat.one_pos
      have hil : i.val < v2.val.length := by
        rw [show v2.val.length = v2.length from rfl, hv2.1]; exact hib
      step as ⟨inter, hinter⟩
      rw [← getElem!_pos] at hinter
      step as ⟨sm, hsm⟩
      rw [← getElem!_pos] at hsm
      have hIco : Finset.Ico i.val bc.val = {i.val} := by
        rw [show bc.val = i.val + 1 by rw [hi]; exact (Nat.sub_add_cancel hbc1).symm,
          Nat.Ico_succ_singleton]
      obtain ⟨hion, hib'⟩ := hv2.2 i.val hib
      step with optional_multiscalar_mul_loop1_loop2_spec v2 bc.val hv2 inter sm i hib
        ⟨hinter ▸ hion, hinter ▸ hib', by rw [hIco, Finset.sum_singleton, hinter]⟩
        ⟨hsm ▸ hion, hsm ▸ hib', by
          rw [hIco, Finset.sum_singleton, hsm, Nat.sub_self, zero_add, one_smul]⟩
        as ⟨c, hcon, hcb, hc⟩
      have hzero : wsum edwards.EdwardsPoint.«x86_64-tables».toPoint v1.val bc.val = 0 :=
        Finset.sum_eq_zero fun b hb => by rw [hv1z b (Finset.mem_range.mp hb), smul_zero]
      have hcol : c.toPoint = column sp P d1.val := by
        rw [hc, hw2, hzero, zero_add, ← Finset.range_eq_Ico]
        rfl
      rcases t with _ | T
      · have hdc' : d.val = dc := htn.mp rfl
        dsimp only
        rw [WP.spec_ok]
        refine ⟨hv2, Nat.le_of_lt hd1lt,
          ⟨fun h => (by cases h), fun h => absurd h (Nat.ne_of_lt hd1lt)⟩,
          fun T' hT' => ?_, by rw [hdd]; exact Nat.lt_succ_self _⟩
        obtain rfl : c = T' := Option.some.inj hT'
        refine ⟨hcon, hcb, ?_⟩
        rw [hcol, show dc - d1.val = 1 by rw [← hdc', hdd, Nat.add_sub_cancel_left],
          Finset.sum_range_one, mul_zero, pow_zero, one_smul, add_zero]
      · obtain ⟨hTon, hTb, hT⟩ := hts T rfl
        have hdc' : d.val ≠ dc := fun h => by cases htn.mpr h
        dsimp only
        step as ⟨k, hk⟩
        have hkw : k.val = w.val := by
          rw [hk, UScalar.cast_val_eq]
          exact Nat.mod_eq_of_lt (lt_of_le_of_lt hw.2 (by decide))
        step with edwards.«EdwardsPointx86_64-tables».mul_by_pow_2_spec T k hTb hTon
            (by rw [hkw]; exact hw.1)
          as ⟨T2, hT2on, hT2, hT2b⟩
        step with «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».add_spec_point
          T2 c hT2b hcb hT2on hcon as ⟨T3, hT3on, hT3, hT3b⟩
        refine ⟨hv2, Nat.le_of_lt hd1lt,
          ⟨fun h => (by cases h), fun h => absurd h (Nat.ne_of_lt hd1lt)⟩,
          fun T' hT' => ?_, by rw [hdd]; exact Nat.lt_succ_self _⟩
        obtain rfl : T3 = T' := Option.some.inj hT'
        refine ⟨hT3on, hT3b, ?_⟩
        have hdcd : dc - d1.val = (dc - d.val) + 1 := by
          rw [hdd, Nat.sub_add_eq]
          exact (Nat.sub_add_cancel (Nat.sub_pos_of_lt hd1lt)).symm
        rw [hT3, hT2, hT, hcol, hkw, hdcd, Finset.sum_range_succ', Finset.smul_sum]
        rw [mul_zero, pow_zero, one_smul, add_zero]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, ← pow_add, hdd, show w.val + w.val * j = w.val * (j + 1) by ring,
          show d1.val + 1 + j = d1.val + (j + 1) by ring]
    · simp only [hpos, ite_false, WP.spec_ok]
      have h0 : d.val = 0 := by scalar_tac
      refine ⟨by rw [htn, h0]; exact eq_comm, fun T hT => ?_⟩
      obtain ⟨hTon, hTb, hT'⟩ := hts T hT
      refine ⟨hTon, hTb, ?_⟩
      rw [hT', h0, Nat.sub_zero]
      exact Finset.sum_congr rfl fun j _ => by rw [zero_add]
  · exact ⟨hok, hdi, hnone, hsome⟩

/-- The pairs collected by `scalars_points`, up to `m`: digits of `ss[j]` and the projective Niels
form of the point `ops[j] = some P`. -/
private def PairsOK (w : ℕ) (ss : List scalar.Scalar)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-tables»))
    (v : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-tables»)) (m : ℕ) : Prop
        :=
  v.length = m ∧ ∀ j < m, ∃ P, ops[j]! = some P ∧
    (v.val[j]!).2.OnCurve ∧ (v.val[j]!).2.LimbsLt 54 ∧ (v.val[j]!).2.toPoint = P.toPoint ∧
    (v.val[j]!).1.asInt w = ss[j]!.asNat ∧
    (∀ i < 64, -2 ^ w ≤ 2 * (v.val[j]!).1[i]!.val ∧ 2 * (v.val[j]!).1[i]!.val ≤ 2 ^ w) ∧
    ∀ i < 64, 256 < i * w → (v.val[j]!).1[i]!.val = 0

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

namespace «VartimeMultiscalarMulPippengerEdwardsPointx86_64-tables».optional_multiscalar_mul

open Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

/-- The loop of `scalars_points`: the digits of each scalar with the next point, until the
scalars or the points run out; `none` at the first `none` point. -/
@[local step]
private theorem scalars_points_loop_spec {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It (Option edwards.EdwardsPoint.«x86_64-tables»))
    (scalars : Slice S) (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) scalars.val ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (w : Usize) (hw : 4 ≤ w.val ∧ w.val ≤ 8)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-tables»))
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve) (points : It) (k : Usize)
    (hit : iterInst.Yields points (ops.drop k.val)) (hk : k.val ≤ ss.length)
    (hkops : k.val ≤ ops.length)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-tables»))
    (hout : PairsOK w.val ss ops out k.val) :
    scalars_points_loop borrowInst iterInst scalars points w out k
      ⦃ (r : Option (alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-tables»))) =>
        (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ v, r = some v → PairsOK w.val ss ops v (min ss.length ops.length) ⦄ := by
  have hslen : scalars.val.length = ss.length := hborrow.length_eq
  have hsb : ∀ k (hk : k < scalars.val.length),
      borrowInst.borrow scalars.val[k] ⦃ (s' : scalar.Scalar) => s' = ss[k]! ⦄ := fun k hk => by
    rw [getElem!_pos ss k (hslen ▸ hk)]
    exact (List.forall₂_iff_get.mp hborrow).2 k hk _
  unfold scalars_points_loop
  apply loop.spec_decr_nat (measure := fun (_, _, k') => ss.length - k'.val)
    (inv := fun (it, o, k') => iterInst.Yields it (ops.drop k'.val) ∧ k'.val ≤ ss.length ∧
      k'.val ≤ ops.length ∧ PairsOK w.val ss ops o k'.val)
  · rintro ⟨it, o, k'⟩ ⟨hit', hk', hko, hpo⟩
    unfold scalars_points_loop.body
    by_cases hlt : k'.val < ss.length
    · have hlt' : k' < Slice.len scalars := by scalar_tac
      simp only [hlt', ite_true]
      step as ⟨t, ht⟩
      subst ht
      step with hsb k'.val (by scalar_tac) as ⟨s, hs⟩
      have hs' : s.asNat < 2 ^ 255 := hs ▸ hss _
          (by rw [getElem!_pos ss _ hlt]; exact List.getElem_mem _)
      step with scalar.Scalar.as_radix_2w_spec s w hw hs' as ⟨d, hdv, hdlow, hdall, hdz⟩
      generalize hrest : ops.drop k'.val = rest at hit'
      cases hit' with
      | nil hnext =>
        step with hnext as ⟨o', it1, hq⟩
        subst hq
        dsimp only
        rw [WP.spec_ok]
        have hko' : k'.val = ops.length := by
          have := congrArg List.length hrest
          simp at this; scalar_tac
        refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun v hv => ?_⟩
        · rw [List.take_of_length_le (by scalar_tac)] at h
          obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem h
          obtain ⟨P, hP, -⟩ := hpo.2 j (by scalar_tac)
          rw [getElem!_pos ops j hj, hjn] at hP
          cases hP
        · obtain rfl := Option.some.inj hv
          rwa [show min ss.length ops.length = k'.val by scalar_tac]
      | @cons it it' x xs' hnext hrest' =>
        step with hnext as ⟨o', it1, ho, hit1⟩
        subst ho hit1
        have hk'o : k'.val < ops.length := by
          by_contra hcon
          rw [List.drop_eq_nil_of_le (by scalar_tac)] at hrest
          cases hrest
        have hx : ops[k'.val]! = x := by
          rw [getElem!_pos ops k'.val hk'o]
          have := List.drop_eq_getElem_cons hk'o
          rw [hrest] at this
          exact (List.cons.inj this).1.symm
        have hxs : xs' = ops.drop (k'.val + 1) := by
          have := List.drop_eq_getElem_cons hk'o
          rw [hrest] at this
          exact (List.cons.inj this).2
        rcases x with _ | P
        · dsimp only
          rw [WP.spec_ok]
          refine ⟨⟨fun _ => ?_, fun _ => rfl⟩, fun v hv => by cases hv⟩
          rw [← hx]
          exact List.mem_take_iff_getElem.mpr ⟨k'.val, by simp only [lt_min_iff]; scalar_tac, by
            rw [getElem!_pos ops k'.val hk'o]⟩
        · have hPmem : some P ∈ ops := by
            rw [← hx, getElem!_pos ops k'.val hk'o]; exact List.getElem_mem _
          obtain ⟨hPb, hPon⟩ := hps P hPmem
          step with edwards.«EdwardsPointx86_64-tables».as_projective_niels_spec_point P hPb hPon
            as ⟨pnp, hpon, hpp, hpb⟩
          step with alloc.vec.Vec.push_spec o (d, pnp) (by
            have := hpo.1; have := alloc.vec.Vec.len_ineq o; scalar_tac) as ⟨o1, ho1⟩
          step as ⟨k1, hk1⟩
          have hk1v : k1.val = k'.val + 1 := by scalar_tac
          refine ⟨by rw [hk1v, ← hxs]; exact hrest', by scalar_tac, by scalar_tac,
            ⟨by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hpo.1, hk1v], fun j hj => ?_⟩,
            by scalar_tac⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp (hk1v ▸ hj) with hj' | rfl
          · have hjo : j < o.length := hpo.1 ▸ hj'
            rw [show o1.val[j]! = o1[j]! from rfl,
              alloc.vec.Vec.getElem!_of_val_eq_append_of_lt ho1 hjo]
            exact hpo.2 j hj'
          · have := alloc.vec.Vec.getElem!_of_val_eq_append_length ho1
            rw [hpo.1] at this
            rw [show o1.val[k'.val]! = o1[k'.val]! from rfl, this]
            exact ⟨P, hx, hpon, hpb, hpp, by rw [hdv, hs], hdall, hdz⟩
    · have hge : ¬ k' < Slice.len scalars := by scalar_tac
      simp only [hge, ite_false, WP.spec_ok]
      have hks : k'.val = ss.length := by scalar_tac
      refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun v hv => ?_⟩
      · obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem h
        simp only [List.length_take] at hj
        obtain ⟨P, hP, -⟩ := hpo.2 j (by scalar_tac)
        rw [getElem!_pos ops j (by scalar_tac), ← List.getElem_take (j := ss.length)] at hP
        · rw [hjn] at hP; cases hP
        · rw [List.length_take]; exact hj
      · obtain rfl := Option.some.inj hv
        rwa [show min ss.length ops.length = k'.val by scalar_tac]
  · exact ⟨hit, hk, hkops, hout⟩

end «VartimeMultiscalarMulPippengerEdwardsPointx86_64-tables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

open «VartimeMultiscalarMulPippengerEdwardsPointx86_64-tables» in
/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^52`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«x86_64-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (r = none ↔ none ∈ ops.take ss.length)
          ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold optional_multiscalar_mul.collect
    optional_multiscalar_mul.collect_loop
  apply spec_bind (collect.collectLoop_spec _ it xs hit (alloc.vec.Vec.new _) (by simpa using hxs))
  intro vs hvs
  replace hvs : vs.val = xs := by rw [hvs]; rfl
  apply spec_bind (Pₘ := fun (w : Usize) => 6 ≤ w.val ∧ w.val ≤ 8)
  · split_ifs <;> rw [WP.spec_ok] <;> decide
  intro w hw
  have hw256 : 2 ^ w.val ≤ 256 := Nat.pow_le_pow_right (by norm_num) hw.2
  step with Usize.ShiftLeft_spec 1#usize w (by
      rcases System.Platform.numBits_eq with h | h <;> simp only [h] <;> scalar_tac)
    as ⟨md, hmd, hmdbv⟩
  have hmd' : md.val = 2 ^ w.val := by
    rw [hmd, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  step with scalar.Scalar.to_radix_2w_size_hint_spec w ⟨by scalar_tac, hw.2⟩ as
      ⟨dc, hdc4, hdc5, hdc6, hdc7, hdc8⟩
  step as ⟨bc, hbc⟩
  have hbc' : 2 * bc.val = 2 ^ w.val := by
    rw [hbc, hmd']
    exact Nat.mul_div_cancel' (dvd_pow_self 2 (by scalar_tac))
  have hbc8 : bc.val ≤ 128 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hw.2; scalar_tac
  have hbc1 : 1 ≤ bc.val := by
    have := Nat.one_le_two_pow (n := w.val); scalar_tac
  have hdcw : dc.val ≤ 64 ∧ ∀ i, dc.val ≤ i → 256 < i * w.val := by
    rcases (show w.val = 6 ∨ w.val = 7 ∨ w.val = 8 by scalar_tac) with h | h | h
    · rw [hdc6 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
    · rw [hdc7 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
    · rw [hdc8 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
  have hdc0 : dc.val ≠ 0 := by
    rcases (show w.val = 6 ∨ w.val = 7 ∨ w.val = 8 by scalar_tac) with h | h | h
    · rw [hdc6 h]; decide
    · rw [hdc7 h]; decide
    · rw [hdc8 h]; decide
  step with hpoints' as ⟨it1, hit1⟩
  step with optional_multiscalar_mul.scalars_points_loop_spec
    _ _ _ ss (by rw [show (alloc.vec.Vec.deref vs).val = vs.val from Slice.from_val _ _, hvs]; exact
        hborrow_scalars) hss w
    ⟨by scalar_tac, hw.2⟩ ops hps it1 0#usize (by simpa using hit1) (Nat.zero_le _) (Nat.zero_le _)
    (alloc.vec.Vec.new _) ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    as ⟨o, hnone, hsome⟩
  rcases o with _ | sp
  · dsimp only
    rw [WP.spec_ok]
    exact ⟨by simpa using hnone, fun R hR => by cases hR⟩
  · have hnn : none ∉ ops.take ss.length := fun h => by cases hnone.mpr h
    obtain ⟨hsplen, hsp⟩ := hsome sp rfl
    let P : ℕ → curve25519.edwards.Point := fun k => ((ops[k]!).getD default).toPoint
    have hsp' : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 54 ∧
        (sp.val[k]!).2.toPoint = P k := fun k hk => by
      obtain ⟨Q, hQ, hon, hb, hp, -⟩ := hsp k (hsplen ▸ hk)
      exact ⟨hon, hb, by rw [hp]; change Q.toPoint = ((ops[k]!).getD default).toPoint; rw [hQ]; rfl⟩
    have hdig : ∀ k < sp.length, ∀ e < 64, -(bc.val : ℤ) ≤ (sp.val[k]!).1[e]!.val ∧
        (sp.val[k]!).1[e]!.val ≤ (bc.val : ℤ) := fun k hk e he => by
      obtain ⟨Q, -, -, -, -, -, hb, -⟩ := hsp k (hsplen ▸ hk)
      have := hb e he
      have hbz : (2 : ℤ) ^ w.val = 2 * bc.val := by exact_mod_cast hbc'.symm
      rw [hbz] at this
      constructor <;> linarith [this.1, this.2]
    step with optional_multiscalar_mul_loop0_spec bc (alloc.vec.Vec.new _) 0#usize hbc8
      (Nat.zero_le _) rfl (fun j hj => absurd hj (Nat.not_lt_zero j)) as ⟨b, hb⟩
    step with optional_multiscalar_mul_loop1_spec w bc sp b none dc P dc.val
      ⟨by scalar_tac, hw.2⟩ hbc1 hbc8 hdcw.1 hsp' hdig hb (le_refl _) ⟨fun _ => rfl, fun _ => rfl⟩
      (fun T hT => by cases hT) as ⟨t, htn, hts⟩
    rcases t with _ | T
    · exact absurd (htn.mp rfl) hdc0
    obtain ⟨hTon, hTb, hT⟩ := hts T rfl
    step with core.option.Option.expect.spec as ⟨R, hR⟩
    obtain rfl : T = R := Option.some.inj hR
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : T = R' := Option.some.inj hR'
    refine ⟨hTon, ?_, hTb⟩
    unfold column at hT
    rw [hT, sum_zipWith_filterMap _ _ _ hnn, ← hsplen, sum_columns]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    obtain ⟨Q, hQ, -, -, -, hval, -, hz⟩ := hsp k (hsplen ▸ hk')
    rw [sum_digits _ _ _ hdcw.1 fun j hj hj' => hz j hj (hdcw.2 j hj'), hval, natCast_zsmul]

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

end

section
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
    (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
    (sub_spec_point)

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

/-- The buckets of `optional_multiscalar_mul`: `n` points on the curve within the limb bounds. -/
private def BucketsOK (v : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables») (n : ℕ) : Prop :=
  v.length = n ∧ ∀ j < n, v.val[j]!.OnCurve ∧ v.val[j]!.LimbsLt 26

open edwards.EdwardsPoint.«i686-tables».Insts in
/-- The first loop: `buckets_count` identities. -/
@[local step]
private theorem optional_multiscalar_mul_loop0_spec (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables») (b : Usize) (hbc : bc.val ≤ 128)
    (hb : b.val ≤ bc.val) (hlen : buckets.length = b.val)
    (hbk : ∀ j < b.val, buckets.val[j]!.OnCurve ∧ buckets.val[j]!.LimbsLt 26 ∧
      buckets.val[j]!.toPoint = 0) :
    optional_multiscalar_mul_loop0 bc buckets b
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables») => BucketsOK r bc.val ⦄ := by
  unfold optional_multiscalar_mul_loop0
  apply loop.spec_decr_nat (measure := fun (_, b') => bc.val - b'.val)
    (inv := fun (v, b') => b'.val ≤ bc.val ∧ v.length = b'.val ∧
      ∀ j < b'.val, v.val[j]!.OnCurve ∧ v.val[j]!.LimbsLt 26 ∧ v.val[j]!.toPoint = 0)
  · rintro ⟨v, b'⟩ ⟨hb', hl, hv⟩
    unfold optional_multiscalar_mul_loop0.body
    by_cases hlt : b' < bc
    · simp only [hlt, ite_true]
      step with Curve25519_dalekTraitsIdentity.identity_spec_point
        as ⟨e, heon, he, heb⟩
      step as ⟨v1, hv1⟩
      step as ⟨b1, hb1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hv1, hl, hb1], ?_,
        by scalar_tac⟩
      rw [hb1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append
        (P := fun _ x => x.OnCurve ∧ x.LimbsLt 26 ∧ x.toPoint = 0) hv1 (hl ▸ hv) ⟨heon, heb, he⟩
    · simp only [hlt, ite_false, WP.spec_ok]
      have : b'.val = bc.val := by scalar_tac
      exact ⟨this ▸ hl, fun j hj => ⟨(hv j (this ▸ hj)).1, (hv j (this ▸ hj)).2.1⟩⟩
  · exact ⟨hb, hlen, hbk⟩

open edwards.EdwardsPoint.«i686-tables».Insts in
/-- The reset loop: every bucket becomes the identity. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop0_spec (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables») (b : Usize)
    (hok : BucketsOK buckets bc.val) (hb : b.val ≤ bc.val)
    (hz : ∀ j < b.val, buckets.val[j]!.toPoint = 0) :
    optional_multiscalar_mul_loop1_loop0 bc buckets b
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables») =>
        BucketsOK r bc.val ∧ ∀ j < bc.val, r.val[j]!.toPoint = 0 ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop0
  apply loop.spec_decr_nat (measure := fun (_, b') => bc.val - b'.val)
    (inv := fun (v, b') => b'.val ≤ bc.val ∧ BucketsOK v bc.val ∧
      ∀ j < b'.val, v.val[j]!.toPoint = 0)
  · rintro ⟨v, b'⟩ ⟨hb', ⟨hl, hv⟩, hvz⟩
    unfold optional_multiscalar_mul_loop1_loop0.body
    by_cases hlt : b' < bc
    · simp only [hlt, ite_true]
      step with Curve25519_dalekTraitsIdentity.identity_spec_point
        as ⟨e, heon, he, heb⟩
      step as ⟨x, back, hx, hback⟩
      step as ⟨b1, hb1⟩
      have hbl : b'.val < v.val.length := by
        rw [show v.val.length = v.length from rfl, hl]; scalar_tac
      refine ⟨by scalar_tac, ⟨?_, fun j hj => ?_⟩, fun j hj => ?_, by scalar_tac⟩
      · rw [hback, alloc.vec.Vec.set_length, hl]
      · rw [hback, alloc.vec.Vec.set_val_eq]
        rcases eq_or_ne j b'.val with rfl | hne
        · rw [getElem!_set_eq' _ _ _ hbl]; exact ⟨heon, heb⟩
        · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
      · rw [hback, alloc.vec.Vec.set_val_eq]
        rcases eq_or_ne j b'.val with rfl | hne
        · rw [getElem!_set_eq' _ _ _ hbl]; exact he
        · rw [getElem!_set_ne' _ _ _ _ hne]; exact hvz j (by scalar_tac)
    · simp only [hlt, ite_false, WP.spec_ok]
      have : b'.val = bc.val := by scalar_tac
      exact ⟨⟨hl, hv⟩, fun j hj => hvz j (this ▸ hj)⟩
  · exact ⟨hb, hok, hz⟩

open edwards.EdwardsPoint.«i686-tables».Insts in
/-- The running sums: `buckets_sum` ends as `∑_b (b + 1) • bucket_b`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop2_spec
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables») (bc : ℕ)
    (hok : BucketsOK buckets bc) (inter sum : edwards.EdwardsPoint.«i686-tables») (i : Usize)
    (hi : i.val < bc) (hinter : inter.OnCurve ∧ inter.LimbsLt 26 ∧
      inter.toPoint = ∑ b ∈ Finset.Ico i.val bc, buckets.val[b]!.toPoint)
    (hsum : sum.OnCurve ∧ sum.LimbsLt 26 ∧
      sum.toPoint = ∑ b ∈ Finset.Ico i.val bc, (b - i.val + 1) • buckets.val[b]!.toPoint) :
    optional_multiscalar_mul_loop1_loop2 buckets inter sum i
      ⦃ (r : edwards.EdwardsPoint.«i686-tables») => r.OnCurve ∧ r.LimbsLt 26 ∧
        r.toPoint = wsum edwards.EdwardsPoint.«i686-tables».toPoint buckets.val bc ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop2
  apply loop.spec_decr_nat (measure := fun (_, _, i') => i'.val)
    (inv := fun (it, sm, i') => i'.val < bc ∧
      it.OnCurve ∧ it.LimbsLt 26 ∧
        it.toPoint = ∑ b ∈ Finset.Ico i'.val bc, buckets.val[b]!.toPoint ∧
      sm.OnCurve ∧ sm.LimbsLt 26 ∧
        sm.toPoint = ∑ b ∈ Finset.Ico i'.val bc, (b - i'.val + 1) • buckets.val[b]!.toPoint)
  · rintro ⟨it, sm, i'⟩ ⟨hi', hiton, hitb, hitp, hsmon, hsmb, hsmp⟩
    unfold optional_multiscalar_mul_loop1_loop2.body
    by_cases hpos : i' > 0#usize
    · simp only [hpos, ite_true]
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < bc := by scalar_tac
      step as ⟨ep, hep⟩
      rw [← getElem!_pos] at hep
      obtain ⟨hepon, hepb⟩ := hok.2 i1.val hi1b
      rw [← hep] at hepon hepb
      step with «CoreOpsArithAddAssignEdwardsPointi686-tables».add_assign_spec_point
        it ep hitb hepb hiton hepon as ⟨it1, hit1on, hit1, hit1b⟩
      step with «CoreOpsArithAddAssignEdwardsPointi686-tables».add_assign_spec_point
        sm it1 hsmb hit1b hsmon hit1on as ⟨sm1, hsm1on, hsm1, hsm1b⟩
      have hii : i'.val = i1.val + 1 := by scalar_tac
      have hsum1 : ∑ b ∈ Finset.Ico i1.val bc, buckets.val[b]!.toPoint =
          ∑ b ∈ Finset.Ico i'.val bc, buckets.val[b]!.toPoint + ep.toPoint := by
        rw [Finset.sum_eq_sum_Ico_succ_bot hi1b, hii, hep, add_comm]
      refine ⟨hi1b, hit1on, hit1b, by rw [hit1, hitp, hsum1], hsm1on, hsm1b, ?_,
        by rw [hii]; exact Nat.lt_succ_self _⟩
      rw [hsm1, hit1, hsmp, hitp, ← hsum1, hii]
      exact running_sum_step (fun b => buckets.val[b]!.toPoint) i1.val bc hi1b
    · simp only [hpos, ite_false, WP.spec_ok]
      have h0 : i'.val = 0 := by scalar_tac
      refine ⟨hsmon, hsmb, ?_⟩
      rw [hsmp, h0, wsum, Finset.range_eq_Ico]
      exact Finset.sum_congr rfl fun b _ => by rw [Nat.sub_zero]
  · exact ⟨hi, hinter.1, hinter.2.1, hinter.2.2, hsum.1, hsum.2.1, hsum.2.2⟩

open scoped Helpers.IndexStep in
/-- The accumulation loop: point `k` (from `si` on) is added to bucket `d_k[e] - 1`, or subtracted
from bucket `-d_k[e] - 1`; the weighted sum of the buckets grows by `d_k[e] • P_k`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop1_spec
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables») (e si : Usize) (bc : ℕ)
    (P : ℕ → curve25519.edwards.Point) (he : e.val < 64) (hbc : bc ≤ 128)
    (hsp : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 27 ∧
      (sp.val[k]!).2.toPoint = P k)
    (hdig : ∀ k < sp.length, -(bc : ℤ) ≤ (sp.val[k]!).1[e.val]!.val ∧
      (sp.val[k]!).1[e.val]!.val ≤ bc)
    (hok : BucketsOK buckets bc) (hsi : si.val ≤ sp.length) :
    optional_multiscalar_mul_loop1_loop1 sp buckets e si
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables») => BucketsOK r bc ∧
        wsum edwards.EdwardsPoint.«i686-tables».toPoint r.val bc =
          wsum edwards.EdwardsPoint.«i686-tables».toPoint buckets.val bc +
            ∑ k ∈ Finset.Ico si.val sp.length, (sp.val[k]!).1[e.val]!.val • P k ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop1
  apply loop.spec_decr_nat (measure := fun (_, si') => sp.length - si'.val)
    (inv := fun (v, si') => si.val ≤ si'.val ∧ si'.val ≤ sp.length ∧ BucketsOK v bc ∧
      wsum edwards.EdwardsPoint.«i686-tables».toPoint v.val bc =
        wsum edwards.EdwardsPoint.«i686-tables».toPoint buckets.val bc +
          ∑ k ∈ Finset.Ico si.val si'.val, (sp.val[k]!).1[e.val]!.val • P k)
  · rintro ⟨v, si'⟩ ⟨hss, hsl, ⟨hvl, hv⟩, hw⟩
    unfold optional_multiscalar_mul_loop1_loop1.body
    by_cases hlt : si'.val < sp.length
    · have hlt' : si' < alloc.vec.Vec.len sp := by scalar_tac
      simp only [hlt', ite_true]
      step as ⟨digits, pt, hdp⟩
      rw [← getElem!_pos] at hdp
      obtain ⟨hpton, hptb, hptp⟩ := hsp si'.val hlt
      obtain ⟨hdl, hdu⟩ := hdig si'.val hlt
      rw [← hdp] at hpton hptb hptp hdl hdu
      simp only at hpton hptb hptp hdl hdu
      step as ⟨d8, hd8⟩
      step with IScalar.cast_inBounds_spec as ⟨d, hd⟩
      rw [show lift (core.cmp.impls.OrdI16.cmp d 0#i16) = ok (compare d.val 0) from rfl, bind_ok]
      apply spec_bind (Pₘ := fun v1 => BucketsOK v1 bc ∧
        wsum edwards.EdwardsPoint.«i686-tables».toPoint v1.val bc =
          wsum edwards.EdwardsPoint.«i686-tables».toPoint v.val bc + d.val • P si'.val)
      · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
        · rw [(compare_lt_iff_lt).mpr hneg]
          simp only
          step as ⟨i2, hi2⟩
          step as ⟨i3, hi3⟩
          step with IScalar.hcast_inBounds_spec as ⟨b, hb⟩
          have hbv : b.val + 1 = (-d.val).toNat := by scalar_tac
          have hbl : b.val < bc := by scalar_tac
          step as ⟨ep, hep⟩
          rw [← getElem!_pos] at hep
          obtain ⟨hepon, hepb⟩ := hv b.val hbl
          rw [← hep] at hepon hepb
          step with sub_spec_point ep pt hepb hptb hepon hpton as ⟨c, hcon, hc, hcb⟩
          step with «CompletedPointi686-tables».as_extended_spec_point as
              ⟨ep1, hep1on, hep1, hep1b⟩
          step as ⟨y, back, hy, hback⟩
          have hbl' : b.val < v.val.length := by
            rw [show v.val.length = v.length from rfl, hvl]; exact hbl
          refine ⟨⟨by rw [hback, alloc.vec.Vec.set_length, hvl], fun j hj => ?_⟩, ?_⟩
          · rw [hback, alloc.vec.Vec.set_val_eq]
            rcases eq_or_ne j b.val with rfl | hne
            · rw [getElem!_set_eq' _ _ _ hbl']; exact ⟨hep1on, hep1b⟩
            · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
          · rw [hback, alloc.vec.Vec.set_val_eq, wsum_set _ _ _ _ hbl hvl, hep1, hc, ← hep, hptp]
            congr 1
            rw [sub_sub_cancel_left, smul_neg, ← natCast_zsmul, ← neg_zsmul]
            congr 1
            push_cast
            omega
        · rw [(compare_eq_iff_eq).mpr hzero]
          simp only [WP.spec_ok]
          rw [hzero, zero_smul, add_zero]
          exact ⟨⟨hvl, hv⟩, rfl⟩
        · rw [(compare_gt_iff_gt).mpr hpos]
          simp only
          step as ⟨i2, hi2⟩
          step with IScalar.hcast_inBounds_spec as ⟨b, hb⟩
          have hbv : b.val + 1 = d.val.toNat := by scalar_tac
          have hbl : b.val < bc := by scalar_tac
          step as ⟨ep, hep⟩
          rw [← getElem!_pos] at hep
          obtain ⟨hepon, hepb⟩ := hv b.val hbl
          rw [← hep] at hepon hepb
          step with add_spec_point ep pt hepb hptb hepon hpton as ⟨c, hcon, hc, hcb⟩
          step with «CompletedPointi686-tables».as_extended_spec_point as
              ⟨ep1, hep1on, hep1, hep1b⟩
          step as ⟨y, back, hy, hback⟩
          have hbl' : b.val < v.val.length := by
            rw [show v.val.length = v.length from rfl, hvl]; exact hbl
          refine ⟨⟨by rw [hback, alloc.vec.Vec.set_length, hvl], fun j hj => ?_⟩, ?_⟩
          · rw [hback, alloc.vec.Vec.set_val_eq]
            rcases eq_or_ne j b.val with rfl | hne
            · rw [getElem!_set_eq' _ _ _ hbl']; exact ⟨hep1on, hep1b⟩
            · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
          · rw [hback, alloc.vec.Vec.set_val_eq, wsum_set _ _ _ _ hbl hvl, hep1, hc, ← hep, hptp]
            congr 1
            rw [add_sub_cancel_left, ← natCast_zsmul]
            congr 1
            push_cast
            omega
      · rintro v1 ⟨hok1, hw1⟩
        step as ⟨si1, hsi1⟩
        refine ⟨by scalar_tac, by scalar_tac, hok1, ?_, by scalar_tac⟩
        rw [hw1, hw, show si1.val = si'.val + 1 by scalar_tac, Finset.sum_Ico_succ_top hss,
          add_assoc, hd, hd8, ← hdp]
    · have hge : ¬ si' < alloc.vec.Vec.len sp := by scalar_tac
      simp only [hge, ite_false, WP.spec_ok]
      have : si'.val = sp.length := by scalar_tac
      exact ⟨⟨hvl, hv⟩, this ▸ hw⟩
  · exact ⟨le_refl _, hsi, hok, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The column of digit position `e`: `∑_k d_k[e] • P_k`. -/
private noncomputable def column
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-tables»))
    (P : ℕ → curve25519.edwards.Point) (e : ℕ) : curve25519.edwards.Point :=
  ∑ k ∈ Finset.range sp.length, ((sp.val[k]!).1[e]!.val : ℤ) • P k

open edwards.EdwardsPoint.«i686-tables».Insts in
open scoped Helpers.IndexStep in
/-- The outer loop over the digit positions, from the top: the total is
`∑_{j} 2^(w j) • column (di + j)` over the positions processed. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_spec (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables»)
    (total : Option edwards.EdwardsPoint.«i686-tables») (di : Usize)
    (P : ℕ → curve25519.edwards.Point) (dc : ℕ) (hw : 0 < w.val ∧ w.val ≤ 8)
    (hbc1 : 1 ≤ bc.val) (hbc : bc.val ≤ 128) (hdc : dc ≤ 64)
    (hsp : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 27 ∧
      (sp.val[k]!).2.toPoint = P k)
    (hdig : ∀ k < sp.length, ∀ e < 64, -(bc.val : ℤ) ≤ (sp.val[k]!).1[e]!.val ∧
      (sp.val[k]!).1[e]!.val ≤ (bc.val : ℤ))
    (hok : BucketsOK buckets bc.val) (hdi : di.val ≤ dc)
    (hnone : total = none ↔ di.val = dc)
    (hsome : ∀ T, total = some T → T.OnCurve ∧ T.LimbsLt 26 ∧
      T.toPoint = ∑ j ∈ Finset.range (dc - di.val), 2 ^ (w.val * j) • column sp P (di.val + j)) :
    optional_multiscalar_mul_loop1 w bc sp buckets total di
      ⦃ (r : Option edwards.EdwardsPoint.«i686-tables») => (r = none ↔ dc = 0) ∧
        ∀ T, r = some T → T.OnCurve ∧ T.LimbsLt 26 ∧
          T.toPoint = ∑ j ∈ Finset.range dc, 2 ^ (w.val * j) • column sp P j ⦄ := by
  unfold optional_multiscalar_mul_loop1
  apply loop.spec_decr_nat (measure := fun (_, _, d) => d.val)
    (inv := fun (v, t, d) => BucketsOK v bc.val ∧ d.val ≤ dc ∧ (t = none ↔ d.val = dc) ∧
      ∀ T, t = some T → T.OnCurve ∧ T.LimbsLt 26 ∧
        T.toPoint = ∑ j ∈ Finset.range (dc - d.val), 2 ^ (w.val * j) • column sp P (d.val + j))
  · rintro ⟨v, t, d⟩ ⟨hv, hd, htn, hts⟩
    unfold optional_multiscalar_mul_loop1.body
    by_cases hpos : d > 0#usize
    · simp only [hpos, ite_true]
      step as ⟨d1, hd1⟩
      have hdpos : 0 < d.val := hpos
      have hdd : d.val = d1.val + 1 := by rw [hd1]; exact (Nat.sub_add_cancel hdpos).symm
      have hd1lt : d1.val < dc := by
        rw [hd1]; exact lt_of_lt_of_le (Nat.sub_lt hdpos Nat.one_pos) hd
      have hd164 : d1.val < 64 := lt_of_lt_of_le hd1lt hdc
      step with optional_multiscalar_mul_loop1_loop0_spec bc v 0#usize hv (Nat.zero_le _)
        (fun j hj => absurd hj (Nat.not_lt_zero j)) as ⟨v1, hv1, hv1z⟩
      step with optional_multiscalar_mul_loop1_loop1_spec sp v1 d1 0#usize bc.val P
        hd164 hbc hsp (fun k hk => hdig k hk d1.val hd164) hv1
        (Nat.zero_le _) as ⟨v2, hv2, hw2⟩
      step as ⟨i, hi⟩
      have hib : i.val < bc.val := by
        rw [hi]; exact Nat.sub_lt (lt_of_lt_of_le Nat.one_pos hbc1) Nat.one_pos
      have hil : i.val < v2.val.length := by
        rw [show v2.val.length = v2.length from rfl, hv2.1]; exact hib
      step as ⟨inter, hinter⟩
      rw [← getElem!_pos] at hinter
      step as ⟨sm, hsm⟩
      rw [← getElem!_pos] at hsm
      have hIco : Finset.Ico i.val bc.val = {i.val} := by
        rw [show bc.val = i.val + 1 by rw [hi]; exact (Nat.sub_add_cancel hbc1).symm,
          Nat.Ico_succ_singleton]
      obtain ⟨hion, hib'⟩ := hv2.2 i.val hib
      step with optional_multiscalar_mul_loop1_loop2_spec v2 bc.val hv2 inter sm i hib
        ⟨hinter ▸ hion, hinter ▸ hib', by rw [hIco, Finset.sum_singleton, hinter]⟩
        ⟨hsm ▸ hion, hsm ▸ hib', by
          rw [hIco, Finset.sum_singleton, hsm, Nat.sub_self, zero_add, one_smul]⟩
        as ⟨c, hcon, hcb, hc⟩
      have hzero : wsum edwards.EdwardsPoint.«i686-tables».toPoint v1.val bc.val = 0 :=
        Finset.sum_eq_zero fun b hb => by rw [hv1z b (Finset.mem_range.mp hb), smul_zero]
      have hcol : c.toPoint = column sp P d1.val := by
        rw [hc, hw2, hzero, zero_add, ← Finset.range_eq_Ico]
        rfl
      rcases t with _ | T
      · have hdc' : d.val = dc := htn.mp rfl
        dsimp only
        rw [WP.spec_ok]
        refine ⟨hv2, Nat.le_of_lt hd1lt,
          ⟨fun h => (by cases h), fun h => absurd h (Nat.ne_of_lt hd1lt)⟩,
          fun T' hT' => ?_, by rw [hdd]; exact Nat.lt_succ_self _⟩
        obtain rfl : c = T' := Option.some.inj hT'
        refine ⟨hcon, hcb, ?_⟩
        rw [hcol, show dc - d1.val = 1 by rw [← hdc', hdd, Nat.add_sub_cancel_left],
          Finset.sum_range_one, mul_zero, pow_zero, one_smul, add_zero]
      · obtain ⟨hTon, hTb, hT⟩ := hts T rfl
        have hdc' : d.val ≠ dc := fun h => by cases htn.mpr h
        dsimp only
        step as ⟨k, hk⟩
        have hkw : k.val = w.val := by
          rw [hk, UScalar.cast_val_eq]
          exact Nat.mod_eq_of_lt (lt_of_le_of_lt hw.2 (by decide))
        step with edwards.«EdwardsPointi686-tables».mul_by_pow_2_spec T k hTb hTon
            (by rw [hkw]; exact hw.1)
          as ⟨T2, hT2on, hT2, hT2b⟩
        step with «CoreOpsArithAddEdwardsPointi686-tablesEdwardsPointi686-tables».add_spec_point
          T2 c hT2b hcb hT2on hcon as ⟨T3, hT3on, hT3, hT3b⟩
        refine ⟨hv2, Nat.le_of_lt hd1lt,
          ⟨fun h => (by cases h), fun h => absurd h (Nat.ne_of_lt hd1lt)⟩,
          fun T' hT' => ?_, by rw [hdd]; exact Nat.lt_succ_self _⟩
        obtain rfl : T3 = T' := Option.some.inj hT'
        refine ⟨hT3on, hT3b, ?_⟩
        have hdcd : dc - d1.val = (dc - d.val) + 1 := by
          rw [hdd, Nat.sub_add_eq]
          exact (Nat.sub_add_cancel (Nat.sub_pos_of_lt hd1lt)).symm
        rw [hT3, hT2, hT, hcol, hkw, hdcd, Finset.sum_range_succ', Finset.smul_sum]
        rw [mul_zero, pow_zero, one_smul, add_zero]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, ← pow_add, hdd, show w.val + w.val * j = w.val * (j + 1) by ring,
          show d1.val + 1 + j = d1.val + (j + 1) by ring]
    · simp only [hpos, ite_false, WP.spec_ok]
      have h0 : d.val = 0 := by scalar_tac
      refine ⟨by rw [htn, h0]; exact eq_comm, fun T hT => ?_⟩
      obtain ⟨hTon, hTb, hT'⟩ := hts T hT
      refine ⟨hTon, hTb, ?_⟩
      rw [hT', h0, Nat.sub_zero]
      exact Finset.sum_congr rfl fun j _ => by rw [zero_add]
  · exact ⟨hok, hdi, hnone, hsome⟩

/-- The pairs collected by `scalars_points`, up to `m`: digits of `ss[j]` and the projective Niels
form of the point `ops[j] = some P`. -/
private def PairsOK (w : ℕ) (ss : List scalar.Scalar)
    (ops : List (Option edwards.EdwardsPoint.«i686-tables»))
    (v : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-tables»)) (m : ℕ) : Prop
        :=
  v.length = m ∧ ∀ j < m, ∃ P, ops[j]! = some P ∧
    (v.val[j]!).2.OnCurve ∧ (v.val[j]!).2.LimbsLt 27 ∧ (v.val[j]!).2.toPoint = P.toPoint ∧
    (v.val[j]!).1.asInt w = ss[j]!.asNat ∧
    (∀ i < 64, -2 ^ w ≤ 2 * (v.val[j]!).1[i]!.val ∧ 2 * (v.val[j]!).1[i]!.val ≤ 2 ^ w) ∧
    ∀ i < 64, 256 < i * w → (v.val[j]!).1[i]!.val = 0

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

namespace «VartimeMultiscalarMulPippengerEdwardsPointi686-tables».optional_multiscalar_mul

open Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

/-- The loop of `scalars_points`: the digits of each scalar with the next point, until the
scalars or the points run out; `none` at the first `none` point. -/
@[local step]
private theorem scalars_points_loop_spec {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It (Option edwards.EdwardsPoint.«i686-tables»))
    (scalars : Slice S) (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) scalars.val ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (w : Usize) (hw : 4 ≤ w.val ∧ w.val ≤ 8)
    (ops : List (Option edwards.EdwardsPoint.«i686-tables»))
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve) (points : It) (k : Usize)
    (hit : iterInst.Yields points (ops.drop k.val)) (hk : k.val ≤ ss.length)
    (hkops : k.val ≤ ops.length)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-tables»))
    (hout : PairsOK w.val ss ops out k.val) :
    scalars_points_loop borrowInst iterInst scalars points w out k
      ⦃ (r : Option (alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-tables»))) =>
        (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ v, r = some v → PairsOK w.val ss ops v (min ss.length ops.length) ⦄ := by
  have hslen : scalars.val.length = ss.length := hborrow.length_eq
  have hsb : ∀ k (hk : k < scalars.val.length),
      borrowInst.borrow scalars.val[k] ⦃ (s' : scalar.Scalar) => s' = ss[k]! ⦄ := fun k hk => by
    rw [getElem!_pos ss k (hslen ▸ hk)]
    exact (List.forall₂_iff_get.mp hborrow).2 k hk _
  unfold scalars_points_loop
  apply loop.spec_decr_nat (measure := fun (_, _, k') => ss.length - k'.val)
    (inv := fun (it, o, k') => iterInst.Yields it (ops.drop k'.val) ∧ k'.val ≤ ss.length ∧
      k'.val ≤ ops.length ∧ PairsOK w.val ss ops o k'.val)
  · rintro ⟨it, o, k'⟩ ⟨hit', hk', hko, hpo⟩
    unfold scalars_points_loop.body
    by_cases hlt : k'.val < ss.length
    · have hlt' : k' < Slice.len scalars := by scalar_tac
      simp only [hlt', ite_true]
      step as ⟨t, ht⟩
      subst ht
      step with hsb k'.val (by scalar_tac) as ⟨s, hs⟩
      have hs' : s.asNat < 2 ^ 255 := hs ▸ hss _
          (by rw [getElem!_pos ss _ hlt]; exact List.getElem_mem _)
      step with scalar.Scalar.as_radix_2w_spec s w hw hs' as ⟨d, hdv, hdlow, hdall, hdz⟩
      generalize hrest : ops.drop k'.val = rest at hit'
      cases hit' with
      | nil hnext =>
        step with hnext as ⟨o', it1, hq⟩
        subst hq
        dsimp only
        rw [WP.spec_ok]
        have hko' : k'.val = ops.length := by
          have := congrArg List.length hrest
          simp at this; scalar_tac
        refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun v hv => ?_⟩
        · rw [List.take_of_length_le (by scalar_tac)] at h
          obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem h
          obtain ⟨P, hP, -⟩ := hpo.2 j (by scalar_tac)
          rw [getElem!_pos ops j hj, hjn] at hP
          cases hP
        · obtain rfl := Option.some.inj hv
          rwa [show min ss.length ops.length = k'.val by scalar_tac]
      | @cons it it' x xs' hnext hrest' =>
        step with hnext as ⟨o', it1, ho, hit1⟩
        subst ho hit1
        have hk'o : k'.val < ops.length := by
          by_contra hcon
          rw [List.drop_eq_nil_of_le (by scalar_tac)] at hrest
          cases hrest
        have hx : ops[k'.val]! = x := by
          rw [getElem!_pos ops k'.val hk'o]
          have := List.drop_eq_getElem_cons hk'o
          rw [hrest] at this
          exact (List.cons.inj this).1.symm
        have hxs : xs' = ops.drop (k'.val + 1) := by
          have := List.drop_eq_getElem_cons hk'o
          rw [hrest] at this
          exact (List.cons.inj this).2
        rcases x with _ | P
        · dsimp only
          rw [WP.spec_ok]
          refine ⟨⟨fun _ => ?_, fun _ => rfl⟩, fun v hv => by cases hv⟩
          rw [← hx]
          exact List.mem_take_iff_getElem.mpr ⟨k'.val, by simp only [lt_min_iff]; scalar_tac, by
            rw [getElem!_pos ops k'.val hk'o]⟩
        · have hPmem : some P ∈ ops := by
            rw [← hx, getElem!_pos ops k'.val hk'o]; exact List.getElem_mem _
          obtain ⟨hPb, hPon⟩ := hps P hPmem
          step with edwards.«EdwardsPointi686-tables».as_projective_niels_spec_point P hPb hPon
            as ⟨pnp, hpon, hpp, hpb⟩
          step with alloc.vec.Vec.push_spec o (d, pnp) (by
            have := hpo.1; have := alloc.vec.Vec.len_ineq o; scalar_tac) as ⟨o1, ho1⟩
          step as ⟨k1, hk1⟩
          have hk1v : k1.val = k'.val + 1 := by scalar_tac
          refine ⟨by rw [hk1v, ← hxs]; exact hrest', by scalar_tac, by scalar_tac,
            ⟨by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hpo.1, hk1v], fun j hj => ?_⟩,
            by scalar_tac⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp (hk1v ▸ hj) with hj' | rfl
          · have hjo : j < o.length := hpo.1 ▸ hj'
            rw [show o1.val[j]! = o1[j]! from rfl,
              alloc.vec.Vec.getElem!_of_val_eq_append_of_lt ho1 hjo]
            exact hpo.2 j hj'
          · have := alloc.vec.Vec.getElem!_of_val_eq_append_length ho1
            rw [hpo.1] at this
            rw [show o1.val[k'.val]! = o1[k'.val]! from rfl, this]
            exact ⟨P, hx, hpon, hpb, hpp, by rw [hdv, hs], hdall, hdz⟩
    · have hge : ¬ k' < Slice.len scalars := by scalar_tac
      simp only [hge, ite_false, WP.spec_ok]
      have hks : k'.val = ss.length := by scalar_tac
      refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun v hv => ?_⟩
      · obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem h
        simp only [List.length_take] at hj
        obtain ⟨P, hP, -⟩ := hpo.2 j (by scalar_tac)
        rw [getElem!_pos ops j (by scalar_tac), ← List.getElem_take (j := ss.length)] at hP
        · rw [hjn] at hP; cases hP
        · rw [List.length_take]; exact hj
      · obtain rfl := Option.some.inj hv
        rwa [show min ss.length ops.length = k'.val by scalar_tac]
  · exact ⟨hit, hk, hkops, hout⟩

end «VartimeMultiscalarMulPippengerEdwardsPointi686-tables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

open «VartimeMultiscalarMulPippengerEdwardsPointi686-tables» in
/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^26`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«i686-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«i686-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-tables») => (r = none ↔ none ∈ ops.take ss.length)
          ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold optional_multiscalar_mul.collect
    optional_multiscalar_mul.collect_loop
  apply spec_bind (collect.collectLoop_spec _ it xs hit (alloc.vec.Vec.new _) (by simpa using hxs))
  intro vs hvs
  replace hvs : vs.val = xs := by rw [hvs]; rfl
  apply spec_bind (Pₘ := fun (w : Usize) => 6 ≤ w.val ∧ w.val ≤ 8)
  · split_ifs <;> rw [WP.spec_ok] <;> decide
  intro w hw
  have hw256 : 2 ^ w.val ≤ 256 := Nat.pow_le_pow_right (by norm_num) hw.2
  step with Usize.ShiftLeft_spec 1#usize w (by
      rcases System.Platform.numBits_eq with h | h <;> simp only [h] <;> scalar_tac)
    as ⟨md, hmd, hmdbv⟩
  have hmd' : md.val = 2 ^ w.val := by
    rw [hmd, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  step with scalar.Scalar.to_radix_2w_size_hint_spec w ⟨by scalar_tac, hw.2⟩ as
      ⟨dc, hdc4, hdc5, hdc6, hdc7, hdc8⟩
  step as ⟨bc, hbc⟩
  have hbc' : 2 * bc.val = 2 ^ w.val := by
    rw [hbc, hmd']
    exact Nat.mul_div_cancel' (dvd_pow_self 2 (by scalar_tac))
  have hbc8 : bc.val ≤ 128 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hw.2; scalar_tac
  have hbc1 : 1 ≤ bc.val := by
    have := Nat.one_le_two_pow (n := w.val); scalar_tac
  have hdcw : dc.val ≤ 64 ∧ ∀ i, dc.val ≤ i → 256 < i * w.val := by
    rcases (show w.val = 6 ∨ w.val = 7 ∨ w.val = 8 by scalar_tac) with h | h | h
    · rw [hdc6 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
    · rw [hdc7 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
    · rw [hdc8 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
  have hdc0 : dc.val ≠ 0 := by
    rcases (show w.val = 6 ∨ w.val = 7 ∨ w.val = 8 by scalar_tac) with h | h | h
    · rw [hdc6 h]; decide
    · rw [hdc7 h]; decide
    · rw [hdc8 h]; decide
  step with hpoints' as ⟨it1, hit1⟩
  step with optional_multiscalar_mul.scalars_points_loop_spec
    _ _ _ ss (by rw [show (alloc.vec.Vec.deref vs).val = vs.val from Slice.from_val _ _, hvs]; exact
        hborrow_scalars) hss w
    ⟨by scalar_tac, hw.2⟩ ops hps it1 0#usize (by simpa using hit1) (Nat.zero_le _) (Nat.zero_le _)
    (alloc.vec.Vec.new _) ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    as ⟨o, hnone, hsome⟩
  rcases o with _ | sp
  · dsimp only
    rw [WP.spec_ok]
    exact ⟨by simpa using hnone, fun R hR => by cases hR⟩
  · have hnn : none ∉ ops.take ss.length := fun h => by cases hnone.mpr h
    obtain ⟨hsplen, hsp⟩ := hsome sp rfl
    let P : ℕ → curve25519.edwards.Point := fun k => ((ops[k]!).getD default).toPoint
    have hsp' : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 27 ∧
        (sp.val[k]!).2.toPoint = P k := fun k hk => by
      obtain ⟨Q, hQ, hon, hb, hp, -⟩ := hsp k (hsplen ▸ hk)
      exact ⟨hon, hb, by rw [hp]; change Q.toPoint = ((ops[k]!).getD default).toPoint; rw [hQ]; rfl⟩
    have hdig : ∀ k < sp.length, ∀ e < 64, -(bc.val : ℤ) ≤ (sp.val[k]!).1[e]!.val ∧
        (sp.val[k]!).1[e]!.val ≤ (bc.val : ℤ) := fun k hk e he => by
      obtain ⟨Q, -, -, -, -, -, hb, -⟩ := hsp k (hsplen ▸ hk)
      have := hb e he
      have hbz : (2 : ℤ) ^ w.val = 2 * bc.val := by exact_mod_cast hbc'.symm
      rw [hbz] at this
      constructor <;> linarith [this.1, this.2]
    step with optional_multiscalar_mul_loop0_spec bc (alloc.vec.Vec.new _) 0#usize hbc8
      (Nat.zero_le _) rfl (fun j hj => absurd hj (Nat.not_lt_zero j)) as ⟨b, hb⟩
    step with optional_multiscalar_mul_loop1_spec w bc sp b none dc P dc.val
      ⟨by scalar_tac, hw.2⟩ hbc1 hbc8 hdcw.1 hsp' hdig hb (le_refl _) ⟨fun _ => rfl, fun _ => rfl⟩
      (fun T hT => by cases hT) as ⟨t, htn, hts⟩
    rcases t with _ | T
    · exact absurd (htn.mp rfl) hdc0
    obtain ⟨hTon, hTb, hT⟩ := hts T rfl
    step with core.option.Option.expect.spec as ⟨R, hR⟩
    obtain rfl : T = R := Option.some.inj hR
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : T = R' := Option.some.inj hR'
    refine ⟨hTon, ?_, hTb⟩
    unfold column at hT
    rw [hT, sum_zipWith_filterMap _ _ _ hnn, ← hsplen, sum_columns]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    obtain ⟨Q, hQ, -, -, -, hval, -, hz⟩ := hsp k (hsplen ▸ hk')
    rw [sum_digits _ _ _ hdcw.1 fun j hj hj' => hz j hj (hdcw.2 j hj'), hval, natCast_zsmul]

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    (sub_spec_point)

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

/-- The buckets of `optional_multiscalar_mul`: `n` points on the curve within the limb bounds. -/
private def BucketsOK (v : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables») (n : ℕ) : Prop :=
  v.length = n ∧ ∀ j < n, v.val[j]!.OnCurve ∧ v.val[j]!.LimbsLt 52

open edwards.EdwardsPoint.«x86_64-no-tables».Insts in
/-- The first loop: `buckets_count` identities. -/
@[local step]
private theorem optional_multiscalar_mul_loop0_spec (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables») (b : Usize)
        (hbc : bc.val ≤ 128)
    (hb : b.val ≤ bc.val) (hlen : buckets.length = b.val)
    (hbk : ∀ j < b.val, buckets.val[j]!.OnCurve ∧ buckets.val[j]!.LimbsLt 52 ∧
      buckets.val[j]!.toPoint = 0) :
    optional_multiscalar_mul_loop0 bc buckets b
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables») => BucketsOK r bc.val ⦄ := by
  unfold optional_multiscalar_mul_loop0
  apply loop.spec_decr_nat (measure := fun (_, b') => bc.val - b'.val)
    (inv := fun (v, b') => b'.val ≤ bc.val ∧ v.length = b'.val ∧
      ∀ j < b'.val, v.val[j]!.OnCurve ∧ v.val[j]!.LimbsLt 52 ∧ v.val[j]!.toPoint = 0)
  · rintro ⟨v, b'⟩ ⟨hb', hl, hv⟩
    unfold optional_multiscalar_mul_loop0.body
    by_cases hlt : b' < bc
    · simp only [hlt, ite_true]
      step with Curve25519_dalekTraitsIdentity.identity_spec_point
        as ⟨e, heon, he, heb⟩
      step as ⟨v1, hv1⟩
      step as ⟨b1, hb1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hv1, hl, hb1], ?_,
        by scalar_tac⟩
      rw [hb1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append
        (P := fun _ x => x.OnCurve ∧ x.LimbsLt 52 ∧ x.toPoint = 0) hv1 (hl ▸ hv) ⟨heon, heb, he⟩
    · simp only [hlt, ite_false, WP.spec_ok]
      have : b'.val = bc.val := by scalar_tac
      exact ⟨this ▸ hl, fun j hj => ⟨(hv j (this ▸ hj)).1, (hv j (this ▸ hj)).2.1⟩⟩
  · exact ⟨hb, hlen, hbk⟩

open edwards.EdwardsPoint.«x86_64-no-tables».Insts in
/-- The reset loop: every bucket becomes the identity. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop0_spec (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables») (b : Usize)
    (hok : BucketsOK buckets bc.val) (hb : b.val ≤ bc.val)
    (hz : ∀ j < b.val, buckets.val[j]!.toPoint = 0) :
    optional_multiscalar_mul_loop1_loop0 bc buckets b
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables») =>
        BucketsOK r bc.val ∧ ∀ j < bc.val, r.val[j]!.toPoint = 0 ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop0
  apply loop.spec_decr_nat (measure := fun (_, b') => bc.val - b'.val)
    (inv := fun (v, b') => b'.val ≤ bc.val ∧ BucketsOK v bc.val ∧
      ∀ j < b'.val, v.val[j]!.toPoint = 0)
  · rintro ⟨v, b'⟩ ⟨hb', ⟨hl, hv⟩, hvz⟩
    unfold optional_multiscalar_mul_loop1_loop0.body
    by_cases hlt : b' < bc
    · simp only [hlt, ite_true]
      step with Curve25519_dalekTraitsIdentity.identity_spec_point
        as ⟨e, heon, he, heb⟩
      step as ⟨x, back, hx, hback⟩
      step as ⟨b1, hb1⟩
      have hbl : b'.val < v.val.length := by
        rw [show v.val.length = v.length from rfl, hl]; scalar_tac
      refine ⟨by scalar_tac, ⟨?_, fun j hj => ?_⟩, fun j hj => ?_, by scalar_tac⟩
      · rw [hback, alloc.vec.Vec.set_length, hl]
      · rw [hback, alloc.vec.Vec.set_val_eq]
        rcases eq_or_ne j b'.val with rfl | hne
        · rw [getElem!_set_eq' _ _ _ hbl]; exact ⟨heon, heb⟩
        · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
      · rw [hback, alloc.vec.Vec.set_val_eq]
        rcases eq_or_ne j b'.val with rfl | hne
        · rw [getElem!_set_eq' _ _ _ hbl]; exact he
        · rw [getElem!_set_ne' _ _ _ _ hne]; exact hvz j (by scalar_tac)
    · simp only [hlt, ite_false, WP.spec_ok]
      have : b'.val = bc.val := by scalar_tac
      exact ⟨⟨hl, hv⟩, fun j hj => hvz j (this ▸ hj)⟩
  · exact ⟨hb, hok, hz⟩

open edwards.EdwardsPoint.«x86_64-no-tables».Insts in
/-- The running sums: `buckets_sum` ends as `∑_b (b + 1) • bucket_b`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop2_spec
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables») (bc : ℕ)
    (hok : BucketsOK buckets bc) (inter sum : edwards.EdwardsPoint.«x86_64-no-tables») (i : Usize)
    (hi : i.val < bc) (hinter : inter.OnCurve ∧ inter.LimbsLt 52 ∧
      inter.toPoint = ∑ b ∈ Finset.Ico i.val bc, buckets.val[b]!.toPoint)
    (hsum : sum.OnCurve ∧ sum.LimbsLt 52 ∧
      sum.toPoint = ∑ b ∈ Finset.Ico i.val bc, (b - i.val + 1) • buckets.val[b]!.toPoint) :
    optional_multiscalar_mul_loop1_loop2 buckets inter sum i
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») => r.OnCurve ∧ r.LimbsLt 52 ∧
        r.toPoint = wsum edwards.EdwardsPoint.«x86_64-no-tables».toPoint buckets.val bc ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop2
  apply loop.spec_decr_nat (measure := fun (_, _, i') => i'.val)
    (inv := fun (it, sm, i') => i'.val < bc ∧
      it.OnCurve ∧ it.LimbsLt 52 ∧
        it.toPoint = ∑ b ∈ Finset.Ico i'.val bc, buckets.val[b]!.toPoint ∧
      sm.OnCurve ∧ sm.LimbsLt 52 ∧
        sm.toPoint = ∑ b ∈ Finset.Ico i'.val bc, (b - i'.val + 1) • buckets.val[b]!.toPoint)
  · rintro ⟨it, sm, i'⟩ ⟨hi', hiton, hitb, hitp, hsmon, hsmb, hsmp⟩
    unfold optional_multiscalar_mul_loop1_loop2.body
    by_cases hpos : i' > 0#usize
    · simp only [hpos, ite_true]
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < bc := by scalar_tac
      step as ⟨ep, hep⟩
      rw [← getElem!_pos] at hep
      obtain ⟨hepon, hepb⟩ := hok.2 i1.val hi1b
      rw [← hep] at hepon hepb
      step with «CoreOpsArithAddAssignEdwardsPointx86_64-no-tables».add_assign_spec_point
        it ep hitb hepb hiton hepon as ⟨it1, hit1on, hit1, hit1b⟩
      step with «CoreOpsArithAddAssignEdwardsPointx86_64-no-tables».add_assign_spec_point
        sm it1 hsmb hit1b hsmon hit1on as ⟨sm1, hsm1on, hsm1, hsm1b⟩
      have hii : i'.val = i1.val + 1 := by scalar_tac
      have hsum1 : ∑ b ∈ Finset.Ico i1.val bc, buckets.val[b]!.toPoint =
          ∑ b ∈ Finset.Ico i'.val bc, buckets.val[b]!.toPoint + ep.toPoint := by
        rw [Finset.sum_eq_sum_Ico_succ_bot hi1b, hii, hep, add_comm]
      refine ⟨hi1b, hit1on, hit1b, by rw [hit1, hitp, hsum1], hsm1on, hsm1b, ?_,
        by rw [hii]; exact Nat.lt_succ_self _⟩
      rw [hsm1, hit1, hsmp, hitp, ← hsum1, hii]
      exact running_sum_step (fun b => buckets.val[b]!.toPoint) i1.val bc hi1b
    · simp only [hpos, ite_false, WP.spec_ok]
      have h0 : i'.val = 0 := by scalar_tac
      refine ⟨hsmon, hsmb, ?_⟩
      rw [hsmp, h0, wsum, Finset.range_eq_Ico]
      exact Finset.sum_congr rfl fun b _ => by rw [Nat.sub_zero]
  · exact ⟨hi, hinter.1, hinter.2.1, hinter.2.2, hsum.1, hsum.2.1, hsum.2.2⟩

open scoped Helpers.IndexStep in
/-- The accumulation loop: point `k` (from `si` on) is added to bucket `d_k[e] - 1`, or subtracted
from bucket `-d_k[e] - 1`; the weighted sum of the buckets grows by `d_k[e] • P_k`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop1_spec
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-no-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables») (e si : Usize) (bc : ℕ)
    (P : ℕ → curve25519.edwards.Point) (he : e.val < 64) (hbc : bc ≤ 128)
    (hsp : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 54 ∧
      (sp.val[k]!).2.toPoint = P k)
    (hdig : ∀ k < sp.length, -(bc : ℤ) ≤ (sp.val[k]!).1[e.val]!.val ∧
      (sp.val[k]!).1[e.val]!.val ≤ bc)
    (hok : BucketsOK buckets bc) (hsi : si.val ≤ sp.length) :
    optional_multiscalar_mul_loop1_loop1 sp buckets e si
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables») => BucketsOK r bc ∧
        wsum edwards.EdwardsPoint.«x86_64-no-tables».toPoint r.val bc =
          wsum edwards.EdwardsPoint.«x86_64-no-tables».toPoint buckets.val bc +
            ∑ k ∈ Finset.Ico si.val sp.length, (sp.val[k]!).1[e.val]!.val • P k ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop1
  apply loop.spec_decr_nat (measure := fun (_, si') => sp.length - si'.val)
    (inv := fun (v, si') => si.val ≤ si'.val ∧ si'.val ≤ sp.length ∧ BucketsOK v bc ∧
      wsum edwards.EdwardsPoint.«x86_64-no-tables».toPoint v.val bc =
        wsum edwards.EdwardsPoint.«x86_64-no-tables».toPoint buckets.val bc +
          ∑ k ∈ Finset.Ico si.val si'.val, (sp.val[k]!).1[e.val]!.val • P k)
  · rintro ⟨v, si'⟩ ⟨hss, hsl, ⟨hvl, hv⟩, hw⟩
    unfold optional_multiscalar_mul_loop1_loop1.body
    by_cases hlt : si'.val < sp.length
    · have hlt' : si' < alloc.vec.Vec.len sp := by scalar_tac
      simp only [hlt', ite_true]
      step as ⟨digits, pt, hdp⟩
      rw [← getElem!_pos] at hdp
      obtain ⟨hpton, hptb, hptp⟩ := hsp si'.val hlt
      obtain ⟨hdl, hdu⟩ := hdig si'.val hlt
      rw [← hdp] at hpton hptb hptp hdl hdu
      simp only at hpton hptb hptp hdl hdu
      step as ⟨d8, hd8⟩
      step with IScalar.cast_inBounds_spec as ⟨d, hd⟩
      rw [show lift (core.cmp.impls.OrdI16.cmp d 0#i16) = ok (compare d.val 0) from rfl, bind_ok]
      apply spec_bind (Pₘ := fun v1 => BucketsOK v1 bc ∧
        wsum edwards.EdwardsPoint.«x86_64-no-tables».toPoint v1.val bc =
          wsum edwards.EdwardsPoint.«x86_64-no-tables».toPoint v.val bc + d.val • P si'.val)
      · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
        · rw [(compare_lt_iff_lt).mpr hneg]
          simp only
          step as ⟨i2, hi2⟩
          step as ⟨i3, hi3⟩
          step with IScalar.hcast_inBounds_spec as ⟨b, hb⟩
          have hbv : b.val + 1 = (-d.val).toNat := by scalar_tac
          have hbl : b.val < bc := by scalar_tac
          step as ⟨ep, hep⟩
          rw [← getElem!_pos] at hep
          obtain ⟨hepon, hepb⟩ := hv b.val hbl
          rw [← hep] at hepon hepb
          step with sub_spec_point ep pt hepb hptb hepon hpton as ⟨c, hcon, hc, hcb⟩
          step with «CompletedPointx86_64-no-tables».as_extended_spec_point as
              ⟨ep1, hep1on, hep1, hep1b⟩
          step as ⟨y, back, hy, hback⟩
          have hbl' : b.val < v.val.length := by
            rw [show v.val.length = v.length from rfl, hvl]; exact hbl
          refine ⟨⟨by rw [hback, alloc.vec.Vec.set_length, hvl], fun j hj => ?_⟩, ?_⟩
          · rw [hback, alloc.vec.Vec.set_val_eq]
            rcases eq_or_ne j b.val with rfl | hne
            · rw [getElem!_set_eq' _ _ _ hbl']; exact ⟨hep1on, hep1b⟩
            · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
          · rw [hback, alloc.vec.Vec.set_val_eq, wsum_set _ _ _ _ hbl hvl, hep1, hc, ← hep, hptp]
            congr 1
            rw [sub_sub_cancel_left, smul_neg, ← natCast_zsmul, ← neg_zsmul]
            congr 1
            push_cast
            omega
        · rw [(compare_eq_iff_eq).mpr hzero]
          simp only [WP.spec_ok]
          rw [hzero, zero_smul, add_zero]
          exact ⟨⟨hvl, hv⟩, rfl⟩
        · rw [(compare_gt_iff_gt).mpr hpos]
          simp only
          step as ⟨i2, hi2⟩
          step with IScalar.hcast_inBounds_spec as ⟨b, hb⟩
          have hbv : b.val + 1 = d.val.toNat := by scalar_tac
          have hbl : b.val < bc := by scalar_tac
          step as ⟨ep, hep⟩
          rw [← getElem!_pos] at hep
          obtain ⟨hepon, hepb⟩ := hv b.val hbl
          rw [← hep] at hepon hepb
          step with add_spec_point ep pt hepb hptb hepon hpton as ⟨c, hcon, hc, hcb⟩
          step with «CompletedPointx86_64-no-tables».as_extended_spec_point as
              ⟨ep1, hep1on, hep1, hep1b⟩
          step as ⟨y, back, hy, hback⟩
          have hbl' : b.val < v.val.length := by
            rw [show v.val.length = v.length from rfl, hvl]; exact hbl
          refine ⟨⟨by rw [hback, alloc.vec.Vec.set_length, hvl], fun j hj => ?_⟩, ?_⟩
          · rw [hback, alloc.vec.Vec.set_val_eq]
            rcases eq_or_ne j b.val with rfl | hne
            · rw [getElem!_set_eq' _ _ _ hbl']; exact ⟨hep1on, hep1b⟩
            · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
          · rw [hback, alloc.vec.Vec.set_val_eq, wsum_set _ _ _ _ hbl hvl, hep1, hc, ← hep, hptp]
            congr 1
            rw [add_sub_cancel_left, ← natCast_zsmul]
            congr 1
            push_cast
            omega
      · rintro v1 ⟨hok1, hw1⟩
        step as ⟨si1, hsi1⟩
        refine ⟨by scalar_tac, by scalar_tac, hok1, ?_, by scalar_tac⟩
        rw [hw1, hw, show si1.val = si'.val + 1 by scalar_tac, Finset.sum_Ico_succ_top hss,
          add_assoc, hd, hd8, ← hdp]
    · have hge : ¬ si' < alloc.vec.Vec.len sp := by scalar_tac
      simp only [hge, ite_false, WP.spec_ok]
      have : si'.val = sp.length := by scalar_tac
      exact ⟨⟨hvl, hv⟩, this ▸ hw⟩
  · exact ⟨le_refl _, hsi, hok, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The column of digit position `e`: `∑_k d_k[e] • P_k`. -/
private noncomputable def column
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-no-tables»))
    (P : ℕ → curve25519.edwards.Point) (e : ℕ) : curve25519.edwards.Point :=
  ∑ k ∈ Finset.range sp.length, ((sp.val[k]!).1[e]!.val : ℤ) • P k

open edwards.EdwardsPoint.«x86_64-no-tables».Insts in
open scoped Helpers.IndexStep in
/-- The outer loop over the digit positions, from the top: the total is
`∑_{j} 2^(w j) • column (di + j)` over the positions processed. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_spec (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-no-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables»)
    (total : Option edwards.EdwardsPoint.«x86_64-no-tables») (di : Usize)
    (P : ℕ → curve25519.edwards.Point) (dc : ℕ) (hw : 0 < w.val ∧ w.val ≤ 8)
    (hbc1 : 1 ≤ bc.val) (hbc : bc.val ≤ 128) (hdc : dc ≤ 64)
    (hsp : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 54 ∧
      (sp.val[k]!).2.toPoint = P k)
    (hdig : ∀ k < sp.length, ∀ e < 64, -(bc.val : ℤ) ≤ (sp.val[k]!).1[e]!.val ∧
      (sp.val[k]!).1[e]!.val ≤ (bc.val : ℤ))
    (hok : BucketsOK buckets bc.val) (hdi : di.val ≤ dc)
    (hnone : total = none ↔ di.val = dc)
    (hsome : ∀ T, total = some T → T.OnCurve ∧ T.LimbsLt 52 ∧
      T.toPoint = ∑ j ∈ Finset.range (dc - di.val), 2 ^ (w.val * j) • column sp P (di.val + j)) :
    optional_multiscalar_mul_loop1 w bc sp buckets total di
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (r = none ↔ dc = 0) ∧
        ∀ T, r = some T → T.OnCurve ∧ T.LimbsLt 52 ∧
          T.toPoint = ∑ j ∈ Finset.range dc, 2 ^ (w.val * j) • column sp P j ⦄ := by
  unfold optional_multiscalar_mul_loop1
  apply loop.spec_decr_nat (measure := fun (_, _, d) => d.val)
    (inv := fun (v, t, d) => BucketsOK v bc.val ∧ d.val ≤ dc ∧ (t = none ↔ d.val = dc) ∧
      ∀ T, t = some T → T.OnCurve ∧ T.LimbsLt 52 ∧
        T.toPoint = ∑ j ∈ Finset.range (dc - d.val), 2 ^ (w.val * j) • column sp P (d.val + j))
  · rintro ⟨v, t, d⟩ ⟨hv, hd, htn, hts⟩
    unfold optional_multiscalar_mul_loop1.body
    by_cases hpos : d > 0#usize
    · simp only [hpos, ite_true]
      step as ⟨d1, hd1⟩
      have hdpos : 0 < d.val := hpos
      have hdd : d.val = d1.val + 1 := by rw [hd1]; exact (Nat.sub_add_cancel hdpos).symm
      have hd1lt : d1.val < dc := by
        rw [hd1]; exact lt_of_lt_of_le (Nat.sub_lt hdpos Nat.one_pos) hd
      have hd164 : d1.val < 64 := lt_of_lt_of_le hd1lt hdc
      step with optional_multiscalar_mul_loop1_loop0_spec bc v 0#usize hv (Nat.zero_le _)
        (fun j hj => absurd hj (Nat.not_lt_zero j)) as ⟨v1, hv1, hv1z⟩
      step with optional_multiscalar_mul_loop1_loop1_spec sp v1 d1 0#usize bc.val P
        hd164 hbc hsp (fun k hk => hdig k hk d1.val hd164) hv1
        (Nat.zero_le _) as ⟨v2, hv2, hw2⟩
      step as ⟨i, hi⟩
      have hib : i.val < bc.val := by
        rw [hi]; exact Nat.sub_lt (lt_of_lt_of_le Nat.one_pos hbc1) Nat.one_pos
      have hil : i.val < v2.val.length := by
        rw [show v2.val.length = v2.length from rfl, hv2.1]; exact hib
      step as ⟨inter, hinter⟩
      rw [← getElem!_pos] at hinter
      step as ⟨sm, hsm⟩
      rw [← getElem!_pos] at hsm
      have hIco : Finset.Ico i.val bc.val = {i.val} := by
        rw [show bc.val = i.val + 1 by rw [hi]; exact (Nat.sub_add_cancel hbc1).symm,
          Nat.Ico_succ_singleton]
      obtain ⟨hion, hib'⟩ := hv2.2 i.val hib
      step with optional_multiscalar_mul_loop1_loop2_spec v2 bc.val hv2 inter sm i hib
        ⟨hinter ▸ hion, hinter ▸ hib', by rw [hIco, Finset.sum_singleton, hinter]⟩
        ⟨hsm ▸ hion, hsm ▸ hib', by
          rw [hIco, Finset.sum_singleton, hsm, Nat.sub_self, zero_add, one_smul]⟩
        as ⟨c, hcon, hcb, hc⟩
      have hzero : wsum edwards.EdwardsPoint.«x86_64-no-tables».toPoint v1.val bc.val = 0 :=
        Finset.sum_eq_zero fun b hb => by rw [hv1z b (Finset.mem_range.mp hb), smul_zero]
      have hcol : c.toPoint = column sp P d1.val := by
        rw [hc, hw2, hzero, zero_add, ← Finset.range_eq_Ico]
        rfl
      rcases t with _ | T
      · have hdc' : d.val = dc := htn.mp rfl
        dsimp only
        rw [WP.spec_ok]
        refine ⟨hv2, Nat.le_of_lt hd1lt,
          ⟨fun h => (by cases h), fun h => absurd h (Nat.ne_of_lt hd1lt)⟩,
          fun T' hT' => ?_, by rw [hdd]; exact Nat.lt_succ_self _⟩
        obtain rfl : c = T' := Option.some.inj hT'
        refine ⟨hcon, hcb, ?_⟩
        rw [hcol, show dc - d1.val = 1 by rw [← hdc', hdd, Nat.add_sub_cancel_left],
          Finset.sum_range_one, mul_zero, pow_zero, one_smul, add_zero]
      · obtain ⟨hTon, hTb, hT⟩ := hts T rfl
        have hdc' : d.val ≠ dc := fun h => by cases htn.mpr h
        dsimp only
        step as ⟨k, hk⟩
        have hkw : k.val = w.val := by
          rw [hk, UScalar.cast_val_eq]
          exact Nat.mod_eq_of_lt (lt_of_le_of_lt hw.2 (by decide))
        step with edwards.«EdwardsPointx86_64-no-tables».mul_by_pow_2_spec T k hTb hTon
            (by rw [hkw]; exact hw.1)
          as ⟨T2, hT2on, hT2, hT2b⟩
        step with
            «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables».add_spec_point
          T2 c hT2b hcb hT2on hcon as ⟨T3, hT3on, hT3, hT3b⟩
        refine ⟨hv2, Nat.le_of_lt hd1lt,
          ⟨fun h => (by cases h), fun h => absurd h (Nat.ne_of_lt hd1lt)⟩,
          fun T' hT' => ?_, by rw [hdd]; exact Nat.lt_succ_self _⟩
        obtain rfl : T3 = T' := Option.some.inj hT'
        refine ⟨hT3on, hT3b, ?_⟩
        have hdcd : dc - d1.val = (dc - d.val) + 1 := by
          rw [hdd, Nat.sub_add_eq]
          exact (Nat.sub_add_cancel (Nat.sub_pos_of_lt hd1lt)).symm
        rw [hT3, hT2, hT, hcol, hkw, hdcd, Finset.sum_range_succ', Finset.smul_sum]
        rw [mul_zero, pow_zero, one_smul, add_zero]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, ← pow_add, hdd, show w.val + w.val * j = w.val * (j + 1) by ring,
          show d1.val + 1 + j = d1.val + (j + 1) by ring]
    · simp only [hpos, ite_false, WP.spec_ok]
      have h0 : d.val = 0 := by scalar_tac
      refine ⟨by rw [htn, h0]; exact eq_comm, fun T hT => ?_⟩
      obtain ⟨hTon, hTb, hT'⟩ := hts T hT
      refine ⟨hTon, hTb, ?_⟩
      rw [hT', h0, Nat.sub_zero]
      exact Finset.sum_congr rfl fun j _ => by rw [zero_add]
  · exact ⟨hok, hdi, hnone, hsome⟩

/-- The pairs collected by `scalars_points`, up to `m`: digits of `ss[j]` and the projective Niels
form of the point `ops[j] = some P`. -/
private def PairsOK (w : ℕ) (ss : List scalar.Scalar)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (v : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-no-tables»)) (m : ℕ) :
        Prop :=
  v.length = m ∧ ∀ j < m, ∃ P, ops[j]! = some P ∧
    (v.val[j]!).2.OnCurve ∧ (v.val[j]!).2.LimbsLt 54 ∧ (v.val[j]!).2.toPoint = P.toPoint ∧
    (v.val[j]!).1.asInt w = ss[j]!.asNat ∧
    (∀ i < 64, -2 ^ w ≤ 2 * (v.val[j]!).1[i]!.val ∧ 2 * (v.val[j]!).1[i]!.val ≤ 2 ^ w) ∧
    ∀ i < 64, 256 < i * w → (v.val[j]!).1[i]!.val = 0

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

namespace «VartimeMultiscalarMulPippengerEdwardsPointx86_64-no-tables».optional_multiscalar_mul

open Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

/-- The loop of `scalars_points`: the digits of each scalar with the next point, until the
scalars or the points run out; `none` at the first `none` point. -/
@[local step]
private theorem scalars_points_loop_spec {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It
        (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (scalars : Slice S) (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) scalars.val ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (w : Usize) (hw : 4 ≤ w.val ∧ w.val ≤ 8)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve) (points : It) (k : Usize)
    (hit : iterInst.Yields points (ops.drop k.val)) (hk : k.val ≤ ss.length)
    (hkops : k.val ≤ ops.length)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-no-tables»))
    (hout : PairsOK w.val ss ops out k.val) :
    scalars_points_loop borrowInst iterInst scalars points w out k
      ⦃ (r : Option (alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-no-tables»)))
          =>
        (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ v, r = some v → PairsOK w.val ss ops v (min ss.length ops.length) ⦄ := by
  have hslen : scalars.val.length = ss.length := hborrow.length_eq
  have hsb : ∀ k (hk : k < scalars.val.length),
      borrowInst.borrow scalars.val[k] ⦃ (s' : scalar.Scalar) => s' = ss[k]! ⦄ := fun k hk => by
    rw [getElem!_pos ss k (hslen ▸ hk)]
    exact (List.forall₂_iff_get.mp hborrow).2 k hk _
  unfold scalars_points_loop
  apply loop.spec_decr_nat (measure := fun (_, _, k') => ss.length - k'.val)
    (inv := fun (it, o, k') => iterInst.Yields it (ops.drop k'.val) ∧ k'.val ≤ ss.length ∧
      k'.val ≤ ops.length ∧ PairsOK w.val ss ops o k'.val)
  · rintro ⟨it, o, k'⟩ ⟨hit', hk', hko, hpo⟩
    unfold scalars_points_loop.body
    by_cases hlt : k'.val < ss.length
    · have hlt' : k' < Slice.len scalars := by scalar_tac
      simp only [hlt', ite_true]
      step as ⟨t, ht⟩
      subst ht
      step with hsb k'.val (by scalar_tac) as ⟨s, hs⟩
      have hs' : s.asNat < 2 ^ 255 := hs ▸ hss _
          (by rw [getElem!_pos ss _ hlt]; exact List.getElem_mem _)
      step with scalar.Scalar.as_radix_2w_spec s w hw hs' as ⟨d, hdv, hdlow, hdall, hdz⟩
      generalize hrest : ops.drop k'.val = rest at hit'
      cases hit' with
      | nil hnext =>
        step with hnext as ⟨o', it1, hq⟩
        subst hq
        dsimp only
        rw [WP.spec_ok]
        have hko' : k'.val = ops.length := by
          have := congrArg List.length hrest
          simp at this; scalar_tac
        refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun v hv => ?_⟩
        · rw [List.take_of_length_le (by scalar_tac)] at h
          obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem h
          obtain ⟨P, hP, -⟩ := hpo.2 j (by scalar_tac)
          rw [getElem!_pos ops j hj, hjn] at hP
          cases hP
        · obtain rfl := Option.some.inj hv
          rwa [show min ss.length ops.length = k'.val by scalar_tac]
      | @cons it it' x xs' hnext hrest' =>
        step with hnext as ⟨o', it1, ho, hit1⟩
        subst ho hit1
        have hk'o : k'.val < ops.length := by
          by_contra hcon
          rw [List.drop_eq_nil_of_le (by scalar_tac)] at hrest
          cases hrest
        have hx : ops[k'.val]! = x := by
          rw [getElem!_pos ops k'.val hk'o]
          have := List.drop_eq_getElem_cons hk'o
          rw [hrest] at this
          exact (List.cons.inj this).1.symm
        have hxs : xs' = ops.drop (k'.val + 1) := by
          have := List.drop_eq_getElem_cons hk'o
          rw [hrest] at this
          exact (List.cons.inj this).2
        rcases x with _ | P
        · dsimp only
          rw [WP.spec_ok]
          refine ⟨⟨fun _ => ?_, fun _ => rfl⟩, fun v hv => by cases hv⟩
          rw [← hx]
          exact List.mem_take_iff_getElem.mpr ⟨k'.val, by simp only [lt_min_iff]; scalar_tac, by
            rw [getElem!_pos ops k'.val hk'o]⟩
        · have hPmem : some P ∈ ops := by
            rw [← hx, getElem!_pos ops k'.val hk'o]; exact List.getElem_mem _
          obtain ⟨hPb, hPon⟩ := hps P hPmem
          step with edwards.«EdwardsPointx86_64-no-tables».as_projective_niels_spec_point P hPb hPon
            as ⟨pnp, hpon, hpp, hpb⟩
          step with alloc.vec.Vec.push_spec o (d, pnp) (by
            have := hpo.1; have := alloc.vec.Vec.len_ineq o; scalar_tac) as ⟨o1, ho1⟩
          step as ⟨k1, hk1⟩
          have hk1v : k1.val = k'.val + 1 := by scalar_tac
          refine ⟨by rw [hk1v, ← hxs]; exact hrest', by scalar_tac, by scalar_tac,
            ⟨by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hpo.1, hk1v], fun j hj => ?_⟩,
            by scalar_tac⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp (hk1v ▸ hj) with hj' | rfl
          · have hjo : j < o.length := hpo.1 ▸ hj'
            rw [show o1.val[j]! = o1[j]! from rfl,
              alloc.vec.Vec.getElem!_of_val_eq_append_of_lt ho1 hjo]
            exact hpo.2 j hj'
          · have := alloc.vec.Vec.getElem!_of_val_eq_append_length ho1
            rw [hpo.1] at this
            rw [show o1.val[k'.val]! = o1[k'.val]! from rfl, this]
            exact ⟨P, hx, hpon, hpb, hpp, by rw [hdv, hs], hdall, hdz⟩
    · have hge : ¬ k' < Slice.len scalars := by scalar_tac
      simp only [hge, ite_false, WP.spec_ok]
      have hks : k'.val = ss.length := by scalar_tac
      refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun v hv => ?_⟩
      · obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem h
        simp only [List.length_take] at hj
        obtain ⟨P, hP, -⟩ := hpo.2 j (by scalar_tac)
        rw [getElem!_pos ops j (by scalar_tac), ← List.getElem_take (j := ss.length)] at hP
        · rw [hjn] at hP; cases hP
        · rw [List.length_take]; exact hj
      · obtain rfl := Option.some.inj hv
        rwa [show min ss.length ops.length = k'.val by scalar_tac]
  · exact ⟨hit, hk, hkops, hout⟩

end «VartimeMultiscalarMulPippengerEdwardsPointx86_64-no-tables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

open «VartimeMultiscalarMulPippengerEdwardsPointx86_64-no-tables» in
/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^52`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«x86_64-no-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») =>
          (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold optional_multiscalar_mul.collect optional_multiscalar_mul.collect_loop
  apply spec_bind (collect.collectLoop_spec _ it xs hit (alloc.vec.Vec.new _) (by simpa using hxs))
  intro vs hvs
  replace hvs : vs.val = xs := by rw [hvs]; rfl
  apply spec_bind (Pₘ := fun (w : Usize) => 6 ≤ w.val ∧ w.val ≤ 8)
  · split_ifs <;> rw [WP.spec_ok] <;> decide
  intro w hw
  have hw256 : 2 ^ w.val ≤ 256 := Nat.pow_le_pow_right (by norm_num) hw.2
  step with Usize.ShiftLeft_spec 1#usize w (by
      rcases System.Platform.numBits_eq with h | h <;> simp only [h] <;> scalar_tac)
    as ⟨md, hmd, hmdbv⟩
  have hmd' : md.val = 2 ^ w.val := by
    rw [hmd, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  step with scalar.Scalar.to_radix_2w_size_hint_spec w ⟨by scalar_tac, hw.2⟩ as
      ⟨dc, hdc4, hdc5, hdc6, hdc7, hdc8⟩
  step as ⟨bc, hbc⟩
  have hbc' : 2 * bc.val = 2 ^ w.val := by
    rw [hbc, hmd']
    exact Nat.mul_div_cancel' (dvd_pow_self 2 (by scalar_tac))
  have hbc8 : bc.val ≤ 128 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hw.2; scalar_tac
  have hbc1 : 1 ≤ bc.val := by
    have := Nat.one_le_two_pow (n := w.val); scalar_tac
  have hdcw : dc.val ≤ 64 ∧ ∀ i, dc.val ≤ i → 256 < i * w.val := by
    rcases (show w.val = 6 ∨ w.val = 7 ∨ w.val = 8 by scalar_tac) with h | h | h
    · rw [hdc6 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
    · rw [hdc7 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
    · rw [hdc8 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
  have hdc0 : dc.val ≠ 0 := by
    rcases (show w.val = 6 ∨ w.val = 7 ∨ w.val = 8 by scalar_tac) with h | h | h
    · rw [hdc6 h]; decide
    · rw [hdc7 h]; decide
    · rw [hdc8 h]; decide
  step with hpoints' as ⟨it1, hit1⟩
  step with optional_multiscalar_mul.scalars_points_loop_spec
    _ _ _ ss (by rw [show (alloc.vec.Vec.deref vs).val = vs.val from Slice.from_val _ _, hvs]; exact
        hborrow_scalars) hss w
    ⟨by scalar_tac, hw.2⟩ ops hps it1 0#usize (by simpa using hit1) (Nat.zero_le _) (Nat.zero_le _)
    (alloc.vec.Vec.new _) ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    as ⟨o, hnone, hsome⟩
  rcases o with _ | sp
  · dsimp only
    rw [WP.spec_ok]
    exact ⟨by simpa using hnone, fun R hR => by cases hR⟩
  · have hnn : none ∉ ops.take ss.length := fun h => by cases hnone.mpr h
    obtain ⟨hsplen, hsp⟩ := hsome sp rfl
    let P : ℕ → curve25519.edwards.Point := fun k => ((ops[k]!).getD default).toPoint
    have hsp' : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 54 ∧
        (sp.val[k]!).2.toPoint = P k := fun k hk => by
      obtain ⟨Q, hQ, hon, hb, hp, -⟩ := hsp k (hsplen ▸ hk)
      exact ⟨hon, hb, by rw [hp]; change Q.toPoint = ((ops[k]!).getD default).toPoint; rw [hQ]; rfl⟩
    have hdig : ∀ k < sp.length, ∀ e < 64, -(bc.val : ℤ) ≤ (sp.val[k]!).1[e]!.val ∧
        (sp.val[k]!).1[e]!.val ≤ (bc.val : ℤ) := fun k hk e he => by
      obtain ⟨Q, -, -, -, -, -, hb, -⟩ := hsp k (hsplen ▸ hk)
      have := hb e he
      have hbz : (2 : ℤ) ^ w.val = 2 * bc.val := by exact_mod_cast hbc'.symm
      rw [hbz] at this
      constructor <;> linarith [this.1, this.2]
    step with optional_multiscalar_mul_loop0_spec bc (alloc.vec.Vec.new _) 0#usize hbc8
      (Nat.zero_le _) rfl (fun j hj => absurd hj (Nat.not_lt_zero j)) as ⟨b, hb⟩
    step with optional_multiscalar_mul_loop1_spec w bc sp b none dc P dc.val
      ⟨by scalar_tac, hw.2⟩ hbc1 hbc8 hdcw.1 hsp' hdig hb (le_refl _) ⟨fun _ => rfl, fun _ => rfl⟩
      (fun T hT => by cases hT) as ⟨t, htn, hts⟩
    rcases t with _ | T
    · exact absurd (htn.mp rfl) hdc0
    obtain ⟨hTon, hTb, hT⟩ := hts T rfl
    step with core.option.Option.expect.spec as ⟨R, hR⟩
    obtain rfl : T = R := Option.some.inj hR
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : T = R' := Option.some.inj hR'
    refine ⟨hTon, ?_, hTb⟩
    unfold column at hT
    rw [hT, sum_zipWith_filterMap _ _ _ hnn, ← hsplen, sum_columns]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    obtain ⟨Q, hQ, -, -, -, hval, -, hz⟩ := hsp k (hsplen ▸ hk')
    rw [sum_digits _ _ _ hdcw.1 fun j hj hj' => hz j hj (hdcw.2 j hj'), hval, natCast_zsmul]

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

end

section
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
    (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
    (sub_spec_point)

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

/-- The buckets of `optional_multiscalar_mul`: `n` points on the curve within the limb bounds. -/
private def BucketsOK (v : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables») (n : ℕ) : Prop :=
  v.length = n ∧ ∀ j < n, v.val[j]!.OnCurve ∧ v.val[j]!.LimbsLt 26

open edwards.EdwardsPoint.«i686-no-tables».Insts in
/-- The first loop: `buckets_count` identities. -/
@[local step]
private theorem optional_multiscalar_mul_loop0_spec (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables») (b : Usize)
        (hbc : bc.val ≤ 128)
    (hb : b.val ≤ bc.val) (hlen : buckets.length = b.val)
    (hbk : ∀ j < b.val, buckets.val[j]!.OnCurve ∧ buckets.val[j]!.LimbsLt 26 ∧
      buckets.val[j]!.toPoint = 0) :
    optional_multiscalar_mul_loop0 bc buckets b
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables») => BucketsOK r bc.val ⦄ := by
  unfold optional_multiscalar_mul_loop0
  apply loop.spec_decr_nat (measure := fun (_, b') => bc.val - b'.val)
    (inv := fun (v, b') => b'.val ≤ bc.val ∧ v.length = b'.val ∧
      ∀ j < b'.val, v.val[j]!.OnCurve ∧ v.val[j]!.LimbsLt 26 ∧ v.val[j]!.toPoint = 0)
  · rintro ⟨v, b'⟩ ⟨hb', hl, hv⟩
    unfold optional_multiscalar_mul_loop0.body
    by_cases hlt : b' < bc
    · simp only [hlt, ite_true]
      step with Curve25519_dalekTraitsIdentity.identity_spec_point
        as ⟨e, heon, he, heb⟩
      step as ⟨v1, hv1⟩
      step as ⟨b1, hb1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hv1, hl, hb1], ?_,
        by scalar_tac⟩
      rw [hb1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append
        (P := fun _ x => x.OnCurve ∧ x.LimbsLt 26 ∧ x.toPoint = 0) hv1 (hl ▸ hv) ⟨heon, heb, he⟩
    · simp only [hlt, ite_false, WP.spec_ok]
      have : b'.val = bc.val := by scalar_tac
      exact ⟨this ▸ hl, fun j hj => ⟨(hv j (this ▸ hj)).1, (hv j (this ▸ hj)).2.1⟩⟩
  · exact ⟨hb, hlen, hbk⟩

open edwards.EdwardsPoint.«i686-no-tables».Insts in
/-- The reset loop: every bucket becomes the identity. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop0_spec (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables») (b : Usize)
    (hok : BucketsOK buckets bc.val) (hb : b.val ≤ bc.val)
    (hz : ∀ j < b.val, buckets.val[j]!.toPoint = 0) :
    optional_multiscalar_mul_loop1_loop0 bc buckets b
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables») =>
        BucketsOK r bc.val ∧ ∀ j < bc.val, r.val[j]!.toPoint = 0 ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop0
  apply loop.spec_decr_nat (measure := fun (_, b') => bc.val - b'.val)
    (inv := fun (v, b') => b'.val ≤ bc.val ∧ BucketsOK v bc.val ∧
      ∀ j < b'.val, v.val[j]!.toPoint = 0)
  · rintro ⟨v, b'⟩ ⟨hb', ⟨hl, hv⟩, hvz⟩
    unfold optional_multiscalar_mul_loop1_loop0.body
    by_cases hlt : b' < bc
    · simp only [hlt, ite_true]
      step with Curve25519_dalekTraitsIdentity.identity_spec_point
        as ⟨e, heon, he, heb⟩
      step as ⟨x, back, hx, hback⟩
      step as ⟨b1, hb1⟩
      have hbl : b'.val < v.val.length := by
        rw [show v.val.length = v.length from rfl, hl]; scalar_tac
      refine ⟨by scalar_tac, ⟨?_, fun j hj => ?_⟩, fun j hj => ?_, by scalar_tac⟩
      · rw [hback, alloc.vec.Vec.set_length, hl]
      · rw [hback, alloc.vec.Vec.set_val_eq]
        rcases eq_or_ne j b'.val with rfl | hne
        · rw [getElem!_set_eq' _ _ _ hbl]; exact ⟨heon, heb⟩
        · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
      · rw [hback, alloc.vec.Vec.set_val_eq]
        rcases eq_or_ne j b'.val with rfl | hne
        · rw [getElem!_set_eq' _ _ _ hbl]; exact he
        · rw [getElem!_set_ne' _ _ _ _ hne]; exact hvz j (by scalar_tac)
    · simp only [hlt, ite_false, WP.spec_ok]
      have : b'.val = bc.val := by scalar_tac
      exact ⟨⟨hl, hv⟩, fun j hj => hvz j (this ▸ hj)⟩
  · exact ⟨hb, hok, hz⟩

open edwards.EdwardsPoint.«i686-no-tables».Insts in
/-- The running sums: `buckets_sum` ends as `∑_b (b + 1) • bucket_b`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop2_spec
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables») (bc : ℕ)
    (hok : BucketsOK buckets bc) (inter sum : edwards.EdwardsPoint.«i686-no-tables») (i : Usize)
    (hi : i.val < bc) (hinter : inter.OnCurve ∧ inter.LimbsLt 26 ∧
      inter.toPoint = ∑ b ∈ Finset.Ico i.val bc, buckets.val[b]!.toPoint)
    (hsum : sum.OnCurve ∧ sum.LimbsLt 26 ∧
      sum.toPoint = ∑ b ∈ Finset.Ico i.val bc, (b - i.val + 1) • buckets.val[b]!.toPoint) :
    optional_multiscalar_mul_loop1_loop2 buckets inter sum i
      ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») => r.OnCurve ∧ r.LimbsLt 26 ∧
        r.toPoint = wsum edwards.EdwardsPoint.«i686-no-tables».toPoint buckets.val bc ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop2
  apply loop.spec_decr_nat (measure := fun (_, _, i') => i'.val)
    (inv := fun (it, sm, i') => i'.val < bc ∧
      it.OnCurve ∧ it.LimbsLt 26 ∧
        it.toPoint = ∑ b ∈ Finset.Ico i'.val bc, buckets.val[b]!.toPoint ∧
      sm.OnCurve ∧ sm.LimbsLt 26 ∧
        sm.toPoint = ∑ b ∈ Finset.Ico i'.val bc, (b - i'.val + 1) • buckets.val[b]!.toPoint)
  · rintro ⟨it, sm, i'⟩ ⟨hi', hiton, hitb, hitp, hsmon, hsmb, hsmp⟩
    unfold optional_multiscalar_mul_loop1_loop2.body
    by_cases hpos : i' > 0#usize
    · simp only [hpos, ite_true]
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < bc := by scalar_tac
      step as ⟨ep, hep⟩
      rw [← getElem!_pos] at hep
      obtain ⟨hepon, hepb⟩ := hok.2 i1.val hi1b
      rw [← hep] at hepon hepb
      step with «CoreOpsArithAddAssignEdwardsPointi686-no-tables».add_assign_spec_point
        it ep hitb hepb hiton hepon as ⟨it1, hit1on, hit1, hit1b⟩
      step with «CoreOpsArithAddAssignEdwardsPointi686-no-tables».add_assign_spec_point
        sm it1 hsmb hit1b hsmon hit1on as ⟨sm1, hsm1on, hsm1, hsm1b⟩
      have hii : i'.val = i1.val + 1 := by scalar_tac
      have hsum1 : ∑ b ∈ Finset.Ico i1.val bc, buckets.val[b]!.toPoint =
          ∑ b ∈ Finset.Ico i'.val bc, buckets.val[b]!.toPoint + ep.toPoint := by
        rw [Finset.sum_eq_sum_Ico_succ_bot hi1b, hii, hep, add_comm]
      refine ⟨hi1b, hit1on, hit1b, by rw [hit1, hitp, hsum1], hsm1on, hsm1b, ?_,
        by rw [hii]; exact Nat.lt_succ_self _⟩
      rw [hsm1, hit1, hsmp, hitp, ← hsum1, hii]
      exact running_sum_step (fun b => buckets.val[b]!.toPoint) i1.val bc hi1b
    · simp only [hpos, ite_false, WP.spec_ok]
      have h0 : i'.val = 0 := by scalar_tac
      refine ⟨hsmon, hsmb, ?_⟩
      rw [hsmp, h0, wsum, Finset.range_eq_Ico]
      exact Finset.sum_congr rfl fun b _ => by rw [Nat.sub_zero]
  · exact ⟨hi, hinter.1, hinter.2.1, hinter.2.2, hsum.1, hsum.2.1, hsum.2.2⟩

open scoped Helpers.IndexStep in
/-- The accumulation loop: point `k` (from `si` on) is added to bucket `d_k[e] - 1`, or subtracted
from bucket `-d_k[e] - 1`; the weighted sum of the buckets grows by `d_k[e] • P_k`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop1_spec
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-no-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables») (e si : Usize) (bc : ℕ)
    (P : ℕ → curve25519.edwards.Point) (he : e.val < 64) (hbc : bc ≤ 128)
    (hsp : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 27 ∧
      (sp.val[k]!).2.toPoint = P k)
    (hdig : ∀ k < sp.length, -(bc : ℤ) ≤ (sp.val[k]!).1[e.val]!.val ∧
      (sp.val[k]!).1[e.val]!.val ≤ bc)
    (hok : BucketsOK buckets bc) (hsi : si.val ≤ sp.length) :
    optional_multiscalar_mul_loop1_loop1 sp buckets e si
      ⦃ (r : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables») => BucketsOK r bc ∧
        wsum edwards.EdwardsPoint.«i686-no-tables».toPoint r.val bc =
          wsum edwards.EdwardsPoint.«i686-no-tables».toPoint buckets.val bc +
            ∑ k ∈ Finset.Ico si.val sp.length, (sp.val[k]!).1[e.val]!.val • P k ⦄ := by
  unfold optional_multiscalar_mul_loop1_loop1
  apply loop.spec_decr_nat (measure := fun (_, si') => sp.length - si'.val)
    (inv := fun (v, si') => si.val ≤ si'.val ∧ si'.val ≤ sp.length ∧ BucketsOK v bc ∧
      wsum edwards.EdwardsPoint.«i686-no-tables».toPoint v.val bc =
        wsum edwards.EdwardsPoint.«i686-no-tables».toPoint buckets.val bc +
          ∑ k ∈ Finset.Ico si.val si'.val, (sp.val[k]!).1[e.val]!.val • P k)
  · rintro ⟨v, si'⟩ ⟨hss, hsl, ⟨hvl, hv⟩, hw⟩
    unfold optional_multiscalar_mul_loop1_loop1.body
    by_cases hlt : si'.val < sp.length
    · have hlt' : si' < alloc.vec.Vec.len sp := by scalar_tac
      simp only [hlt', ite_true]
      step as ⟨digits, pt, hdp⟩
      rw [← getElem!_pos] at hdp
      obtain ⟨hpton, hptb, hptp⟩ := hsp si'.val hlt
      obtain ⟨hdl, hdu⟩ := hdig si'.val hlt
      rw [← hdp] at hpton hptb hptp hdl hdu
      simp only at hpton hptb hptp hdl hdu
      step as ⟨d8, hd8⟩
      step with IScalar.cast_inBounds_spec as ⟨d, hd⟩
      rw [show lift (core.cmp.impls.OrdI16.cmp d 0#i16) = ok (compare d.val 0) from rfl, bind_ok]
      apply spec_bind (Pₘ := fun v1 => BucketsOK v1 bc ∧
        wsum edwards.EdwardsPoint.«i686-no-tables».toPoint v1.val bc =
          wsum edwards.EdwardsPoint.«i686-no-tables».toPoint v.val bc + d.val • P si'.val)
      · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
        · rw [(compare_lt_iff_lt).mpr hneg]
          simp only
          step as ⟨i2, hi2⟩
          step as ⟨i3, hi3⟩
          step with IScalar.hcast_inBounds_spec as ⟨b, hb⟩
          have hbv : b.val + 1 = (-d.val).toNat := by scalar_tac
          have hbl : b.val < bc := by scalar_tac
          step as ⟨ep, hep⟩
          rw [← getElem!_pos] at hep
          obtain ⟨hepon, hepb⟩ := hv b.val hbl
          rw [← hep] at hepon hepb
          step with sub_spec_point ep pt hepb hptb hepon hpton as ⟨c, hcon, hc, hcb⟩
          step with «CompletedPointi686-no-tables».as_extended_spec_point as
              ⟨ep1, hep1on, hep1, hep1b⟩
          step as ⟨y, back, hy, hback⟩
          have hbl' : b.val < v.val.length := by
            rw [show v.val.length = v.length from rfl, hvl]; exact hbl
          refine ⟨⟨by rw [hback, alloc.vec.Vec.set_length, hvl], fun j hj => ?_⟩, ?_⟩
          · rw [hback, alloc.vec.Vec.set_val_eq]
            rcases eq_or_ne j b.val with rfl | hne
            · rw [getElem!_set_eq' _ _ _ hbl']; exact ⟨hep1on, hep1b⟩
            · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
          · rw [hback, alloc.vec.Vec.set_val_eq, wsum_set _ _ _ _ hbl hvl, hep1, hc, ← hep, hptp]
            congr 1
            rw [sub_sub_cancel_left, smul_neg, ← natCast_zsmul, ← neg_zsmul]
            congr 1
            push_cast
            omega
        · rw [(compare_eq_iff_eq).mpr hzero]
          simp only [WP.spec_ok]
          rw [hzero, zero_smul, add_zero]
          exact ⟨⟨hvl, hv⟩, rfl⟩
        · rw [(compare_gt_iff_gt).mpr hpos]
          simp only
          step as ⟨i2, hi2⟩
          step with IScalar.hcast_inBounds_spec as ⟨b, hb⟩
          have hbv : b.val + 1 = d.val.toNat := by scalar_tac
          have hbl : b.val < bc := by scalar_tac
          step as ⟨ep, hep⟩
          rw [← getElem!_pos] at hep
          obtain ⟨hepon, hepb⟩ := hv b.val hbl
          rw [← hep] at hepon hepb
          step with add_spec_point ep pt hepb hptb hepon hpton as ⟨c, hcon, hc, hcb⟩
          step with «CompletedPointi686-no-tables».as_extended_spec_point as
              ⟨ep1, hep1on, hep1, hep1b⟩
          step as ⟨y, back, hy, hback⟩
          have hbl' : b.val < v.val.length := by
            rw [show v.val.length = v.length from rfl, hvl]; exact hbl
          refine ⟨⟨by rw [hback, alloc.vec.Vec.set_length, hvl], fun j hj => ?_⟩, ?_⟩
          · rw [hback, alloc.vec.Vec.set_val_eq]
            rcases eq_or_ne j b.val with rfl | hne
            · rw [getElem!_set_eq' _ _ _ hbl']; exact ⟨hep1on, hep1b⟩
            · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
          · rw [hback, alloc.vec.Vec.set_val_eq, wsum_set _ _ _ _ hbl hvl, hep1, hc, ← hep, hptp]
            congr 1
            rw [add_sub_cancel_left, ← natCast_zsmul]
            congr 1
            push_cast
            omega
      · rintro v1 ⟨hok1, hw1⟩
        step as ⟨si1, hsi1⟩
        refine ⟨by scalar_tac, by scalar_tac, hok1, ?_, by scalar_tac⟩
        rw [hw1, hw, show si1.val = si'.val + 1 by scalar_tac, Finset.sum_Ico_succ_top hss,
          add_assoc, hd, hd8, ← hdp]
    · have hge : ¬ si' < alloc.vec.Vec.len sp := by scalar_tac
      simp only [hge, ite_false, WP.spec_ok]
      have : si'.val = sp.length := by scalar_tac
      exact ⟨⟨hvl, hv⟩, this ▸ hw⟩
  · exact ⟨le_refl _, hsi, hok, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The column of digit position `e`: `∑_k d_k[e] • P_k`. -/
private noncomputable def column
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-no-tables»))
    (P : ℕ → curve25519.edwards.Point) (e : ℕ) : curve25519.edwards.Point :=
  ∑ k ∈ Finset.range sp.length, ((sp.val[k]!).1[e]!.val : ℤ) • P k

open edwards.EdwardsPoint.«i686-no-tables».Insts in
open scoped Helpers.IndexStep in
/-- The outer loop over the digit positions, from the top: the total is
`∑_{j} 2^(w j) • column (di + j)` over the positions processed. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_spec (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-no-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables»)
    (total : Option edwards.EdwardsPoint.«i686-no-tables») (di : Usize)
    (P : ℕ → curve25519.edwards.Point) (dc : ℕ) (hw : 0 < w.val ∧ w.val ≤ 8)
    (hbc1 : 1 ≤ bc.val) (hbc : bc.val ≤ 128) (hdc : dc ≤ 64)
    (hsp : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 27 ∧
      (sp.val[k]!).2.toPoint = P k)
    (hdig : ∀ k < sp.length, ∀ e < 64, -(bc.val : ℤ) ≤ (sp.val[k]!).1[e]!.val ∧
      (sp.val[k]!).1[e]!.val ≤ (bc.val : ℤ))
    (hok : BucketsOK buckets bc.val) (hdi : di.val ≤ dc)
    (hnone : total = none ↔ di.val = dc)
    (hsome : ∀ T, total = some T → T.OnCurve ∧ T.LimbsLt 26 ∧
      T.toPoint = ∑ j ∈ Finset.range (dc - di.val), 2 ^ (w.val * j) • column sp P (di.val + j)) :
    optional_multiscalar_mul_loop1 w bc sp buckets total di
      ⦃ (r : Option edwards.EdwardsPoint.«i686-no-tables») => (r = none ↔ dc = 0) ∧
        ∀ T, r = some T → T.OnCurve ∧ T.LimbsLt 26 ∧
          T.toPoint = ∑ j ∈ Finset.range dc, 2 ^ (w.val * j) • column sp P j ⦄ := by
  unfold optional_multiscalar_mul_loop1
  apply loop.spec_decr_nat (measure := fun (_, _, d) => d.val)
    (inv := fun (v, t, d) => BucketsOK v bc.val ∧ d.val ≤ dc ∧ (t = none ↔ d.val = dc) ∧
      ∀ T, t = some T → T.OnCurve ∧ T.LimbsLt 26 ∧
        T.toPoint = ∑ j ∈ Finset.range (dc - d.val), 2 ^ (w.val * j) • column sp P (d.val + j))
  · rintro ⟨v, t, d⟩ ⟨hv, hd, htn, hts⟩
    unfold optional_multiscalar_mul_loop1.body
    by_cases hpos : d > 0#usize
    · simp only [hpos, ite_true]
      step as ⟨d1, hd1⟩
      have hdpos : 0 < d.val := hpos
      have hdd : d.val = d1.val + 1 := by rw [hd1]; exact (Nat.sub_add_cancel hdpos).symm
      have hd1lt : d1.val < dc := by
        rw [hd1]; exact lt_of_lt_of_le (Nat.sub_lt hdpos Nat.one_pos) hd
      have hd164 : d1.val < 64 := lt_of_lt_of_le hd1lt hdc
      step with optional_multiscalar_mul_loop1_loop0_spec bc v 0#usize hv (Nat.zero_le _)
        (fun j hj => absurd hj (Nat.not_lt_zero j)) as ⟨v1, hv1, hv1z⟩
      step with optional_multiscalar_mul_loop1_loop1_spec sp v1 d1 0#usize bc.val P
        hd164 hbc hsp (fun k hk => hdig k hk d1.val hd164) hv1
        (Nat.zero_le _) as ⟨v2, hv2, hw2⟩
      step as ⟨i, hi⟩
      have hib : i.val < bc.val := by
        rw [hi]; exact Nat.sub_lt (lt_of_lt_of_le Nat.one_pos hbc1) Nat.one_pos
      have hil : i.val < v2.val.length := by
        rw [show v2.val.length = v2.length from rfl, hv2.1]; exact hib
      step as ⟨inter, hinter⟩
      rw [← getElem!_pos] at hinter
      step as ⟨sm, hsm⟩
      rw [← getElem!_pos] at hsm
      have hIco : Finset.Ico i.val bc.val = {i.val} := by
        rw [show bc.val = i.val + 1 by rw [hi]; exact (Nat.sub_add_cancel hbc1).symm,
          Nat.Ico_succ_singleton]
      obtain ⟨hion, hib'⟩ := hv2.2 i.val hib
      step with optional_multiscalar_mul_loop1_loop2_spec v2 bc.val hv2 inter sm i hib
        ⟨hinter ▸ hion, hinter ▸ hib', by rw [hIco, Finset.sum_singleton, hinter]⟩
        ⟨hsm ▸ hion, hsm ▸ hib', by
          rw [hIco, Finset.sum_singleton, hsm, Nat.sub_self, zero_add, one_smul]⟩
        as ⟨c, hcon, hcb, hc⟩
      have hzero : wsum edwards.EdwardsPoint.«i686-no-tables».toPoint v1.val bc.val = 0 :=
        Finset.sum_eq_zero fun b hb => by rw [hv1z b (Finset.mem_range.mp hb), smul_zero]
      have hcol : c.toPoint = column sp P d1.val := by
        rw [hc, hw2, hzero, zero_add, ← Finset.range_eq_Ico]
        rfl
      rcases t with _ | T
      · have hdc' : d.val = dc := htn.mp rfl
        dsimp only
        rw [WP.spec_ok]
        refine ⟨hv2, Nat.le_of_lt hd1lt,
          ⟨fun h => (by cases h), fun h => absurd h (Nat.ne_of_lt hd1lt)⟩,
          fun T' hT' => ?_, by rw [hdd]; exact Nat.lt_succ_self _⟩
        obtain rfl : c = T' := Option.some.inj hT'
        refine ⟨hcon, hcb, ?_⟩
        rw [hcol, show dc - d1.val = 1 by rw [← hdc', hdd, Nat.add_sub_cancel_left],
          Finset.sum_range_one, mul_zero, pow_zero, one_smul, add_zero]
      · obtain ⟨hTon, hTb, hT⟩ := hts T rfl
        have hdc' : d.val ≠ dc := fun h => by cases htn.mpr h
        dsimp only
        step as ⟨k, hk⟩
        have hkw : k.val = w.val := by
          rw [hk, UScalar.cast_val_eq]
          exact Nat.mod_eq_of_lt (lt_of_le_of_lt hw.2 (by decide))
        step with edwards.«EdwardsPointi686-no-tables».mul_by_pow_2_spec T k hTb hTon
            (by rw [hkw]; exact hw.1)
          as ⟨T2, hT2on, hT2, hT2b⟩
        step with
            «CoreOpsArithAddEdwardsPointi686-no-tablesEdwardsPointi686-no-tables».add_spec_point
          T2 c hT2b hcb hT2on hcon as ⟨T3, hT3on, hT3, hT3b⟩
        refine ⟨hv2, Nat.le_of_lt hd1lt,
          ⟨fun h => (by cases h), fun h => absurd h (Nat.ne_of_lt hd1lt)⟩,
          fun T' hT' => ?_, by rw [hdd]; exact Nat.lt_succ_self _⟩
        obtain rfl : T3 = T' := Option.some.inj hT'
        refine ⟨hT3on, hT3b, ?_⟩
        have hdcd : dc - d1.val = (dc - d.val) + 1 := by
          rw [hdd, Nat.sub_add_eq]
          exact (Nat.sub_add_cancel (Nat.sub_pos_of_lt hd1lt)).symm
        rw [hT3, hT2, hT, hcol, hkw, hdcd, Finset.sum_range_succ', Finset.smul_sum]
        rw [mul_zero, pow_zero, one_smul, add_zero]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, ← pow_add, hdd, show w.val + w.val * j = w.val * (j + 1) by ring,
          show d1.val + 1 + j = d1.val + (j + 1) by ring]
    · simp only [hpos, ite_false, WP.spec_ok]
      have h0 : d.val = 0 := by scalar_tac
      refine ⟨by rw [htn, h0]; exact eq_comm, fun T hT => ?_⟩
      obtain ⟨hTon, hTb, hT'⟩ := hts T hT
      refine ⟨hTon, hTb, ?_⟩
      rw [hT', h0, Nat.sub_zero]
      exact Finset.sum_congr rfl fun j _ => by rw [zero_add]
  · exact ⟨hok, hdi, hnone, hsome⟩

/-- The pairs collected by `scalars_points`, up to `m`: digits of `ss[j]` and the projective Niels
form of the point `ops[j] = some P`. -/
private def PairsOK (w : ℕ) (ss : List scalar.Scalar)
    (ops : List (Option edwards.EdwardsPoint.«i686-no-tables»))
    (v : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-no-tables»)) (m : ℕ) :
        Prop :=
  v.length = m ∧ ∀ j < m, ∃ P, ops[j]! = some P ∧
    (v.val[j]!).2.OnCurve ∧ (v.val[j]!).2.LimbsLt 27 ∧ (v.val[j]!).2.toPoint = P.toPoint ∧
    (v.val[j]!).1.asInt w = ss[j]!.asNat ∧
    (∀ i < 64, -2 ^ w ≤ 2 * (v.val[j]!).1[i]!.val ∧ 2 * (v.val[j]!).1[i]!.val ≤ 2 ^ w) ∧
    ∀ i < 64, 256 < i * w → (v.val[j]!).1[i]!.val = 0

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

namespace «VartimeMultiscalarMulPippengerEdwardsPointi686-no-tables».optional_multiscalar_mul

open Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

/-- The loop of `scalars_points`: the digits of each scalar with the next point, until the
scalars or the points run out; `none` at the first `none` point. -/
@[local step]
private theorem scalars_points_loop_spec {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It
        (Option edwards.EdwardsPoint.«i686-no-tables»))
    (scalars : Slice S) (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) scalars.val ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (w : Usize) (hw : 4 ≤ w.val ∧ w.val ≤ 8)
    (ops : List (Option edwards.EdwardsPoint.«i686-no-tables»))
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve) (points : It) (k : Usize)
    (hit : iterInst.Yields points (ops.drop k.val)) (hk : k.val ≤ ss.length)
    (hkops : k.val ≤ ops.length)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-no-tables»))
    (hout : PairsOK w.val ss ops out k.val) :
    scalars_points_loop borrowInst iterInst scalars points w out k
      ⦃ (r : Option (alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-no-tables»)))
          =>
        (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ v, r = some v → PairsOK w.val ss ops v (min ss.length ops.length) ⦄ := by
  have hslen : scalars.val.length = ss.length := hborrow.length_eq
  have hsb : ∀ k (hk : k < scalars.val.length),
      borrowInst.borrow scalars.val[k] ⦃ (s' : scalar.Scalar) => s' = ss[k]! ⦄ := fun k hk => by
    rw [getElem!_pos ss k (hslen ▸ hk)]
    exact (List.forall₂_iff_get.mp hborrow).2 k hk _
  unfold scalars_points_loop
  apply loop.spec_decr_nat (measure := fun (_, _, k') => ss.length - k'.val)
    (inv := fun (it, o, k') => iterInst.Yields it (ops.drop k'.val) ∧ k'.val ≤ ss.length ∧
      k'.val ≤ ops.length ∧ PairsOK w.val ss ops o k'.val)
  · rintro ⟨it, o, k'⟩ ⟨hit', hk', hko, hpo⟩
    unfold scalars_points_loop.body
    by_cases hlt : k'.val < ss.length
    · have hlt' : k' < Slice.len scalars := by scalar_tac
      simp only [hlt', ite_true]
      step as ⟨t, ht⟩
      subst ht
      step with hsb k'.val (by scalar_tac) as ⟨s, hs⟩
      have hs' : s.asNat < 2 ^ 255 := hs ▸ hss _
          (by rw [getElem!_pos ss _ hlt]; exact List.getElem_mem _)
      step with scalar.Scalar.as_radix_2w_spec s w hw hs' as ⟨d, hdv, hdlow, hdall, hdz⟩
      generalize hrest : ops.drop k'.val = rest at hit'
      cases hit' with
      | nil hnext =>
        step with hnext as ⟨o', it1, hq⟩
        subst hq
        dsimp only
        rw [WP.spec_ok]
        have hko' : k'.val = ops.length := by
          have := congrArg List.length hrest
          simp at this; scalar_tac
        refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun v hv => ?_⟩
        · rw [List.take_of_length_le (by scalar_tac)] at h
          obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem h
          obtain ⟨P, hP, -⟩ := hpo.2 j (by scalar_tac)
          rw [getElem!_pos ops j hj, hjn] at hP
          cases hP
        · obtain rfl := Option.some.inj hv
          rwa [show min ss.length ops.length = k'.val by scalar_tac]
      | @cons it it' x xs' hnext hrest' =>
        step with hnext as ⟨o', it1, ho, hit1⟩
        subst ho hit1
        have hk'o : k'.val < ops.length := by
          by_contra hcon
          rw [List.drop_eq_nil_of_le (by scalar_tac)] at hrest
          cases hrest
        have hx : ops[k'.val]! = x := by
          rw [getElem!_pos ops k'.val hk'o]
          have := List.drop_eq_getElem_cons hk'o
          rw [hrest] at this
          exact (List.cons.inj this).1.symm
        have hxs : xs' = ops.drop (k'.val + 1) := by
          have := List.drop_eq_getElem_cons hk'o
          rw [hrest] at this
          exact (List.cons.inj this).2
        rcases x with _ | P
        · dsimp only
          rw [WP.spec_ok]
          refine ⟨⟨fun _ => ?_, fun _ => rfl⟩, fun v hv => by cases hv⟩
          rw [← hx]
          exact List.mem_take_iff_getElem.mpr ⟨k'.val, by simp only [lt_min_iff]; scalar_tac, by
            rw [getElem!_pos ops k'.val hk'o]⟩
        · have hPmem : some P ∈ ops := by
            rw [← hx, getElem!_pos ops k'.val hk'o]; exact List.getElem_mem _
          obtain ⟨hPb, hPon⟩ := hps P hPmem
          step with edwards.«EdwardsPointi686-no-tables».as_projective_niels_spec_point P hPb hPon
            as ⟨pnp, hpon, hpp, hpb⟩
          step with alloc.vec.Vec.push_spec o (d, pnp) (by
            have := hpo.1; have := alloc.vec.Vec.len_ineq o; scalar_tac) as ⟨o1, ho1⟩
          step as ⟨k1, hk1⟩
          have hk1v : k1.val = k'.val + 1 := by scalar_tac
          refine ⟨by rw [hk1v, ← hxs]; exact hrest', by scalar_tac, by scalar_tac,
            ⟨by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hpo.1, hk1v], fun j hj => ?_⟩,
            by scalar_tac⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp (hk1v ▸ hj) with hj' | rfl
          · have hjo : j < o.length := hpo.1 ▸ hj'
            rw [show o1.val[j]! = o1[j]! from rfl,
              alloc.vec.Vec.getElem!_of_val_eq_append_of_lt ho1 hjo]
            exact hpo.2 j hj'
          · have := alloc.vec.Vec.getElem!_of_val_eq_append_length ho1
            rw [hpo.1] at this
            rw [show o1.val[k'.val]! = o1[k'.val]! from rfl, this]
            exact ⟨P, hx, hpon, hpb, hpp, by rw [hdv, hs], hdall, hdz⟩
    · have hge : ¬ k' < Slice.len scalars := by scalar_tac
      simp only [hge, ite_false, WP.spec_ok]
      have hks : k'.val = ss.length := by scalar_tac
      refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun v hv => ?_⟩
      · obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem h
        simp only [List.length_take] at hj
        obtain ⟨P, hP, -⟩ := hpo.2 j (by scalar_tac)
        rw [getElem!_pos ops j (by scalar_tac), ← List.getElem_take (j := ss.length)] at hP
        · rw [hjn] at hP; cases hP
        · rw [List.length_take]; exact hj
      · obtain rfl := Option.some.inj hv
        rwa [show min ss.length ops.length = k'.val by scalar_tac]
  · exact ⟨hit, hk, hkops, hout⟩

end «VartimeMultiscalarMulPippengerEdwardsPointi686-no-tables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

open «VartimeMultiscalarMulPippengerEdwardsPointi686-no-tables» in
/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^26`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«i686-no-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«i686-no-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-no-tables») =>
          (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold optional_multiscalar_mul.collect optional_multiscalar_mul.collect_loop
  apply spec_bind (collect.collectLoop_spec _ it xs hit (alloc.vec.Vec.new _) (by simpa using hxs))
  intro vs hvs
  replace hvs : vs.val = xs := by rw [hvs]; rfl
  apply spec_bind (Pₘ := fun (w : Usize) => 6 ≤ w.val ∧ w.val ≤ 8)
  · split_ifs <;> rw [WP.spec_ok] <;> decide
  intro w hw
  have hw256 : 2 ^ w.val ≤ 256 := Nat.pow_le_pow_right (by norm_num) hw.2
  step with Usize.ShiftLeft_spec 1#usize w (by
      rcases System.Platform.numBits_eq with h | h <;> simp only [h] <;> scalar_tac)
    as ⟨md, hmd, hmdbv⟩
  have hmd' : md.val = 2 ^ w.val := by
    rw [hmd, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  step with scalar.Scalar.to_radix_2w_size_hint_spec w ⟨by scalar_tac, hw.2⟩ as
      ⟨dc, hdc4, hdc5, hdc6, hdc7, hdc8⟩
  step as ⟨bc, hbc⟩
  have hbc' : 2 * bc.val = 2 ^ w.val := by
    rw [hbc, hmd']
    exact Nat.mul_div_cancel' (dvd_pow_self 2 (by scalar_tac))
  have hbc8 : bc.val ≤ 128 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hw.2; scalar_tac
  have hbc1 : 1 ≤ bc.val := by
    have := Nat.one_le_two_pow (n := w.val); scalar_tac
  have hdcw : dc.val ≤ 64 ∧ ∀ i, dc.val ≤ i → 256 < i * w.val := by
    rcases (show w.val = 6 ∨ w.val = 7 ∨ w.val = 8 by scalar_tac) with h | h | h
    · rw [hdc6 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
    · rw [hdc7 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
    · rw [hdc8 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
  have hdc0 : dc.val ≠ 0 := by
    rcases (show w.val = 6 ∨ w.val = 7 ∨ w.val = 8 by scalar_tac) with h | h | h
    · rw [hdc6 h]; decide
    · rw [hdc7 h]; decide
    · rw [hdc8 h]; decide
  step with hpoints' as ⟨it1, hit1⟩
  step with optional_multiscalar_mul.scalars_points_loop_spec
    _ _ _ ss (by rw [show (alloc.vec.Vec.deref vs).val = vs.val from Slice.from_val _ _, hvs]; exact
        hborrow_scalars) hss w
    ⟨by scalar_tac, hw.2⟩ ops hps it1 0#usize (by simpa using hit1) (Nat.zero_le _) (Nat.zero_le _)
    (alloc.vec.Vec.new _) ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    as ⟨o, hnone, hsome⟩
  rcases o with _ | sp
  · dsimp only
    rw [WP.spec_ok]
    exact ⟨by simpa using hnone, fun R hR => by cases hR⟩
  · have hnn : none ∉ ops.take ss.length := fun h => by cases hnone.mpr h
    obtain ⟨hsplen, hsp⟩ := hsome sp rfl
    let P : ℕ → curve25519.edwards.Point := fun k => ((ops[k]!).getD default).toPoint
    have hsp' : ∀ k < sp.length, (sp.val[k]!).2.OnCurve ∧ (sp.val[k]!).2.LimbsLt 27 ∧
        (sp.val[k]!).2.toPoint = P k := fun k hk => by
      obtain ⟨Q, hQ, hon, hb, hp, -⟩ := hsp k (hsplen ▸ hk)
      exact ⟨hon, hb, by rw [hp]; change Q.toPoint = ((ops[k]!).getD default).toPoint; rw [hQ]; rfl⟩
    have hdig : ∀ k < sp.length, ∀ e < 64, -(bc.val : ℤ) ≤ (sp.val[k]!).1[e]!.val ∧
        (sp.val[k]!).1[e]!.val ≤ (bc.val : ℤ) := fun k hk e he => by
      obtain ⟨Q, -, -, -, -, -, hb, -⟩ := hsp k (hsplen ▸ hk)
      have := hb e he
      have hbz : (2 : ℤ) ^ w.val = 2 * bc.val := by exact_mod_cast hbc'.symm
      rw [hbz] at this
      constructor <;> linarith [this.1, this.2]
    step with optional_multiscalar_mul_loop0_spec bc (alloc.vec.Vec.new _) 0#usize hbc8
      (Nat.zero_le _) rfl (fun j hj => absurd hj (Nat.not_lt_zero j)) as ⟨b, hb⟩
    step with optional_multiscalar_mul_loop1_spec w bc sp b none dc P dc.val
      ⟨by scalar_tac, hw.2⟩ hbc1 hbc8 hdcw.1 hsp' hdig hb (le_refl _) ⟨fun _ => rfl, fun _ => rfl⟩
      (fun T hT => by cases hT) as ⟨t, htn, hts⟩
    rcases t with _ | T
    · exact absurd (htn.mp rfl) hdc0
    obtain ⟨hTon, hTb, hT⟩ := hts T rfl
    step with core.option.Option.expect.spec as ⟨R, hR⟩
    obtain rfl : T = R := Option.some.inj hR
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : T = R' := Option.some.inj hR'
    refine ⟨hTon, ?_, hTb⟩
    unfold column at hT
    rw [hT, sum_zipWith_filterMap _ _ _ hnn, ← hsplen, sum_columns]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    obtain ⟨Q, hQ, -, -, -, hval, -, hz⟩ := hsp k (hsplen ▸ hk')
    rw [sum_digits _ _ _ hdcw.1 fun j hj hj' => hz j hj (hdcw.2 j hj'), hval, natCast_zsmul]

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

end

end Curve25519Dalek.backend.serial.scalar_mul.pippenger
