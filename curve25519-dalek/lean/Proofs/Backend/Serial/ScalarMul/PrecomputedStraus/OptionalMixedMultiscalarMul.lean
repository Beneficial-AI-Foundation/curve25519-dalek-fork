/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
public import Defs.ScalarMul
import Proofs.Backend.Serial.CurveModels.AddAffineNiels
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.CompletedAsProjective
import Proofs.Backend.Serial.CurveModels.ProjectiveAsExtended
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Backend.Serial.CurveModels.ProjectiveIdentity
import Proofs.Backend.Serial.CurveModels.SubAffineNiels
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.NonAdjacentForm
import Proofs.Window.NafLookupTable5From
import Proofs.Window.NafLookupTable5Select
import Proofs.Window.NafLookupTable8Select
public section

/-! # `VartimePrecomputedStraus::optional_mixed_multiscalar_mul`

Variable-time Straus with precomputed tables for the static points: width-`8` non-adjacent forms
of the static scalars against the precomputed `NafLookupTable8`s, width-`5` ones of the dynamic
scalars against tables of the dynamic points built on the fly (`None` at the first `None` point),
Horner's rule in base `2` over the `256` digit positions. Missing static scalars count as `0`;
the patched code asserts `|static scalars| ≤ |static points|` and, after the `None` check,
`|dynamic scalars| = |dynamic points|`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

/-- For `ps[m]!` on the static points. -/
private noncomputable instance instInhabitedPoint : Inhabited curve25519.edwards.Point := ⟨0⟩

/-- `Forall₂` as a statement about the entries `getElem!`. -/
private theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    l₁.length = l₂.length ∧ ∀ k < l₁.length, R l₁[k]! l₂[k]! := by
  refine ⟨h.length_eq, fun k hk => ?_⟩
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (h.length_eq ▸ hk)]
  exact (List.forall₂_iff_get.mp h).2 k hk _

/-- Filtering out the `none`s of a list without `none` keeps its length. -/
private theorem length_filterMap_id {β : Type} (l : List (Option β)) (h : none ∉ l) :
    (l.filterMap id).length = l.length := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    rcases o with _ | b
    · simp at h
    · rw [List.filterMap_cons_some (by rfl), List.length_cons, List.length_cons,
        ih (by simpa using h)]

/-- One step of Horner's rule in base `2` for the dynamic and the static points together. -/
private theorem horner2_two (a b e : ℕ) (d f : ℕ → Array I8 256#usize)
    (P Q : ℕ → curve25519.edwards.Point) (he : e < 256) :
    2 • ((∑ k ∈ Finset.range a, nafTail (d k) (e + 1) • P k) +
        ∑ k ∈ Finset.range b, nafTail (f k) (e + 1) • Q k) +
      ∑ k ∈ Finset.range a, (d k)[e]!.val • P k + ∑ k ∈ Finset.range b, (f k)[e]!.val • Q k =
      (∑ k ∈ Finset.range a, nafTail (d k) e • P k) + ∑ k ∈ Finset.range b, nafTail (f k) e • Q k :=
          by
  rw [← horner2 a e d P he, ← horner2 b e f Q he, smul_add]
  abel

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
    (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
    (sub_spec_point)

set_option linter.style.longLine false
namespace «VartimePrecomputedMultiscalarMulVartimePrecomputedStrausx86_64-tablesEdwardsPointx86_64-tables»
set_option linter.style.longLine true
namespace optional_mixed_multiscalar_mul

/-- The scalars' width-`w` non-adjacent forms. -/
@[local step]
private theorem nafs_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) (w : Usize)
    (hw : 2 ≤ w.val ∧ w.val ≤ 8) :
    nafs iterInst borrowInst scalars w
      ⦃ (r : alloc.vec.Vec (Array I8 256#usize)) =>
        List.Forall₂ (fun s d => d.asInt 1 = s.asNat ∧ ∀ i < 256, d[i]!.val ≠ 0 →
          d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ w.val) ss r.val ⦄ := by
  unfold nafs nafs_loop
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    (fun s => scalar.Scalar.non_adjacent_form s w)
    (fun s d => d.asInt 1 = s.asNat ∧ ∀ i < 256, d[i]!.val ≠ 0 →
      d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ w.val)
    scalars xs hit ss hborrow (fun s hs =>
      spec_mono (scalar.Scalar.non_adjacent_form_spec s w hw (hss s hs))
        fun d ⟨hval, hdig, _⟩ => ⟨hval, hdig⟩) (alloc.vec.Vec.new _) (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

open window.«NafLookupTable5ProjectiveNielsPointx86_64-tables».Insts in
/-- The loop of `lookup_tables`: pushes the tables of the remaining points; `none` iff one of
them is `none`. -/
private theorem lookup_tables_loop_spec {It : Type}
    (iterInst : core.iter.traits.iterator.Iterator It (Option edwards.EdwardsPoint.«x86_64-tables»))
    (points : It) (ops : List (Option edwards.EdwardsPoint.«x86_64-tables»))
    (hit : iterInst.Yields points ops)
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (out : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»))
    (hlen : out.length + ops.length ≤ Usize.max) :
    lookup_tables_loop iterInst points out
      ⦃ (r : Option (alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»)))
          =>
        (r = none ↔ none ∈ ops) ∧ ∀ v, r = some v → ∃ zs, v.val = out.val ++ zs ∧
          List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) (ops.filterMap id)
            zs ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold lookup_tables_loop loop lookup_tables_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' x xs' hnext _ ih =>
    unfold lookup_tables_loop loop lookup_tables_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    rcases x with _ | P
    · simp
    · obtain ⟨hPb, hPon⟩ := hps P List.mem_cons_self
      step with «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec
        P hPb hPon as ⟨z, hz, hzb⟩
      step with alloc.vec.Vec.push_spec out z
        (by
          have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
          exact h) as ⟨out1, hout1⟩
      have ih' := ih (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ)) out1 (by
        rw [alloc.vec.Vec.length_of_val_eq_append hout1]
        simp only [List.length_cons] at hlen; omega)
      unfold lookup_tables_loop at ih'
      apply WP.spec_mono ih'
      rintro r ⟨hnone, hsome⟩
      refine ⟨by simp [hnone], fun v hv => ?_⟩
      obtain ⟨zs, hr, hzs⟩ := hsome v hv
      exact ⟨z :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
        by simpa using List.Forall₂.cons ⟨hz, hzb⟩ hzs⟩

/-- The points' tables of odd multiples; `none` iff some point is `none`. -/
@[local step]
private theorem lookup_tables_spec {It : Type}
    (iterInst : core.iter.traits.iterator.Iterator It (Option edwards.EdwardsPoint.«x86_64-tables»))
    (points : It) (ops : List (Option edwards.EdwardsPoint.«x86_64-tables»))
    (hit : iterInst.Yields points ops)
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve) (hlen : ops.length ≤ Usize.max) :
    lookup_tables iterInst points
      ⦃ (r : Option (alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»)))
          =>
        (r = none ↔ none ∈ ops) ∧ ∀ v, r = some v →
          List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54)
            (ops.filterMap id) v.val ⦄ := by
  unfold lookup_tables
  apply spec_mono (lookup_tables_loop_spec iterInst points ops hit hps (alloc.vec.Vec.new _)
    (by simpa using hlen))
  rintro r ⟨hnone, hsome⟩
  refine ⟨hnone, fun v hv => ?_⟩
  obtain ⟨zs, hr, hzs⟩ := hsome v hv
  simpa [hr] using hzs

end optional_mixed_multiscalar_mul
end «VartimePrecomputedMultiscalarMulVartimePrecomputedStrausx86_64-tablesEdwardsPointx86_64-tables»

namespace VartimePrecomputedStraus.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

set_option linter.style.longLine false
open «VartimePrecomputedMultiscalarMulVartimePrecomputedStrausx86_64-tablesEdwardsPointx86_64-tables»
set_option linter.style.longLine true

open scoped Helpers.IndexStep in
/-- The loop0_loop0 loop over the points `i ∈ [k, n)`: adds `d_i[j] • P_i`. -/
@[local step]
private theorem optional_mixed_multiscalar_mul_loop0_loop0_spec (iter : core.ops.range.Range Usize)
    (dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec
        (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»))
    (j : Usize) (R : CompletedPoint.«x86_64-tables») (P : ℕ → curve25519.edwards.Point)
    (hj : j.val < 256)
        (hn : iter.end.val ≤ dynamic_nafs.length ∧ iter.end.val ≤ dynamic_lookup_tables.length)
    (hT : ∀ m < iter.end.val, dynamic_lookup_tables.val[m]!.Represents (P m) ∧
        dynamic_lookup_tables.val[m]!.LimbsLt 54)
    (hD : ∀ m < iter.end.val, ∀ e < 256, (dynamic_nafs.val[m]!)[e]!.val ≠ 0 →
      (dynamic_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(dynamic_nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hk : iter.start.val ≤ iter.end.val) (hR : R.OnCurve) (hRb : R.LimbsLt 54) :
    optional_mixed_multiscalar_mul_loop0_loop0 iter dynamic_nafs dynamic_lookup_tables j R
      ⦃ (r : CompletedPoint.«x86_64-tables») => r.OnCurve ∧ r.LimbsLt 54 ∧
        r.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val iter.end.val,
          (dynamic_nafs.val[m]!)[j.val]!.val • P m ⦄ := by
  unfold optional_mixed_multiscalar_mul_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, R') => it.end = iter.end ∧ iter.start.val ≤ it.start.val ∧
      it.start.val ≤ iter.end.val ∧ R'.OnCurve ∧ R'.LimbsLt 54 ∧
      R'.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val it.start.val,
        (dynamic_nafs.val[m]!)[j.val]!.val • P m)
  · rintro ⟨it, R'⟩ ⟨hend, hst, hle, hR'on, hR'b, hR'p⟩
    unfold optional_mixed_multiscalar_mul_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      have hm : it.start.val < iter.end.val := hend ▸ hlt
      obtain ⟨hrep, hb⟩ := hT it.start.val hm
      step as ⟨a, ha⟩
      rw [← getElem!_pos] at ha
      step as ⟨d, hd⟩
      have hstep : ∀ R1 : CompletedPoint.«x86_64-tables», R1.OnCurve → R1.LimbsLt 54 →
          R1.toPoint = R'.toPoint + d.val • P it.start.val →
          it1.end = iter.end ∧ iter.start.val ≤ it1.start.val ∧ it1.start.val ≤ iter.end.val ∧
          R1.OnCurve ∧ R1.LimbsLt 54 ∧
          R1.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val it1.start.val,
            (dynamic_nafs.val[m]!)[j.val]!.val • P m ∧
          it1.end.val - it1.start.val < it.end.val - it.start.val := by
        intro R1 h1on h1b h1p
        refine ⟨hend1.trans hend, by scalar_tac, by scalar_tac, h1on, h1b, ?_, by scalar_tac⟩
        rw [h1p, hR'p, hstart1, Finset.sum_Ico_succ_top hst, add_assoc, hd, ha]
      rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
      rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 5) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_neg hneg] at hdk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable5.select_spec (P := P it.start.val) _ tab i2
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with sub_spec_point ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show ProjectiveNielsPoint.«x86_64-tables».toPoint q = PointRepr.toPoint q from
            rfl, hq]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        exact hstep R' hR'on hR'b (by rw [hzero, zero_smul, add_zero])
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 5) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_pos hpos] at hdk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable5.select_spec (P := P it.start.val) _ tab i1
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with add_spec_point ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show ProjectiveNielsPoint.«x86_64-tables».toPoint q = PointRepr.toPoint q from
            rfl, hq]
        exact add_nsmul_eq _ _ _ _ (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : it.start.val = iter.end.val := by rw [← hend]; scalar_tac
      exact ⟨hR'on, hR'b, this ▸ hR'p⟩
  · exact ⟨rfl, le_refl _, hk, hR, hRb, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

open «CoreOpsArithAddSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables» in
open «CoreOpsArithSubSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables» in
open scoped Helpers.IndexStep in
/-- The loop0_loop1 loop over the points `i ∈ [k, n)`: adds `d_i[j] • P_i`. -/
@[local step]
private theorem optional_mixed_multiscalar_mul_loop0_loop1_spec (iter : core.ops.range.Range Usize)
    (static_nafs : alloc.vec.Vec (Array I8 256#usize))
    (v : alloc.vec.Vec (window.NafLookupTable8 AffineNielsPoint.«x86_64-tables»))
    (j : Usize) (R : CompletedPoint.«x86_64-tables») (P : ℕ → curve25519.edwards.Point)
    (hj : j.val < 256) (hn : iter.end.val ≤ static_nafs.length ∧ iter.end.val ≤ v.length)
    (hT : ∀ m < iter.end.val, v.val[m]!.Represents (P m) ∧ v.val[m]!.LimbsLt 54)
    (hD : ∀ m < iter.end.val, ∀ e < 256, (static_nafs.val[m]!)[e]!.val ≠ 0 →
      (static_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(static_nafs.val[m]!)[e]!.val| < 2 ^ 8)
    (hk : iter.start.val ≤ iter.end.val) (hR : R.OnCurve) (hRb : R.LimbsLt 54) :
    optional_mixed_multiscalar_mul_loop0_loop1 iter v static_nafs j R
      ⦃ (r : CompletedPoint.«x86_64-tables») => r.OnCurve ∧ r.LimbsLt 54 ∧
        r.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val iter.end.val,
          (static_nafs.val[m]!)[j.val]!.val • P m ⦄ := by
  unfold optional_mixed_multiscalar_mul_loop0_loop1
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, R') => it.end = iter.end ∧ iter.start.val ≤ it.start.val ∧
      it.start.val ≤ iter.end.val ∧ R'.OnCurve ∧ R'.LimbsLt 54 ∧
      R'.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val it.start.val,
        (static_nafs.val[m]!)[j.val]!.val • P m)
  · rintro ⟨it, R'⟩ ⟨hend, hst, hle, hR'on, hR'b, hR'p⟩
    unfold optional_mixed_multiscalar_mul_loop0_loop1.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      have hm : it.start.val < iter.end.val := hend ▸ hlt
      obtain ⟨hrep, hb⟩ := hT it.start.val hm
      step as ⟨a, ha⟩
      rw [← getElem!_pos] at ha
      step as ⟨d, hd⟩
      have hstep : ∀ R1 : CompletedPoint.«x86_64-tables», R1.OnCurve → R1.LimbsLt 54 →
          R1.toPoint = R'.toPoint + d.val • P it.start.val →
          it1.end = iter.end ∧ iter.start.val ≤ it1.start.val ∧ it1.start.val ≤ iter.end.val ∧
          R1.OnCurve ∧ R1.LimbsLt 54 ∧
          R1.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val it1.start.val,
            (static_nafs.val[m]!)[j.val]!.val • P m ∧
          it1.end.val - it1.start.val < it.end.val - it.start.val := by
        intro R1 h1on h1b h1p
        refine ⟨hend1.trans hend, by scalar_tac, by scalar_tac, h1on, h1b, ?_, by scalar_tac⟩
        rw [h1p, hR'p, hstart1, Finset.sum_Ico_succ_top hst, add_assoc, hd, ha]
      rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
      rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 8) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_neg hneg] at hdk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable8.select_spec (P := P it.start.val) _ tab i2
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with sub_spec_point
            ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show AffineNielsPoint.«x86_64-tables».toPoint q = PointRepr.toPoint q from
            rfl, hq]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        exact hstep R' hR'on hR'b (by rw [hzero, zero_smul, add_zero])
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 8) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_pos hpos] at hdk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable8.select_spec (P := P it.start.val) _ tab i1
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with add_spec_point
            ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show AffineNielsPoint.«x86_64-tables».toPoint q = PointRepr.toPoint q from
            rfl, hq]
        exact add_nsmul_eq _ _ _ _ (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : it.start.val = iter.end.val := by rw [← hend]; scalar_tac
      exact ⟨hR'on, hR'b, this ▸ hR'p⟩
  · exact ⟨rfl, le_refl _, hk, hR, hRb, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The outer loop over the digit positions, from the top. -/
@[local step]
private theorem optional_mixed_multiscalar_mul_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (v : alloc.vec.Vec (window.NafLookupTable8 AffineNielsPoint.«x86_64-tables»))
    (static_nafs dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec
        (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»))
    (dp : Usize) (S : ProjectivePoint.«x86_64-tables») (P Q : ℕ → curve25519.edwards.Point)
    (hdp : dp.val ≤ dynamic_nafs.length ∧ dp.val ≤ dynamic_lookup_tables.length)
    (hsl : static_nafs.length ≤ v.length)
    (hT : ∀ m < dp.val, dynamic_lookup_tables.val[m]!.Represents (Q m) ∧
      dynamic_lookup_tables.val[m]!.LimbsLt 54)
    (hD : ∀ m < dp.val, ∀ e < 256, (dynamic_nafs.val[m]!)[e]!.val ≠ 0 →
      (dynamic_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(dynamic_nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hV : ∀ m < static_nafs.length, v.val[m]!.Represents (P m) ∧ v.val[m]!.LimbsLt 54)
    (hE : ∀ m < static_nafs.length, ∀ e < 256, (static_nafs.val[m]!)[e]!.val ≠ 0 →
      (static_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(static_nafs.val[m]!)[e]!.val| < 2 ^ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hS : S.OnCurve) (hSb : S.LimbsLt 52)
    (hSp : S.toPoint =
      (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! iter.iter.end.val • Q m) +
        ∑ m ∈ Finset.range static_nafs.length,
          nafTail static_nafs.val[m]! iter.iter.end.val • P m) :
    optional_mixed_multiscalar_mul_loop0 iter v static_nafs dynamic_nafs dynamic_lookup_tables dp S
      ⦃ (r : ProjectivePoint.«x86_64-tables») => r.OnCurve ∧ r.LimbsLt 52 ∧ r.toPoint =
        (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! 0 • Q m) +
          ∑ m ∈ Finset.range static_nafs.length, nafTail static_nafs.val[m]! 0 • P m ⦄ := by
  unfold optional_mixed_multiscalar_mul_loop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, q) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ q.OnCurve ∧
      q.LimbsLt 52 ∧ q.toPoint =
        (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! it.iter.end.val • Q m) +
          ∑ m ∈ Finset.range static_nafs.length,
            nafTail static_nafs.val[m]! it.iter.end.val • P m)
  · rintro ⟨it, q⟩ ⟨hst, hen, hqon, hqb, hqp⟩
    unfold optional_mixed_multiscalar_mul_loop0.body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, j, ho, hj, hstart1, hend1⟩
      subst ho
      have hj256 : j.val < 256 := by scalar_tac
      step with «ProjectivePointx86_64-tables».double_spec_point as ⟨R, hRon, hRp, hRb⟩
      step with optional_mixed_multiscalar_mul_loop0_loop0_spec
        { start := 0#usize, «end» := dp } dynamic_nafs dynamic_lookup_tables j R Q hj256 hdp hT hD
        (Nat.zero_le _) hRon hRb as ⟨R1, hR1on, hR1b, hR1⟩
      step with optional_mixed_multiscalar_mul_loop0_loop1_spec
        { start := 0#usize, «end» := alloc.vec.Vec.len static_nafs } static_nafs v j R1 P hj256
        ⟨by simp, by simpa using hsl⟩ (by simpa using hV) (by simpa using hE) (Nat.zero_le _)
        hR1on hR1b as ⟨R2, hR2on, hR2b, hR2⟩
      step with «CompletedPointx86_64-tables».as_projective_spec_point as ⟨q1, hq1on, hq1, hq1b⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, hq1on, hq1b, ?_, by scalar_tac⟩
      simp only [alloc.vec.Vec.len_val] at hR1 hR2
      rw [hq1, hR2, hR1, hRp, hqp, ← Finset.range_eq_Ico, ← Finset.range_eq_Ico, hend1, ← hj,
        add_assoc, ← add_assoc (2 • _),
        horner2_two dp.val static_nafs.length j.val (fun k => dynamic_nafs.val[k]!)
          (fun k => static_nafs.val[k]!) Q P hj256]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at hqp
      exact ⟨hqon, hqb, hqp⟩
  · exact ⟨hstart, hend, hS, hSb, hSp⟩

/-- `VartimePrecomputedStraus::optional_mixed_multiscalar_mul`: for a precomputation of the
static points `ps`, `none` iff some dynamic point is `none`; otherwise
`∑ s_i • ps_i + ∑ d_i • Q_i` over the static scalars (at most `|ps|`, the missing ones count as
`0`) and the dynamic scalars and points (as many scalars as points); unreduced scalars
`< 2^255`; limbs `< 2^52`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«x86_64-tables») Clause4_IntoIter)
    (self : VartimePrecomputedStraus.«x86_64-tables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (ps : List curve25519.edwards.Point) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«x86_64-tables»))
    (hself : self.Represents ps) (hself_b : self.LimbsLt 54)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52 ∧ Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : ss.length ≤ ps.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss ps).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold optional_mixed_multiscalar_mul
  have h1 : staticScalarsInst.into_iter static_scalars
      ⦃ (it : Clause0_IntoIter) => staticScalarsInst.iteratorInst.Yields it xs ⦄ :=
    hstatic_scalars
  have h2 : dynamicScalarsInst.into_iter dynamic_scalars
      ⦃ (it : Clause2_IntoIter) => dynamicScalarsInst.iteratorInst.Yields it ys ⦄ :=
    hdynamic_scalars
  have h3 : dynamicPointsInst.into_iter dynamic_points
      ⦃ (it : Clause4_IntoIter) => dynamicPointsInst.iteratorInst.Yields it qops ⦄ :=
    hdynamic_points
  step with h1 as ⟨it, hit⟩
  step with optional_mixed_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_static hss hxs 8#usize (by decide) as ⟨sn, hsn⟩
  step with h2 as ⟨it1, hit1⟩
  step with optional_mixed_multiscalar_mul.nafs_spec
    _ _ it1 ys hit1 ds hborrow_dynamic hds hys 5#usize (by decide) as ⟨dn, hdn⟩
  step with h3 as ⟨it2, hit2⟩
  step with optional_mixed_multiscalar_mul.lookup_tables_spec
    _ it2 qops hit2 hqs hqops as ⟨o, hnone, hsome⟩
  rcases o with _ | dtabs
  · dsimp only
    rw [WP.spec_ok]
    exact ⟨by simpa using hnone, fun R hR => by cases hR⟩
  · have hnn : none ∉ qops := fun h => by cases hnone.mpr h
    obtain ⟨hTlen, hT⟩ := forall₂_getElem! (hsome dtabs rfl)
    obtain ⟨hDlen, hD⟩ := forall₂_getElem! hdn
    obtain ⟨hSlen, hS⟩ := forall₂_getElem! hsn
    obtain ⟨hVlen, hV⟩ := forall₂_getElem! hself
    have hfl := length_filterMap_id qops hnn
    have hdq := hdynamic hnn
    step
    step
    step with
        ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
      as ⟨S0, hS0on, hS0, hS0b⟩
    step as ⟨iter, hiter⟩
    step with optional_mixed_multiscalar_mul_loop0_spec iter self.static_lookup_tables sn dn dtabs
      (alloc.vec.Vec.len dtabs) S0 (fun m => ps[m]!) (fun m => ((qops.filterMap id)[m]!).toPoint)
      ⟨by scalar_tac, by scalar_tac⟩ (by scalar_tac)
      (fun m hm => hT m (by scalar_tac))
      (fun m hm => (hD m (by scalar_tac)).2)
      (fun m hm => ⟨hV m (by scalar_tac),
        hself_b _ (by rw [getElem!_pos _ m (by scalar_tac)]; exact List.getElem_mem _)⟩)
      (fun m hm => (hS m (by scalar_tac)).2)
      (by rw [hiter]; rfl) (by rw [hiter]; decide) hS0on hS0b
      (by
        have he : iter.iter.end.val = 256 := by rw [hiter]; rfl
        rw [hS0, he]
        simp only [nafTail_eq_zero _ 256 fun j hj hj' => absurd hj' (Nat.not_lt.mpr hj),
          zero_smul, Finset.sum_const_zero, add_zero])
      as ⟨S1, hS1on, hS1b, hS1⟩
    step with «ProjectivePointx86_64-tables».as_extended_spec_point as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hS1, add_comm, sum_zipWith_eq, sum_zipWith_eq,
      show min ss.length ps.length = sn.val.length by
        rw [← hSlen]; exact Nat.min_eq_left hstatic,
      show min ds.length (qops.filterMap id).length = (alloc.vec.Vec.len dtabs).val by
        rw [alloc.vec.Vec.len_val, show dtabs.length = dtabs.val.length from rfl, ← hTlen, hfl,
          hdq, Nat.min_self]]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [nafTail_zero, (hS k (by rw [hSlen]; exact hk')).1, natCast_zsmul]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [nafTail_zero, (hD k (by scalar_tac)).1, natCast_zsmul]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end VartimePrecomputedStraus.«x86_64-tables».Insts

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    (sub_spec_point)

set_option linter.style.longLine false
namespace «VartimePrecomputedMultiscalarMulVartimePrecomputedStrausx86_64-no-tablesEdwardsPointx86_64-no-tables»
set_option linter.style.longLine true
namespace optional_mixed_multiscalar_mul

/-- The scalars' width-`w` non-adjacent forms. -/
@[local step]
private theorem nafs_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) (w : Usize)
    (hw : 2 ≤ w.val ∧ w.val ≤ 8) :
    nafs iterInst borrowInst scalars w
      ⦃ (r : alloc.vec.Vec (Array I8 256#usize)) =>
        List.Forall₂ (fun s d => d.asInt 1 = s.asNat ∧ ∀ i < 256, d[i]!.val ≠ 0 →
          d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ w.val) ss r.val ⦄ := by
  unfold nafs nafs_loop
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    (fun s => scalar.Scalar.non_adjacent_form s w)
    (fun s d => d.asInt 1 = s.asNat ∧ ∀ i < 256, d[i]!.val ≠ 0 →
      d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ w.val)
    scalars xs hit ss hborrow (fun s hs =>
      spec_mono (scalar.Scalar.non_adjacent_form_spec s w hw (hss s hs))
        fun d ⟨hval, hdig, _⟩ => ⟨hval, hdig⟩) (alloc.vec.Vec.new _) (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

open window.«NafLookupTable5ProjectiveNielsPointx86_64-no-tables».Insts in
/-- The loop of `lookup_tables`: pushes the tables of the remaining points; `none` iff one of
them is `none`. -/
private theorem lookup_tables_loop_spec {It : Type}
    (iterInst : core.iter.traits.iterator.Iterator It
        (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (points : It) (ops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (hit : iterInst.Yields points ops)
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (out : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»))
    (hlen : out.length + ops.length ≤ Usize.max) :
    lookup_tables_loop iterInst points out
      ⦃ (r : Option
          (alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»))) =>
        (r = none ↔ none ∈ ops) ∧ ∀ v, r = some v → ∃ zs, v.val = out.val ++ zs ∧
          List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) (ops.filterMap id)
            zs ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold lookup_tables_loop loop lookup_tables_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' x xs' hnext _ ih =>
    unfold lookup_tables_loop loop lookup_tables_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    rcases x with _ | P
    · simp
    · obtain ⟨hPb, hPon⟩ := hps P List.mem_cons_self
      step with «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from_spec
        P hPb hPon as ⟨z, hz, hzb⟩
      step with alloc.vec.Vec.push_spec out z
        (by
          have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
          exact h) as ⟨out1, hout1⟩
      have ih' := ih (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ)) out1 (by
        rw [alloc.vec.Vec.length_of_val_eq_append hout1]
        simp only [List.length_cons] at hlen; omega)
      unfold lookup_tables_loop at ih'
      apply WP.spec_mono ih'
      rintro r ⟨hnone, hsome⟩
      refine ⟨by simp [hnone], fun v hv => ?_⟩
      obtain ⟨zs, hr, hzs⟩ := hsome v hv
      exact ⟨z :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
        by simpa using List.Forall₂.cons ⟨hz, hzb⟩ hzs⟩

/-- The points' tables of odd multiples; `none` iff some point is `none`. -/
@[local step]
private theorem lookup_tables_spec {It : Type}
    (iterInst : core.iter.traits.iterator.Iterator It
        (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (points : It) (ops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (hit : iterInst.Yields points ops)
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve) (hlen : ops.length ≤ Usize.max) :
    lookup_tables iterInst points
      ⦃ (r : Option
          (alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»))) =>
        (r = none ↔ none ∈ ops) ∧ ∀ v, r = some v →
          List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54)
            (ops.filterMap id) v.val ⦄ := by
  unfold lookup_tables
  apply spec_mono (lookup_tables_loop_spec iterInst points ops hit hps (alloc.vec.Vec.new _)
    (by simpa using hlen))
  rintro r ⟨hnone, hsome⟩
  refine ⟨hnone, fun v hv => ?_⟩
  obtain ⟨zs, hr, hzs⟩ := hsome v hv
  simpa [hr] using hzs

end optional_mixed_multiscalar_mul
set_option linter.style.longLine false
end «VartimePrecomputedMultiscalarMulVartimePrecomputedStrausx86_64-no-tablesEdwardsPointx86_64-no-tables»
set_option linter.style.longLine true

namespace VartimePrecomputedStraus.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

set_option linter.style.longLine false
open «VartimePrecomputedMultiscalarMulVartimePrecomputedStrausx86_64-no-tablesEdwardsPointx86_64-no-tables»
set_option linter.style.longLine true

open scoped Helpers.IndexStep in
/-- The loop0_loop0 loop over the points `i ∈ [k, n)`: adds `d_i[j] • P_i`. -/
@[local step]
private theorem optional_mixed_multiscalar_mul_loop0_loop0_spec (iter : core.ops.range.Range Usize)
    (dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec
        (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»))
    (j : Usize) (R : CompletedPoint.«x86_64-no-tables») (P : ℕ → curve25519.edwards.Point)
    (hj : j.val < 256)
        (hn : iter.end.val ≤ dynamic_nafs.length ∧ iter.end.val ≤ dynamic_lookup_tables.length)
    (hT : ∀ m < iter.end.val, dynamic_lookup_tables.val[m]!.Represents (P m) ∧
        dynamic_lookup_tables.val[m]!.LimbsLt 54)
    (hD : ∀ m < iter.end.val, ∀ e < 256, (dynamic_nafs.val[m]!)[e]!.val ≠ 0 →
      (dynamic_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(dynamic_nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hk : iter.start.val ≤ iter.end.val) (hR : R.OnCurve) (hRb : R.LimbsLt 54) :
    optional_mixed_multiscalar_mul_loop0_loop0 iter dynamic_nafs dynamic_lookup_tables j R
      ⦃ (r : CompletedPoint.«x86_64-no-tables») => r.OnCurve ∧ r.LimbsLt 54 ∧
        r.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val iter.end.val,
          (dynamic_nafs.val[m]!)[j.val]!.val • P m ⦄ := by
  unfold optional_mixed_multiscalar_mul_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, R') => it.end = iter.end ∧ iter.start.val ≤ it.start.val ∧
      it.start.val ≤ iter.end.val ∧ R'.OnCurve ∧ R'.LimbsLt 54 ∧
      R'.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val it.start.val,
        (dynamic_nafs.val[m]!)[j.val]!.val • P m)
  · rintro ⟨it, R'⟩ ⟨hend, hst, hle, hR'on, hR'b, hR'p⟩
    unfold optional_mixed_multiscalar_mul_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      have hm : it.start.val < iter.end.val := hend ▸ hlt
      obtain ⟨hrep, hb⟩ := hT it.start.val hm
      step as ⟨a, ha⟩
      rw [← getElem!_pos] at ha
      step as ⟨d, hd⟩
      have hstep : ∀ R1 : CompletedPoint.«x86_64-no-tables», R1.OnCurve → R1.LimbsLt 54 →
          R1.toPoint = R'.toPoint + d.val • P it.start.val →
          it1.end = iter.end ∧ iter.start.val ≤ it1.start.val ∧ it1.start.val ≤ iter.end.val ∧
          R1.OnCurve ∧ R1.LimbsLt 54 ∧
          R1.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val it1.start.val,
            (dynamic_nafs.val[m]!)[j.val]!.val • P m ∧
          it1.end.val - it1.start.val < it.end.val - it.start.val := by
        intro R1 h1on h1b h1p
        refine ⟨hend1.trans hend, by scalar_tac, by scalar_tac, h1on, h1b, ?_, by scalar_tac⟩
        rw [h1p, hR'p, hstart1, Finset.sum_Ico_succ_top hst, add_assoc, hd, ha]
      rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
      rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 5) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_neg hneg] at hdk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable5.select_spec (P := P it.start.val) _ tab i2
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with sub_spec_point ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show ProjectiveNielsPoint.«x86_64-no-tables».toPoint q = PointRepr.toPoint q
            from rfl, hq]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        exact hstep R' hR'on hR'b (by rw [hzero, zero_smul, add_zero])
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 5) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_pos hpos] at hdk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable5.select_spec (P := P it.start.val) _ tab i1
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with add_spec_point ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show ProjectiveNielsPoint.«x86_64-no-tables».toPoint q = PointRepr.toPoint q
            from rfl, hq]
        exact add_nsmul_eq _ _ _ _ (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : it.start.val = iter.end.val := by rw [← hend]; scalar_tac
      exact ⟨hR'on, hR'b, this ▸ hR'p⟩
  · exact ⟨rfl, le_refl _, hk, hR, hRb, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

open «CoreOpsArithAddSharedAAffineNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables» in
open «CoreOpsArithSubSharedAAffineNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables» in
open scoped Helpers.IndexStep in
/-- The loop0_loop1 loop over the points `i ∈ [k, n)`: adds `d_i[j] • P_i`. -/
@[local step]
private theorem optional_mixed_multiscalar_mul_loop0_loop1_spec (iter : core.ops.range.Range Usize)
    (static_nafs : alloc.vec.Vec (Array I8 256#usize))
    (v : alloc.vec.Vec (window.NafLookupTable8 AffineNielsPoint.«x86_64-no-tables»))
    (j : Usize) (R : CompletedPoint.«x86_64-no-tables») (P : ℕ → curve25519.edwards.Point)
    (hj : j.val < 256) (hn : iter.end.val ≤ static_nafs.length ∧ iter.end.val ≤ v.length)
    (hT : ∀ m < iter.end.val, v.val[m]!.Represents (P m) ∧ v.val[m]!.LimbsLt 54)
    (hD : ∀ m < iter.end.val, ∀ e < 256, (static_nafs.val[m]!)[e]!.val ≠ 0 →
      (static_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(static_nafs.val[m]!)[e]!.val| < 2 ^ 8)
    (hk : iter.start.val ≤ iter.end.val) (hR : R.OnCurve) (hRb : R.LimbsLt 54) :
    optional_mixed_multiscalar_mul_loop0_loop1 iter v static_nafs j R
      ⦃ (r : CompletedPoint.«x86_64-no-tables») => r.OnCurve ∧ r.LimbsLt 54 ∧
        r.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val iter.end.val,
          (static_nafs.val[m]!)[j.val]!.val • P m ⦄ := by
  unfold optional_mixed_multiscalar_mul_loop0_loop1
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, R') => it.end = iter.end ∧ iter.start.val ≤ it.start.val ∧
      it.start.val ≤ iter.end.val ∧ R'.OnCurve ∧ R'.LimbsLt 54 ∧
      R'.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val it.start.val,
        (static_nafs.val[m]!)[j.val]!.val • P m)
  · rintro ⟨it, R'⟩ ⟨hend, hst, hle, hR'on, hR'b, hR'p⟩
    unfold optional_mixed_multiscalar_mul_loop0_loop1.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      have hm : it.start.val < iter.end.val := hend ▸ hlt
      obtain ⟨hrep, hb⟩ := hT it.start.val hm
      step as ⟨a, ha⟩
      rw [← getElem!_pos] at ha
      step as ⟨d, hd⟩
      have hstep : ∀ R1 : CompletedPoint.«x86_64-no-tables», R1.OnCurve → R1.LimbsLt 54 →
          R1.toPoint = R'.toPoint + d.val • P it.start.val →
          it1.end = iter.end ∧ iter.start.val ≤ it1.start.val ∧ it1.start.val ≤ iter.end.val ∧
          R1.OnCurve ∧ R1.LimbsLt 54 ∧
          R1.toPoint = R.toPoint + ∑ m ∈ Finset.Ico iter.start.val it1.start.val,
            (static_nafs.val[m]!)[j.val]!.val • P m ∧
          it1.end.val - it1.start.val < it.end.val - it.start.val := by
        intro R1 h1on h1b h1p
        refine ⟨hend1.trans hend, by scalar_tac, by scalar_tac, h1on, h1b, ?_, by scalar_tac⟩
        rw [h1p, hR'p, hstart1, Finset.sum_Ico_succ_top hst, add_assoc, hd, ha]
      rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
      rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 8) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_neg hneg] at hdk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable8.select_spec (P := P it.start.val) _ tab i2
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with sub_spec_point
            ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show AffineNielsPoint.«x86_64-no-tables».toPoint q = PointRepr.toPoint q from
            rfl, hq]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        exact hstep R' hR'on hR'b (by rw [hzero, zero_smul, add_zero])
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 8) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_pos hpos] at hdk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable8.select_spec (P := P it.start.val) _ tab i1
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with add_spec_point
            ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show AffineNielsPoint.«x86_64-no-tables».toPoint q = PointRepr.toPoint q from
            rfl, hq]
        exact add_nsmul_eq _ _ _ _ (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : it.start.val = iter.end.val := by rw [← hend]; scalar_tac
      exact ⟨hR'on, hR'b, this ▸ hR'p⟩
  · exact ⟨rfl, le_refl _, hk, hR, hRb, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The outer loop over the digit positions, from the top. -/
@[local step]
private theorem optional_mixed_multiscalar_mul_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (v : alloc.vec.Vec (window.NafLookupTable8 AffineNielsPoint.«x86_64-no-tables»))
    (static_nafs dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec
        (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»))
    (dp : Usize) (S : ProjectivePoint.«x86_64-no-tables») (P Q : ℕ → curve25519.edwards.Point)
    (hdp : dp.val ≤ dynamic_nafs.length ∧ dp.val ≤ dynamic_lookup_tables.length)
    (hsl : static_nafs.length ≤ v.length)
    (hT : ∀ m < dp.val, dynamic_lookup_tables.val[m]!.Represents (Q m) ∧
      dynamic_lookup_tables.val[m]!.LimbsLt 54)
    (hD : ∀ m < dp.val, ∀ e < 256, (dynamic_nafs.val[m]!)[e]!.val ≠ 0 →
      (dynamic_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(dynamic_nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hV : ∀ m < static_nafs.length, v.val[m]!.Represents (P m) ∧ v.val[m]!.LimbsLt 54)
    (hE : ∀ m < static_nafs.length, ∀ e < 256, (static_nafs.val[m]!)[e]!.val ≠ 0 →
      (static_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(static_nafs.val[m]!)[e]!.val| < 2 ^ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hS : S.OnCurve) (hSb : S.LimbsLt 52)
    (hSp : S.toPoint =
      (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! iter.iter.end.val • Q m) +
        ∑ m ∈ Finset.range static_nafs.length,
          nafTail static_nafs.val[m]! iter.iter.end.val • P m) :
    optional_mixed_multiscalar_mul_loop0 iter v static_nafs dynamic_nafs dynamic_lookup_tables dp S
      ⦃ (r : ProjectivePoint.«x86_64-no-tables») => r.OnCurve ∧ r.LimbsLt 52 ∧ r.toPoint =
        (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! 0 • Q m) +
          ∑ m ∈ Finset.range static_nafs.length, nafTail static_nafs.val[m]! 0 • P m ⦄ := by
  unfold optional_mixed_multiscalar_mul_loop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, q) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ q.OnCurve ∧
      q.LimbsLt 52 ∧ q.toPoint =
        (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! it.iter.end.val • Q m) +
          ∑ m ∈ Finset.range static_nafs.length,
            nafTail static_nafs.val[m]! it.iter.end.val • P m)
  · rintro ⟨it, q⟩ ⟨hst, hen, hqon, hqb, hqp⟩
    unfold optional_mixed_multiscalar_mul_loop0.body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, j, ho, hj, hstart1, hend1⟩
      subst ho
      have hj256 : j.val < 256 := by scalar_tac
      step with «ProjectivePointx86_64-no-tables».double_spec_point as ⟨R, hRon, hRp, hRb⟩
      step with optional_mixed_multiscalar_mul_loop0_loop0_spec
        { start := 0#usize, «end» := dp } dynamic_nafs dynamic_lookup_tables j R Q hj256 hdp hT hD
        (Nat.zero_le _) hRon hRb as ⟨R1, hR1on, hR1b, hR1⟩
      step with optional_mixed_multiscalar_mul_loop0_loop1_spec
        { start := 0#usize, «end» := alloc.vec.Vec.len static_nafs } static_nafs v j R1 P hj256
        ⟨by simp, by simpa using hsl⟩ (by simpa using hV) (by simpa using hE) (Nat.zero_le _)
        hR1on hR1b as ⟨R2, hR2on, hR2b, hR2⟩
      step with «CompletedPointx86_64-no-tables».as_projective_spec_point as ⟨q1, hq1on, hq1, hq1b⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, hq1on, hq1b, ?_, by scalar_tac⟩
      simp only [alloc.vec.Vec.len_val] at hR1 hR2
      rw [hq1, hR2, hR1, hRp, hqp, ← Finset.range_eq_Ico, ← Finset.range_eq_Ico, hend1, ← hj,
        add_assoc, ← add_assoc (2 • _),
        horner2_two dp.val static_nafs.length j.val (fun k => dynamic_nafs.val[k]!)
          (fun k => static_nafs.val[k]!) Q P hj256]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at hqp
      exact ⟨hqon, hqb, hqp⟩
  · exact ⟨hstart, hend, hS, hSb, hSp⟩

/-- `VartimePrecomputedStraus::optional_mixed_multiscalar_mul`: for a precomputation of the
static points `ps`, `none` iff some dynamic point is `none`; otherwise
`∑ s_i • ps_i + ∑ d_i • Q_i` over the static scalars (at most `|ps|`, the missing ones count as
`0`) and the dynamic scalars and points (as many scalars as points); unreduced scalars
`< 2^255`; limbs `< 2^52`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«x86_64-no-tables») Clause4_IntoIter)
    (self : VartimePrecomputedStraus.«x86_64-no-tables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (ps : List curve25519.edwards.Point) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (hself : self.Represents ps) (hself_b : self.LimbsLt 54)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52 ∧ Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : ss.length ≤ ps.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss ps).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold optional_mixed_multiscalar_mul
  have h1 : staticScalarsInst.into_iter static_scalars
      ⦃ (it : Clause0_IntoIter) => staticScalarsInst.iteratorInst.Yields it xs ⦄ :=
    hstatic_scalars
  have h2 : dynamicScalarsInst.into_iter dynamic_scalars
      ⦃ (it : Clause2_IntoIter) => dynamicScalarsInst.iteratorInst.Yields it ys ⦄ :=
    hdynamic_scalars
  have h3 : dynamicPointsInst.into_iter dynamic_points
      ⦃ (it : Clause4_IntoIter) => dynamicPointsInst.iteratorInst.Yields it qops ⦄ :=
    hdynamic_points
  step with h1 as ⟨it, hit⟩
  step with optional_mixed_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_static hss hxs 8#usize (by decide) as ⟨sn, hsn⟩
  step with h2 as ⟨it1, hit1⟩
  step with optional_mixed_multiscalar_mul.nafs_spec
    _ _ it1 ys hit1 ds hborrow_dynamic hds hys 5#usize (by decide) as ⟨dn, hdn⟩
  step with h3 as ⟨it2, hit2⟩
  step with optional_mixed_multiscalar_mul.lookup_tables_spec
    _ it2 qops hit2 hqs hqops as ⟨o, hnone, hsome⟩
  rcases o with _ | dtabs
  · dsimp only
    rw [WP.spec_ok]
    exact ⟨by simpa using hnone, fun R hR => by cases hR⟩
  · have hnn : none ∉ qops := fun h => by cases hnone.mpr h
    obtain ⟨hTlen, hT⟩ := forall₂_getElem! (hsome dtabs rfl)
    obtain ⟨hDlen, hD⟩ := forall₂_getElem! hdn
    obtain ⟨hSlen, hS⟩ := forall₂_getElem! hsn
    obtain ⟨hVlen, hV⟩ := forall₂_getElem! hself
    have hfl := length_filterMap_id qops hnn
    have hdq := hdynamic hnn
    step
    step
    step with
        ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
      as ⟨S0, hS0on, hS0, hS0b⟩
    step as ⟨iter, hiter⟩
    step with optional_mixed_multiscalar_mul_loop0_spec iter self.static_lookup_tables sn dn dtabs
      (alloc.vec.Vec.len dtabs) S0 (fun m => ps[m]!) (fun m => ((qops.filterMap id)[m]!).toPoint)
      ⟨by scalar_tac, by scalar_tac⟩ (by scalar_tac)
      (fun m hm => hT m (by scalar_tac))
      (fun m hm => (hD m (by scalar_tac)).2)
      (fun m hm => ⟨hV m (by scalar_tac),
        hself_b _ (by rw [getElem!_pos _ m (by scalar_tac)]; exact List.getElem_mem _)⟩)
      (fun m hm => (hS m (by scalar_tac)).2)
      (by rw [hiter]; rfl) (by rw [hiter]; decide) hS0on hS0b
      (by
        have he : iter.iter.end.val = 256 := by rw [hiter]; rfl
        rw [hS0, he]
        simp only [nafTail_eq_zero _ 256 fun j hj hj' => absurd hj' (Nat.not_lt.mpr hj),
          zero_smul, Finset.sum_const_zero, add_zero])
      as ⟨S1, hS1on, hS1b, hS1⟩
    step with «ProjectivePointx86_64-no-tables».as_extended_spec_point as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hS1, add_comm, sum_zipWith_eq, sum_zipWith_eq,
      show min ss.length ps.length = sn.val.length by
        rw [← hSlen]; exact Nat.min_eq_left hstatic,
      show min ds.length (qops.filterMap id).length = (alloc.vec.Vec.len dtabs).val by
        rw [alloc.vec.Vec.len_val, show dtabs.length = dtabs.val.length from rfl, ← hTlen, hfl,
          hdq, Nat.min_self]]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [nafTail_zero, (hS k (by rw [hSlen]; exact hk')).1, natCast_zsmul]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [nafTail_zero, (hD k (by scalar_tac)).1, natCast_zsmul]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end VartimePrecomputedStraus.«x86_64-no-tables».Insts

end

end Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus
