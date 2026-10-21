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
import Proofs.Backend.Serial.CurveModels.CompletedAsProjective
import Proofs.Backend.Serial.CurveModels.ProjectiveAsExtended
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Backend.Serial.CurveModels.ProjectiveIdentity
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Helpers.Cmp
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.NonAdjacentForm
import Proofs.Window.NafLookupTable5From
import Proofs.Window.NafLookupTable5Select
public section

/-! # `Straus::optional_multiscalar_mul`

Variable-time Straus: the width-`5` non-adjacent forms of the scalars, the tables of odd
multiples of the points (`None` as soon as a point is `None`, as the patched helper), and
Horner's rule in base `2` over the `256` digit positions, adding `d • P_i` for each nonzero digit
(up to the shorter of the two inputs). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.straus

/-- `Forall₂` as a statement about the entries `getElem!`. -/
private theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    l₁.length = l₂.length ∧ ∀ k < l₁.length, R l₁[k]! l₂[k]! := by
  refine ⟨h.length_eq, fun k hk => ?_⟩
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (h.length_eq ▸ hk)]
  exact (List.forall₂_iff_get.mp h).2 k hk _

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
    (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
    (sub_spec_point)

namespace «VartimeMultiscalarMulStrausEdwardsPointx86_64-tables».optional_multiscalar_mul

/-- The scalars' width-`5` non-adjacent forms. -/
@[local step]
private theorem nafs_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    nafs iterInst borrowInst scalars
      ⦃ (r : alloc.vec.Vec (Array I8 256#usize)) =>
        List.Forall₂ (fun s d => d.asInt 1 = s.asNat ∧ ∀ i < 256, d[i]!.val ≠ 0 →
          d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5) ss r.val ⦄ := by
  unfold nafs nafs_loop
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    (fun s => scalar.Scalar.non_adjacent_form s 5#usize)
    (fun s d => d.asInt 1 = s.asNat ∧ ∀ i < 256, d[i]!.val ≠ 0 →
      d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5)
    scalars xs hit ss hborrow (fun s hs =>
      spec_mono (scalar.Scalar.non_adjacent_form_spec s 5#usize (by decide) (hss s hs))
        fun d ⟨hval, hdig, _⟩ => ⟨hval, hdig⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

set_option linter.style.longLine false in
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
      step with
          window.«NafLookupTable5ProjectiveNielsPointx86_64-tables».Insts.«CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec
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

end «VartimeMultiscalarMulStrausEdwardsPointx86_64-tables».optional_multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

open scoped Helpers.IndexStep in
/-- The inner loop: adds `d_k[i] • P_k` for `k = k₀, …, n - 1`. -/
@[local step]
private theorem optional_multiscalar_mul_loop0_loop0_spec
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»))
    (i : Usize) (t : CompletedPoint.«x86_64-tables») (n k : Usize)
        (P : ℕ → curve25519.edwards.Point)
    (hi : i.val < 256) (hn : n.val ≤ nafs.length ∧ n.val ≤ lookup_tables.length)
    (hT : ∀ m < n.val, lookup_tables.val[m]!.Represents (P m) ∧ lookup_tables.val[m]!.LimbsLt 54)
    (hD : ∀ m < n.val, ∀ e < 256, (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hk : k.val ≤ n.val) (ht : t.OnCurve) (htb : t.LimbsLt 54) :
    optional_multiscalar_mul_loop0_loop0 nafs lookup_tables i t n k
      ⦃ (r : CompletedPoint.«x86_64-tables») => r.OnCurve ∧ r.LimbsLt 54 ∧
        r.toPoint = t.toPoint + ∑ m ∈ Finset.Ico k.val n.val,
          (nafs.val[m]!)[i.val]!.val • P m ⦄ := by
  unfold optional_multiscalar_mul_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (_, k') => n.val - k'.val)
    (inv := fun (t', k') => k.val ≤ k'.val ∧ k'.val ≤ n.val ∧ t'.OnCurve ∧ t'.LimbsLt 54 ∧
      t'.toPoint = t.toPoint + ∑ m ∈ Finset.Ico k.val k'.val,
        (nafs.val[m]!)[i.val]!.val • P m)
  · rintro ⟨t', k'⟩ ⟨hkk, hkn, ht'on, ht'b, ht'p⟩
    unfold optional_multiscalar_mul_loop0_loop0.body
    by_cases hlt : k' < n
    · simp only [hlt, ite_true]
      have hm : k'.val < n.val := hlt
      obtain ⟨hrep, hb⟩ := hT k'.val hm
      step as ⟨a, ha⟩
      rw [← getElem!_pos] at ha
      step as ⟨d, hd⟩
      rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
      apply spec_bind (Pₘ := fun t1 => t1.OnCurve ∧
        t1.toPoint = t'.toPoint + d.val • P k'.val ∧ t1.LimbsLt 54)
      · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
        · rw [(compare_lt_iff_lt).mpr hneg]
          simp only
          step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
          step as ⟨tab, htab⟩
          rw [← getElem!_pos] at htab
          have hdk := naf_digit_abs (w := 5) (by norm_num)
            (hD k'.val hm i.val hi (by rw [← ha, ← hd]; omega))
          rw [← ha, ← hd, abs_of_neg hneg] at hdk
          step as ⟨i1, hi1⟩
          step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
          step with window.NafLookupTable5.select_spec (P := P k'.val) _ tab i2
            (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
          step with sub_spec_point ep q hepb hqb hepon hqon as ⟨t1, ht1on, ht1p, ht1b⟩
          refine ⟨ht1on, ?_, ht1b⟩
          rw [ht1p, hep, show ProjectiveNielsPoint.«x86_64-tables».toPoint q = PointRepr.toPoint q
              from rfl,
            hq]
          exact sub_nsmul_eq _ _ _ _ (by omega)
        · rw [(compare_eq_iff_eq).mpr hzero]
          simp only [WP.spec_ok]
          rw [hzero, zero_smul, add_zero]
          exact ⟨ht'on, rfl, ht'b⟩
        · rw [(compare_gt_iff_gt).mpr hpos]
          simp only
          step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
          step as ⟨tab, htab⟩
          rw [← getElem!_pos] at htab
          have hdk := naf_digit_abs (w := 5) (by norm_num)
            (hD k'.val hm i.val hi (by rw [← ha, ← hd]; omega))
          rw [← ha, ← hd, abs_of_pos hpos] at hdk
          step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
          step with window.NafLookupTable5.select_spec (P := P k'.val) _ tab i1
            (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
          step with add_spec_point ep q hepb hqb hepon hqon as ⟨t1, ht1on, ht1p, ht1b⟩
          refine ⟨ht1on, ?_, ht1b⟩
          rw [ht1p, hep, show ProjectiveNielsPoint.«x86_64-tables».toPoint q = PointRepr.toPoint q
              from rfl,
            hq]
          exact add_nsmul_eq _ _ _ _ (by omega)
      · rintro t1 ⟨ht1on, ht1p, ht1b⟩
        step as ⟨k1, hk1⟩
        refine ⟨by scalar_tac, by scalar_tac, ht1on, ht1b, ?_, by scalar_tac⟩
        rw [ht1p, ht'p, show k1.val = k'.val + 1 by scalar_tac, Finset.sum_Ico_succ_top hkk,
          add_assoc, hd, ha]
    · simp only [hlt, ite_false, WP.spec_ok]
      have : k'.val = n.val := by scalar_tac
      exact ⟨ht'on, ht'b, this ▸ ht'p⟩
  · exact ⟨le_refl _, hk, ht, htb, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The outer loop: after the digit positions `e, …, 255`, the accumulator represents
`∑_{m < n} nafTail d_m e • P_m`. -/
@[local step]
private theorem optional_multiscalar_mul_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»))
    (r : ProjectivePoint.«x86_64-tables») (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min nafs.length lookup_tables.length)
    (hT : ∀ m < n, lookup_tables.val[m]!.Represents (P m) ∧ lookup_tables.val[m]!.LimbsLt 54)
    (hD : ∀ m < n, ∀ e < 256, (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! iter.iter.end.val • P m) :
    optional_multiscalar_mul_loop0 iter nafs lookup_tables r
      ⦃ (res : ProjectivePoint.«x86_64-tables») => res.OnCurve ∧ res.LimbsLt 52 ∧
        res.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! 0 • P m ⦄ := by
  unfold optional_multiscalar_mul_loop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, q) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ q.OnCurve ∧
      q.LimbsLt 52 ∧ q.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! it.iter.end.val • P m)
  · rintro ⟨it, q⟩ ⟨hst, hen, hqon, hqb, hqp⟩
    unfold optional_multiscalar_mul_loop0.body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, i, ho, hi, hstart1, hend1⟩
      subst ho
      step with «ProjectivePointx86_64-tables».double_spec_point as ⟨t, hton, htp, htb⟩
      step as ⟨m, hm⟩
      have hmn : m.val = n := by rw [hn]; scalar_tac
      step with optional_multiscalar_mul_loop0_loop0_spec nafs lookup_tables i t m 0#usize P
        (by scalar_tac) (by scalar_tac) (hmn ▸ hT) (hmn ▸ hD) (by scalar_tac) hton htb
        as ⟨t1, ht1on, ht1b, ht1⟩
      step with «CompletedPointx86_64-tables».as_projective_spec_point as ⟨q1, hq1on, hq1, hq1b⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, hq1on, hq1b, ?_, by scalar_tac⟩
      rw [hq1, ht1, htp, hqp, hmn, ← Finset.range_eq_Ico, hend1, ← hi,
        horner2 n i.val (fun k => nafs.val[k]!) P (by scalar_tac)]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at hqp
      exact ⟨hqon, hqb, hqp⟩
  · exact ⟨hstart, hend, hr, hrb, hrp⟩

set_option linter.style.longLine false in
/-- `Straus::optional_multiscalar_mul`: `none` iff some point is `none` (all points are read);
otherwise `∑ s_i • P_i` over the scalars and points, up to the shorter input (unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with
      «VartimeMultiscalarMulStrausEdwardsPointx86_64-tables».optional_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_scalars hss hxs as ⟨nafs, hnafs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with
      «VartimeMultiscalarMulStrausEdwardsPointx86_64-tables».optional_multiscalar_mul.lookup_tables_spec
    _ it1 ops hit1 hps hops as ⟨o, hnone, hsome⟩
  rcases o with _ | tables
  · dsimp only
    rw [WP.spec_ok]
    exact ⟨by simpa using hnone, fun R hR => absurd hR (by simp)⟩
  · have htables := hsome tables rfl
    obtain ⟨hTlen, hT⟩ := forall₂_getElem! htables
    obtain ⟨hDlen, hD⟩ := forall₂_getElem! hnafs
    have hn : min ss.length (ops.filterMap id).length = min nafs.length tables.length := by
      rw [hTlen, hDlen]
    step with
        ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
      as ⟨r, hron, hr, hrb⟩
    step as ⟨iter, hiter⟩
    step with optional_multiscalar_mul_loop0_spec iter nafs tables r
      (fun k => (ops.filterMap id)[k]!.toPoint) (min ss.length (ops.filterMap id).length) hn
      (fun k hk => hT k (by have := min_le_right ss.length (ops.filterMap id).length; omega))
      (fun k hk => (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).2)
      (by rw [hiter]; rfl) (by rw [hiter]; decide) hron hrb
      (by
        rw [hr, hiter]
        exact (Finset.sum_eq_zero fun k _ => by
          rw [show ({ start := 0#usize, «end» := 256#usize } : core.ops.range.Range Usize).end.val
            = 256 from rfl, nafTail_eq_zero _ _ fun j hj hj' => by omega, zero_smul]).symm)
      as ⟨q, hqon, hqb, hq⟩
    step with «ProjectivePointx86_64-tables».as_extended_spec_point as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnone, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hq, sum_zipWith_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [nafTail_zero, (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).1,
      natCast_zsmul]

end Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    (sub_spec_point)

namespace «VartimeMultiscalarMulStrausEdwardsPointx86_64-no-tables».optional_multiscalar_mul

/-- The scalars' width-`5` non-adjacent forms. -/
@[local step]
private theorem nafs_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    nafs iterInst borrowInst scalars
      ⦃ (r : alloc.vec.Vec (Array I8 256#usize)) =>
        List.Forall₂ (fun s d => d.asInt 1 = s.asNat ∧ ∀ i < 256, d[i]!.val ≠ 0 →
          d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5) ss r.val ⦄ := by
  unfold nafs nafs_loop
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    (fun s => scalar.Scalar.non_adjacent_form s 5#usize)
    (fun s d => d.asInt 1 = s.asNat ∧ ∀ i < 256, d[i]!.val ≠ 0 →
      d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5)
    scalars xs hit ss hborrow (fun s hs =>
      spec_mono (scalar.Scalar.non_adjacent_form_spec s 5#usize (by decide) (hss s hs))
        fun d ⟨hval, hdig, _⟩ => ⟨hval, hdig⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

set_option linter.style.longLine false in
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
      step with
          window.«NafLookupTable5ProjectiveNielsPointx86_64-no-tables».Insts.«CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from_spec
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

end «VartimeMultiscalarMulStrausEdwardsPointx86_64-no-tables».optional_multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

open scoped Helpers.IndexStep in
/-- The inner loop: adds `d_k[i] • P_k` for `k = k₀, …, n - 1`. -/
@[local step]
private theorem optional_multiscalar_mul_loop0_loop0_spec
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»))
    (i : Usize) (t : CompletedPoint.«x86_64-no-tables») (n k : Usize)
        (P : ℕ → curve25519.edwards.Point)
    (hi : i.val < 256) (hn : n.val ≤ nafs.length ∧ n.val ≤ lookup_tables.length)
    (hT : ∀ m < n.val, lookup_tables.val[m]!.Represents (P m) ∧ lookup_tables.val[m]!.LimbsLt 54)
    (hD : ∀ m < n.val, ∀ e < 256, (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hk : k.val ≤ n.val) (ht : t.OnCurve) (htb : t.LimbsLt 54) :
    optional_multiscalar_mul_loop0_loop0 nafs lookup_tables i t n k
      ⦃ (r : CompletedPoint.«x86_64-no-tables») => r.OnCurve ∧ r.LimbsLt 54 ∧
        r.toPoint = t.toPoint + ∑ m ∈ Finset.Ico k.val n.val,
          (nafs.val[m]!)[i.val]!.val • P m ⦄ := by
  unfold optional_multiscalar_mul_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (_, k') => n.val - k'.val)
    (inv := fun (t', k') => k.val ≤ k'.val ∧ k'.val ≤ n.val ∧ t'.OnCurve ∧ t'.LimbsLt 54 ∧
      t'.toPoint = t.toPoint + ∑ m ∈ Finset.Ico k.val k'.val,
        (nafs.val[m]!)[i.val]!.val • P m)
  · rintro ⟨t', k'⟩ ⟨hkk, hkn, ht'on, ht'b, ht'p⟩
    unfold optional_multiscalar_mul_loop0_loop0.body
    by_cases hlt : k' < n
    · simp only [hlt, ite_true]
      have hm : k'.val < n.val := hlt
      obtain ⟨hrep, hb⟩ := hT k'.val hm
      step as ⟨a, ha⟩
      rw [← getElem!_pos] at ha
      step as ⟨d, hd⟩
      rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
      apply spec_bind (Pₘ := fun t1 => t1.OnCurve ∧
        t1.toPoint = t'.toPoint + d.val • P k'.val ∧ t1.LimbsLt 54)
      · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
        · rw [(compare_lt_iff_lt).mpr hneg]
          simp only
          step with «CompletedPointx86_64-no-tables».as_extended_spec_point as
              ⟨ep, hepon, hep, hepb⟩
          step as ⟨tab, htab⟩
          rw [← getElem!_pos] at htab
          have hdk := naf_digit_abs (w := 5) (by norm_num)
            (hD k'.val hm i.val hi (by rw [← ha, ← hd]; omega))
          rw [← ha, ← hd, abs_of_neg hneg] at hdk
          step as ⟨i1, hi1⟩
          step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
          step with window.NafLookupTable5.select_spec (P := P k'.val) _ tab i2
            (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
          step with sub_spec_point ep q hepb hqb hepon hqon as ⟨t1, ht1on, ht1p, ht1b⟩
          refine ⟨ht1on, ?_, ht1b⟩
          rw [ht1p, hep, show ProjectiveNielsPoint.«x86_64-no-tables».toPoint q = PointRepr.toPoint
              q from rfl,
            hq]
          exact sub_nsmul_eq _ _ _ _ (by omega)
        · rw [(compare_eq_iff_eq).mpr hzero]
          simp only [WP.spec_ok]
          rw [hzero, zero_smul, add_zero]
          exact ⟨ht'on, rfl, ht'b⟩
        · rw [(compare_gt_iff_gt).mpr hpos]
          simp only
          step with «CompletedPointx86_64-no-tables».as_extended_spec_point as
              ⟨ep, hepon, hep, hepb⟩
          step as ⟨tab, htab⟩
          rw [← getElem!_pos] at htab
          have hdk := naf_digit_abs (w := 5) (by norm_num)
            (hD k'.val hm i.val hi (by rw [← ha, ← hd]; omega))
          rw [← ha, ← hd, abs_of_pos hpos] at hdk
          step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
          step with window.NafLookupTable5.select_spec (P := P k'.val) _ tab i1
            (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
          step with add_spec_point ep q hepb hqb hepon hqon as ⟨t1, ht1on, ht1p, ht1b⟩
          refine ⟨ht1on, ?_, ht1b⟩
          rw [ht1p, hep, show ProjectiveNielsPoint.«x86_64-no-tables».toPoint q = PointRepr.toPoint
              q from rfl,
            hq]
          exact add_nsmul_eq _ _ _ _ (by omega)
      · rintro t1 ⟨ht1on, ht1p, ht1b⟩
        step as ⟨k1, hk1⟩
        refine ⟨by scalar_tac, by scalar_tac, ht1on, ht1b, ?_, by scalar_tac⟩
        rw [ht1p, ht'p, show k1.val = k'.val + 1 by scalar_tac, Finset.sum_Ico_succ_top hkk,
          add_assoc, hd, ha]
    · simp only [hlt, ite_false, WP.spec_ok]
      have : k'.val = n.val := by scalar_tac
      exact ⟨ht'on, ht'b, this ▸ ht'p⟩
  · exact ⟨le_refl _, hk, ht, htb, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The outer loop: after the digit positions `e, …, 255`, the accumulator represents
`∑_{m < n} nafTail d_m e • P_m`. -/
@[local step]
private theorem optional_multiscalar_mul_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»))
    (r : ProjectivePoint.«x86_64-no-tables») (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min nafs.length lookup_tables.length)
    (hT : ∀ m < n, lookup_tables.val[m]!.Represents (P m) ∧ lookup_tables.val[m]!.LimbsLt 54)
    (hD : ∀ m < n, ∀ e < 256, (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! iter.iter.end.val • P m) :
    optional_multiscalar_mul_loop0 iter nafs lookup_tables r
      ⦃ (res : ProjectivePoint.«x86_64-no-tables») => res.OnCurve ∧ res.LimbsLt 52 ∧
        res.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! 0 • P m ⦄ := by
  unfold optional_multiscalar_mul_loop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, q) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ q.OnCurve ∧
      q.LimbsLt 52 ∧ q.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! it.iter.end.val • P m)
  · rintro ⟨it, q⟩ ⟨hst, hen, hqon, hqb, hqp⟩
    unfold optional_multiscalar_mul_loop0.body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, i, ho, hi, hstart1, hend1⟩
      subst ho
      step with «ProjectivePointx86_64-no-tables».double_spec_point as ⟨t, hton, htp, htb⟩
      step as ⟨m, hm⟩
      have hmn : m.val = n := by rw [hn]; scalar_tac
      step with optional_multiscalar_mul_loop0_loop0_spec nafs lookup_tables i t m 0#usize P
        (by scalar_tac) (by scalar_tac) (hmn ▸ hT) (hmn ▸ hD) (by scalar_tac) hton htb
        as ⟨t1, ht1on, ht1b, ht1⟩
      step with «CompletedPointx86_64-no-tables».as_projective_spec_point as ⟨q1, hq1on, hq1, hq1b⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, hq1on, hq1b, ?_, by scalar_tac⟩
      rw [hq1, ht1, htp, hqp, hmn, ← Finset.range_eq_Ico, hend1, ← hi,
        horner2 n i.val (fun k => nafs.val[k]!) P (by scalar_tac)]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at hqp
      exact ⟨hqon, hqb, hqp⟩
  · exact ⟨hstart, hend, hr, hrb, hrp⟩

set_option linter.style.longLine false in
/-- `Straus::optional_multiscalar_mul`: `none` iff some point is `none` (all points are read);
otherwise `∑ s_i • P_i` over the scalars and points, up to the shorter input (unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with
      «VartimeMultiscalarMulStrausEdwardsPointx86_64-no-tables».optional_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_scalars hss hxs as ⟨nafs, hnafs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with
      «VartimeMultiscalarMulStrausEdwardsPointx86_64-no-tables».optional_multiscalar_mul.lookup_tables_spec
    _ it1 ops hit1 hps hops as ⟨o, hnone, hsome⟩
  rcases o with _ | tables
  · dsimp only
    rw [WP.spec_ok]
    exact ⟨by simpa using hnone, fun R hR => absurd hR (by simp)⟩
  · have htables := hsome tables rfl
    obtain ⟨hTlen, hT⟩ := forall₂_getElem! htables
    obtain ⟨hDlen, hD⟩ := forall₂_getElem! hnafs
    have hn : min ss.length (ops.filterMap id).length = min nafs.length tables.length := by
      rw [hTlen, hDlen]
    step with
        ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
      as ⟨r, hron, hr, hrb⟩
    step as ⟨iter, hiter⟩
    step with optional_multiscalar_mul_loop0_spec iter nafs tables r
      (fun k => (ops.filterMap id)[k]!.toPoint) (min ss.length (ops.filterMap id).length) hn
      (fun k hk => hT k (by have := min_le_right ss.length (ops.filterMap id).length; omega))
      (fun k hk => (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).2)
      (by rw [hiter]; rfl) (by rw [hiter]; decide) hron hrb
      (by
        rw [hr, hiter]
        exact (Finset.sum_eq_zero fun k _ => by
          rw [show ({ start := 0#usize, «end» := 256#usize } : core.ops.range.Range Usize).end.val
            = 256 from rfl, nafTail_eq_zero _ _ fun j hj hj' => by omega, zero_smul]).symm)
      as ⟨q, hqon, hqb, hq⟩
    step with «ProjectivePointx86_64-no-tables».as_extended_spec_point as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnone, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hq, sum_zipWith_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [nafTail_zero, (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).1,
      natCast_zsmul]

end Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

end

end Curve25519Dalek.backend.serial.scalar_mul.straus
