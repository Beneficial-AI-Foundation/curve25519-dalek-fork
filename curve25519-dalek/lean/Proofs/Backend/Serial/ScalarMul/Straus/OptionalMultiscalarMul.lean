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
public import Proofs.Helpers.EdwardsOps.Instances
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


end Curve25519Dalek.backend.serial.scalar_mul.straus

/-! ## The loops over a configuration's point operations -/

namespace Curve25519Dalek.EdwardsOps

open Curve25519Dalek.backend.serial.scalar_mul.straus

variable (O : EdwardsOps)

open ControlFlow

/-- `optional_multiscalar_mul_loop0_loop0.body` over the point operations. -/
@[expose] def strausLoop00Body (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (i : Usize) (n : Usize) (t : O.C)
    (k : Usize) : Result (ControlFlow (O.C × Usize) O.C) := do
  if k < n
  then
    let a ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array I8 256#usize)) nafs k
    let digit ← Array.index_usize a i
    let o ← lift (core.cmp.impls.OrdI8.cmp digit 0#i8)
    let t1 ←
      match o with
      | Ordering.lt =>
        do
        let ep ← O.asExtended t
        let nlt ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (window.NafLookupTable5 O.N))
            lookup_tables k
        let i1 ← -. digit
        let i2 ← lift (IScalar.hcast .Usize i1)
        let pnp ← window.NafLookupTable5.select O.copyN nlt i2
        O.subN ep pnp
      | Ordering.eq => ok t
      | Ordering.gt =>
        do
        let ep ← O.asExtended t
        let nlt ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (window.NafLookupTable5 O.N))
            lookup_tables k
        let i1 ← lift (IScalar.hcast .Usize digit)
        let pnp ← window.NafLookupTable5.select O.copyN nlt i1
        O.addN ep pnp
    let k1 ← k + 1#usize
    ok (cont (t1, k1))
  else ok (done t)

/-- `optional_multiscalar_mul_loop0_loop0` over the point operations. -/
@[expose] def strausLoop00 (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (i : Usize) (t : O.C) (n : Usize)
    (k : Usize) : Result O.C := do
  loop (fun (t1, k1) => O.strausLoop00Body nafs lookup_tables i n t1 k1) (t, k)

/-- `optional_multiscalar_mul_loop0.body` over the point operations. -/
@[expose] def strausLoop0Body (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N))
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (r : O.Pr) :
    Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) × O.Pr)
      O.Pr) := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter
  match o with
  | none => ok (done r)
  | some i =>
    let t ← O.pDouble r
    let i1 := alloc.vec.Vec.len nafs
    let i2 := alloc.vec.Vec.len lookup_tables
    let n ← core.cmp.min core.cmp.OrdUsize i1 i2
    let t1 ← O.strausLoop00 nafs lookup_tables i t n 0#usize
    let r1 ← O.cAsProjective t1
    ok (cont (iter1, r1))

/-- `optional_multiscalar_mul_loop0` over the point operations. -/
@[expose] def strausLoop0 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (r : O.Pr) : Result O.Pr := do
  loop (fun (iter1, r1) => O.strausLoop0Body nafs lookup_tables iter1 r1) (iter, r)

open scoped Helpers.IndexStep in
/-- The inner loop: adds `d_k[i] • P_k` for `k = k₀, …, n - 1`. -/
private theorem strausLoop00_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec)
    (hasE : O.AsExtendedSpec) (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N))
    (i : Usize) (t : O.C) (n k : Usize) (P : ℕ → curve25519.edwards.Point)
    (hi : i.val < 256) (hn : n.val ≤ nafs.length ∧ n.val ≤ lookup_tables.length)
    (hT : ∀ m < n.val, lookup_tables.val[m]!.Represents (P m) ∧
      lookup_tables.val[m]!.LimbsLt O.nB)
    (hD : ∀ m < n.val, ∀ e < 256, (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hk : k.val ≤ n.val) (ht : O.cOnCurve t) (htb : O.cBnd t) :
    O.strausLoop00 nafs lookup_tables i t n k ⦃ (r : O.C) => O.cOnCurve r ∧ O.cBnd r ∧
        O.cToPoint r = O.cToPoint t + ∑ m ∈ Finset.Ico k.val n.val,
          (nafs.val[m]!)[i.val]!.val • P m ⦄ := by
  unfold strausLoop00
  apply loop.spec_decr_nat (measure := fun (_, k') => n.val - k'.val)
    (inv := fun (t', k') => k.val ≤ k'.val ∧ k'.val ≤ n.val ∧ O.cOnCurve t' ∧ O.cBnd t' ∧
      O.cToPoint t' = O.cToPoint t + ∑ m ∈ Finset.Ico k.val k'.val,
        (nafs.val[m]!)[i.val]!.val • P m)
  · rintro ⟨t', k'⟩ ⟨hkk, hkn, ht'on, ht'b, ht'p⟩
    unfold strausLoop00Body
    by_cases hlt : k' < n
    · simp only [hlt, ite_true]
      have hm : k'.val < n.val := hlt
      obtain ⟨hrep, hb⟩ := hT k'.val hm
      step as ⟨a, ha⟩
      rw [← getElem!_pos] at ha
      step as ⟨d, hd⟩
      rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
      apply spec_bind (Pₘ := fun t1 => O.cOnCurve t1 ∧
        O.cToPoint t1 = O.cToPoint t' + d.val • P k'.val ∧ O.cBnd t1)
      · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
        · rw [(compare_lt_iff_lt).mpr hneg]
          simp only
          step with hasE t' ht'b ht'on as ⟨ep, hepon, hep, hepb⟩
          step as ⟨tab, htab⟩
          rw [← getElem!_pos] at htab
          have hdk := naf_digit_abs (w := 5) (by norm_num)
            (hD k'.val hm i.val hi (by rw [← ha, ← hd]; omega))
          rw [← ha, ← hd, abs_of_neg hneg] at hdk
          step as ⟨i1, hi1⟩
          step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
          step with window.NafLookupTable5.select_spec (P := P k'.val) _ tab i2
            (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
          step with hsubN ep q hepb hqb hepon hqon as ⟨t1, ht1on, ht1p, ht1b⟩
          refine ⟨ht1on, ?_, ht1b⟩
          rw [ht1p, hep, show O.nToPoint q = PointRepr.toPoint q from rfl, hq]
          exact sub_nsmul_eq _ _ _ _ (by omega)
        · rw [(compare_eq_iff_eq).mpr hzero]
          simp only [WP.spec_ok]
          rw [hzero, zero_smul, add_zero]
          exact ⟨ht'on, rfl, ht'b⟩
        · rw [(compare_gt_iff_gt).mpr hpos]
          simp only
          step with hasE t' ht'b ht'on as ⟨ep, hepon, hep, hepb⟩
          step as ⟨tab, htab⟩
          rw [← getElem!_pos] at htab
          have hdk := naf_digit_abs (w := 5) (by norm_num)
            (hD k'.val hm i.val hi (by rw [← ha, ← hd]; omega))
          rw [← ha, ← hd, abs_of_pos hpos] at hdk
          step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
          step with window.NafLookupTable5.select_spec (P := P k'.val) _ tab i1
            (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
          step with haddN ep q hepb hqb hepon hqon as ⟨t1, ht1on, ht1p, ht1b⟩
          refine ⟨ht1on, ?_, ht1b⟩
          rw [ht1p, hep, show O.nToPoint q = PointRepr.toPoint q from rfl, hq]
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
private theorem strausLoop0_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec) (hasE : O.AsExtendedSpec)
    (hdbl : O.PDoubleSpec) (hasP : O.CAsProjectiveSpec)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N))
    (r : O.Pr) (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min nafs.length lookup_tables.length)
    (hT : ∀ m < n, lookup_tables.val[m]!.Represents (P m) ∧
      lookup_tables.val[m]!.LimbsLt O.nB)
    (hD : ∀ m < n, ∀ e < 256, (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hr : O.pOnCurve r) (hrb : O.pBnd r)
    (hrp : O.pToPoint r = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! iter.iter.end.val • P m) :
    O.strausLoop0 iter nafs lookup_tables r ⦃ (res : O.Pr) => O.pOnCurve res ∧ O.pBnd res ∧
        O.pToPoint res = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! 0 • P m ⦄ := by
  unfold strausLoop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, q) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ O.pOnCurve q ∧
      O.pBnd q ∧
        O.pToPoint q = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! it.iter.end.val • P m)
  · rintro ⟨it, q⟩ ⟨hst, hen, hqon, hqb, hqp⟩
    unfold strausLoop0Body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, i, ho, hi, hstart1, hend1⟩
      subst ho
      step with hdbl q hqb hqon as ⟨t, hton, htp, htb⟩
      step as ⟨m, hm⟩
      have hmn : m.val = n := by rw [hn]; scalar_tac
      step with O.strausLoop00_spec haddN hsubN hasE nafs lookup_tables i t m 0#usize P
        (by scalar_tac) (by scalar_tac) (hmn ▸ hT) (hmn ▸ hD) (by scalar_tac) hton htb
        as ⟨t1, ht1on, ht1b, ht1⟩
      step with hasP t1 ht1b ht1on as ⟨q1, hq1on, hq1, hq1b⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, hq1on, hq1b, ?_, by scalar_tac⟩
      rw [hq1, ht1, htp, hqp, hmn, ← Finset.range_eq_Ico, hend1, ← hi,
        horner2 n i.val (fun k => nafs.val[k]!) P (by scalar_tac)]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at hqp
      exact ⟨hqon, hqb, hqp⟩
  · exact ⟨hstart, hend, hr, hrb, hrp⟩

end Curve25519Dalek.EdwardsOps

namespace Curve25519Dalek.backend.serial.scalar_mul.straus

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

end «VartimeMultiscalarMulStrausEdwardsPointx86_64-tables».optional_multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

private theorem optional_multiscalar_mul_loop0_loop0_eq
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»))
    (i : Usize) (t : CompletedPoint.«x86_64-tables») (n k : Usize) :
    optional_multiscalar_mul_loop0_loop0 nafs lookup_tables i t n k =
      EdwardsOps.X86Tables.strausLoop00 nafs lookup_tables i t n k := by
  unfold optional_multiscalar_mul_loop0_loop0 EdwardsOps.strausLoop00
  congr 1

private theorem optional_multiscalar_mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»))
    (r : ProjectivePoint.«x86_64-tables») :
    optional_multiscalar_mul_loop0 iter nafs lookup_tables r =
      EdwardsOps.X86Tables.strausLoop0 iter nafs lookup_tables r := by
  unfold optional_multiscalar_mul_loop0 EdwardsOps.strausLoop0
  congr 1

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
  rw [optional_multiscalar_mul_loop0_eq]
  exact EdwardsOps.X86Tables.strausLoop0_spec
    EdwardsOps.X86Tables.addN_spec EdwardsOps.X86Tables.subN_spec
    EdwardsOps.X86Tables.asExtended_spec EdwardsOps.X86Tables.pDouble_spec
    EdwardsOps.X86Tables.cAsProjective_spec iter nafs lookup_tables r P n hn hT hD hstart hend hr
    hrb hrp

open «VartimeMultiscalarMulStrausEdwardsPointx86_64-tables» in
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
  step with optional_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_scalars hss hxs as ⟨nafs, hnafs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with optional_multiscalar_mul.lookup_tables_spec
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
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
    (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
    (sub_spec_point)

namespace «VartimeMultiscalarMulStrausEdwardsPointi686-tables».optional_multiscalar_mul

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

open window.«NafLookupTable5ProjectiveNielsPointi686-tables».Insts in
/-- The loop of `lookup_tables`: pushes the tables of the remaining points; `none` iff one of
them is `none`. -/
private theorem lookup_tables_loop_spec {It : Type}
    (iterInst : core.iter.traits.iterator.Iterator It (Option edwards.EdwardsPoint.«i686-tables»))
    (points : It) (ops : List (Option edwards.EdwardsPoint.«i686-tables»))
    (hit : iterInst.Yields points ops)
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (out : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»))
    (hlen : out.length + ops.length ≤ Usize.max) :
    lookup_tables_loop iterInst points out
      ⦃ (r : Option (alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»)))
          =>
        (r = none ↔ none ∈ ops) ∧ ∀ v, r = some v → ∃ zs, v.val = out.val ++ zs ∧
          List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) (ops.filterMap id)
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
      step with «CoreConvertFromSharedAEdwardsPointi686-tables».from_spec
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
    (iterInst : core.iter.traits.iterator.Iterator It (Option edwards.EdwardsPoint.«i686-tables»))
    (points : It) (ops : List (Option edwards.EdwardsPoint.«i686-tables»))
    (hit : iterInst.Yields points ops)
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve) (hlen : ops.length ≤ Usize.max) :
    lookup_tables iterInst points
      ⦃ (r : Option (alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»)))
          =>
        (r = none ↔ none ∈ ops) ∧ ∀ v, r = some v →
          List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27)
            (ops.filterMap id) v.val ⦄ := by
  unfold lookup_tables
  apply spec_mono (lookup_tables_loop_spec iterInst points ops hit hps (alloc.vec.Vec.new _)
    (by simpa using hlen))
  rintro r ⟨hnone, hsome⟩
  refine ⟨hnone, fun v hv => ?_⟩
  obtain ⟨zs, hr, hzs⟩ := hsome v hv
  simpa [hr] using hzs

end «VartimeMultiscalarMulStrausEdwardsPointi686-tables».optional_multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

private theorem optional_multiscalar_mul_loop0_loop0_eq
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»))
    (i : Usize) (t : CompletedPoint.«i686-tables») (n k : Usize) :
    optional_multiscalar_mul_loop0_loop0 nafs lookup_tables i t n k =
      EdwardsOps.I686Tables.strausLoop00 nafs lookup_tables i t n k := by
  unfold optional_multiscalar_mul_loop0_loop0 EdwardsOps.strausLoop00
  congr 1

private theorem optional_multiscalar_mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»))
    (r : ProjectivePoint.«i686-tables») :
    optional_multiscalar_mul_loop0 iter nafs lookup_tables r =
      EdwardsOps.I686Tables.strausLoop0 iter nafs lookup_tables r := by
  unfold optional_multiscalar_mul_loop0 EdwardsOps.strausLoop0
  congr 1

/-- The outer loop: after the digit positions `e, …, 255`, the accumulator represents
`∑_{m < n} nafTail d_m e • P_m`. -/
@[local step]
private theorem optional_multiscalar_mul_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»))
    (r : ProjectivePoint.«i686-tables») (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min nafs.length lookup_tables.length)
    (hT : ∀ m < n, lookup_tables.val[m]!.Represents (P m) ∧ lookup_tables.val[m]!.LimbsLt 27)
    (hD : ∀ m < n, ∀ e < 256, (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hr : r.OnCurve) (hrb : r.LimbsLt 26)
    (hrp : r.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! iter.iter.end.val • P m) :
    optional_multiscalar_mul_loop0 iter nafs lookup_tables r
      ⦃ (res : ProjectivePoint.«i686-tables») => res.OnCurve ∧ res.LimbsLt 26 ∧
        res.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! 0 • P m ⦄ := by
  rw [optional_multiscalar_mul_loop0_eq]
  exact EdwardsOps.I686Tables.strausLoop0_spec
    EdwardsOps.I686Tables.addN_spec EdwardsOps.I686Tables.subN_spec
    EdwardsOps.I686Tables.asExtended_spec EdwardsOps.I686Tables.pDouble_spec
    EdwardsOps.I686Tables.cAsProjective_spec iter nafs lookup_tables r P n hn hT hD hstart hend hr
    hrb hrp

open «VartimeMultiscalarMulStrausEdwardsPointi686-tables» in
/-- `Straus::optional_multiscalar_mul`: `none` iff some point is `none` (all points are read);
otherwise `∑ s_i • P_i` over the scalars and points, up to the shorter input (unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with optional_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_scalars hss hxs as ⟨nafs, hnafs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with optional_multiscalar_mul.lookup_tables_spec
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
        ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
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
    step with «ProjectivePointi686-tables».as_extended_spec_point as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnone, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hq, sum_zipWith_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [nafTail_zero, (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).1,
      natCast_zsmul]

end Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

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

end «VartimeMultiscalarMulStrausEdwardsPointx86_64-no-tables».optional_multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

private theorem optional_multiscalar_mul_loop0_loop0_eq
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»))
    (i : Usize) (t : CompletedPoint.«x86_64-no-tables») (n k : Usize) :
    optional_multiscalar_mul_loop0_loop0 nafs lookup_tables i t n k =
      EdwardsOps.X86NoTables.strausLoop00 nafs lookup_tables i t n k := by
  unfold optional_multiscalar_mul_loop0_loop0 EdwardsOps.strausLoop00
  congr 1

private theorem optional_multiscalar_mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»))
    (r : ProjectivePoint.«x86_64-no-tables») :
    optional_multiscalar_mul_loop0 iter nafs lookup_tables r =
      EdwardsOps.X86NoTables.strausLoop0 iter nafs lookup_tables r := by
  unfold optional_multiscalar_mul_loop0 EdwardsOps.strausLoop0
  congr 1

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
  rw [optional_multiscalar_mul_loop0_eq]
  exact EdwardsOps.X86NoTables.strausLoop0_spec
    EdwardsOps.X86NoTables.addN_spec EdwardsOps.X86NoTables.subN_spec
    EdwardsOps.X86NoTables.asExtended_spec EdwardsOps.X86NoTables.pDouble_spec
    EdwardsOps.X86NoTables.cAsProjective_spec iter nafs lookup_tables r P n hn hT hD hstart hend hr
    hrb hrp

open «VartimeMultiscalarMulStrausEdwardsPointx86_64-no-tables» in
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
  step with optional_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_scalars hss hxs as ⟨nafs, hnafs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with optional_multiscalar_mul.lookup_tables_spec
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

section
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
    (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
    (sub_spec_point)

namespace «VartimeMultiscalarMulStrausEdwardsPointi686-no-tables».optional_multiscalar_mul

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

open window.«NafLookupTable5ProjectiveNielsPointi686-no-tables».Insts in
/-- The loop of `lookup_tables`: pushes the tables of the remaining points; `none` iff one of
them is `none`. -/
private theorem lookup_tables_loop_spec {It : Type}
    (iterInst : core.iter.traits.iterator.Iterator It
        (Option edwards.EdwardsPoint.«i686-no-tables»))
    (points : It) (ops : List (Option edwards.EdwardsPoint.«i686-no-tables»))
    (hit : iterInst.Yields points ops)
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (out : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»))
    (hlen : out.length + ops.length ≤ Usize.max) :
    lookup_tables_loop iterInst points out
      ⦃ (r : Option
          (alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»))) =>
        (r = none ↔ none ∈ ops) ∧ ∀ v, r = some v → ∃ zs, v.val = out.val ++ zs ∧
          List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) (ops.filterMap id)
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
      step with «CoreConvertFromSharedAEdwardsPointi686-no-tables».from_spec
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
        (Option edwards.EdwardsPoint.«i686-no-tables»))
    (points : It) (ops : List (Option edwards.EdwardsPoint.«i686-no-tables»))
    (hit : iterInst.Yields points ops)
    (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve) (hlen : ops.length ≤ Usize.max) :
    lookup_tables iterInst points
      ⦃ (r : Option
          (alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»))) =>
        (r = none ↔ none ∈ ops) ∧ ∀ v, r = some v →
          List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27)
            (ops.filterMap id) v.val ⦄ := by
  unfold lookup_tables
  apply spec_mono (lookup_tables_loop_spec iterInst points ops hit hps (alloc.vec.Vec.new _)
    (by simpa using hlen))
  rintro r ⟨hnone, hsome⟩
  refine ⟨hnone, fun v hv => ?_⟩
  obtain ⟨zs, hr, hzs⟩ := hsome v hv
  simpa [hr] using hzs

end «VartimeMultiscalarMulStrausEdwardsPointi686-no-tables».optional_multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

private theorem optional_multiscalar_mul_loop0_loop0_eq
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»))
    (i : Usize) (t : CompletedPoint.«i686-no-tables») (n k : Usize) :
    optional_multiscalar_mul_loop0_loop0 nafs lookup_tables i t n k =
      EdwardsOps.I686NoTables.strausLoop00 nafs lookup_tables i t n k := by
  unfold optional_multiscalar_mul_loop0_loop0 EdwardsOps.strausLoop00
  congr 1

private theorem optional_multiscalar_mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»))
    (r : ProjectivePoint.«i686-no-tables») :
    optional_multiscalar_mul_loop0 iter nafs lookup_tables r =
      EdwardsOps.I686NoTables.strausLoop0 iter nafs lookup_tables r := by
  unfold optional_multiscalar_mul_loop0 EdwardsOps.strausLoop0
  congr 1

/-- The outer loop: after the digit positions `e, …, 255`, the accumulator represents
`∑_{m < n} nafTail d_m e • P_m`. -/
@[local step]
private theorem optional_multiscalar_mul_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»))
    (r : ProjectivePoint.«i686-no-tables») (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min nafs.length lookup_tables.length)
    (hT : ∀ m < n, lookup_tables.val[m]!.Represents (P m) ∧ lookup_tables.val[m]!.LimbsLt 27)
    (hD : ∀ m < n, ∀ e < 256, (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hr : r.OnCurve) (hrb : r.LimbsLt 26)
    (hrp : r.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! iter.iter.end.val • P m) :
    optional_multiscalar_mul_loop0 iter nafs lookup_tables r
      ⦃ (res : ProjectivePoint.«i686-no-tables») => res.OnCurve ∧ res.LimbsLt 26 ∧
        res.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! 0 • P m ⦄ := by
  rw [optional_multiscalar_mul_loop0_eq]
  exact EdwardsOps.I686NoTables.strausLoop0_spec
    EdwardsOps.I686NoTables.addN_spec EdwardsOps.I686NoTables.subN_spec
    EdwardsOps.I686NoTables.asExtended_spec EdwardsOps.I686NoTables.pDouble_spec
    EdwardsOps.I686NoTables.cAsProjective_spec iter nafs lookup_tables r P n hn hT hD hstart hend hr
    hrb hrp

open «VartimeMultiscalarMulStrausEdwardsPointi686-no-tables» in
/-- `Straus::optional_multiscalar_mul`: `none` iff some point is `none` (all points are read);
otherwise `∑ s_i • P_i` over the scalars and points, up to the shorter input (unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-no-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with optional_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_scalars hss hxs as ⟨nafs, hnafs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with optional_multiscalar_mul.lookup_tables_spec
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
        ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
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
    step with «ProjectivePointi686-no-tables».as_extended_spec_point as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnone, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hq, sum_zipWith_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [nafTail_zero, (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).1,
      natCast_zsmul]

end Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

end

end Curve25519Dalek.backend.serial.scalar_mul.straus
