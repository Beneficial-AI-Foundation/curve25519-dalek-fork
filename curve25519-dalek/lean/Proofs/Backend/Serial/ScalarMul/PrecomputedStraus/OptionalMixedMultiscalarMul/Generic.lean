/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
public import Proofs.Helpers.EdwardsOps.Instances
public import Proofs.Helpers.Naf
public import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.OptionalMixedMultiscalarMul.Lemmas
import Proofs.Helpers.Iterator
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Window.NafLookupTable5Select
import Proofs.Window.NafLookupTable8Select
public section

/-! # `optional_mixed_multiscalar_mul`'s loops, over a configuration's point operations

The three loops of `VartimePrecomputedStraus::optional_mixed_multiscalar_mul`, over the
`EdwardsOps` of a configuration: the four configurations' loops are `rfl`-equal to these, and their
specs follow (`OptionalMixedMultiscalarMul/X86Tables.lean`, …). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.EdwardsOps

open Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

variable (O : EdwardsOps)

open ControlFlow

/-- `optional_mixed_multiscalar_mul_loop0_loop0.body` over the point operations. -/
@[expose] def pstLoop00Body (dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (j : Usize)
    (iter : core.ops.range.Range Usize) (R : O.C) :
    Result (ControlFlow ((core.ops.range.Range Usize) × O.C) O.C) := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done R)
  | some i =>
    let a ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array I8 256#usize))
        dynamic_nafs i
    let digit ← Array.index_usize a j
    let o1 ← lift (core.cmp.impls.OrdI8.cmp digit 0#i8)
    match o1 with
    | Ordering.lt =>
      let ep ← O.asExtended R
      let nlt ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (window.NafLookupTable5 O.N))
          dynamic_lookup_tables i
      let i1 ← -. digit
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN nlt i2
      let R1 ← O.subN ep pnp
      ok (cont (iter1, R1))
    | Ordering.eq => ok (cont (iter1, R))
    | Ordering.gt =>
      let ep ← O.asExtended R
      let nlt ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (window.NafLookupTable5 O.N))
          dynamic_lookup_tables i
      let i1 ← lift (IScalar.hcast .Usize digit)
      let pnp ← window.NafLookupTable5.select O.copyN nlt i1
      let R1 ← O.addN ep pnp
      ok (cont (iter1, R1))

/-- `optional_mixed_multiscalar_mul_loop0_loop0` over the point operations. -/
@[expose] def pstLoop00 (iter : core.ops.range.Range Usize)
    (dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (j : Usize) (R : O.C) :
    Result O.C := do
  loop (fun (iter1, R1) => O.pstLoop00Body dynamic_nafs dynamic_lookup_tables j iter1 R1) (iter, R)

/-- `optional_mixed_multiscalar_mul_loop0_loop1.body` over the point operations. -/
@[expose] def pstLoop01Body (v : alloc.vec.Vec (window.NafLookupTable8 O.An))
    (static_nafs : alloc.vec.Vec (Array I8 256#usize)) (j : Usize)
    (iter : core.ops.range.Range Usize) (R : O.C) :
    Result (ControlFlow ((core.ops.range.Range Usize) × O.C) O.C) := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done R)
  | some i =>
    let a ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array I8 256#usize))
        static_nafs i
    let digit ← Array.index_usize a j
    let o1 ← lift (core.cmp.impls.OrdI8.cmp digit 0#i8)
    match o1 with
    | Ordering.lt =>
      let ep ← O.asExtended R
      let nlt ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (window.NafLookupTable8 O.An))
          v i
      let i1 ← -. digit
      let i2 ← lift (IScalar.hcast .Usize i1)
      let anp ← window.NafLookupTable8.select O.copyA nlt i2
      let R1 ← O.subA ep anp
      ok (cont (iter1, R1))
    | Ordering.eq => ok (cont (iter1, R))
    | Ordering.gt =>
      let ep ← O.asExtended R
      let nlt ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (window.NafLookupTable8 O.An))
          v i
      let i1 ← lift (IScalar.hcast .Usize digit)
      let anp ← window.NafLookupTable8.select O.copyA nlt i1
      let R1 ← O.addA ep anp
      ok (cont (iter1, R1))

/-- `optional_mixed_multiscalar_mul_loop0_loop1` over the point operations. -/
@[expose] def pstLoop01 (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (window.NafLookupTable8 O.An))
    (static_nafs : alloc.vec.Vec (Array I8 256#usize)) (j : Usize) (R : O.C) : Result O.C := do
  loop (fun (iter1, R1) => O.pstLoop01Body v static_nafs j iter1 R1) (iter, R)

/-- `optional_mixed_multiscalar_mul_loop0.body` over the point operations. -/
@[expose] def pstLoop0Body (v : alloc.vec.Vec (window.NafLookupTable8 O.An))
    (static_nafs dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (dp : Usize)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (S : O.Pr) :
    Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) × O.Pr)
      O.Pr) := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter
  match o with
  | none => ok (done S)
  | some j =>
    let R ← O.pDouble S
    let R1 ← O.pstLoop00 { start := 0#usize, «end» := dp } dynamic_nafs dynamic_lookup_tables j R
    let i := alloc.vec.Vec.len static_nafs
    let R2 ← O.pstLoop01 { start := 0#usize, «end» := i } v static_nafs j R1
    let S1 ← O.cAsProjective R2
    ok (cont (iter1, S1))

/-- `optional_mixed_multiscalar_mul_loop0` over the point operations. -/
@[expose] def pstLoop0 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (v : alloc.vec.Vec (window.NafLookupTable8 O.An))
    (static_nafs dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (dp : Usize)
    (S : O.Pr) : Result O.Pr := do
  loop (fun (iter1, S1) =>
    O.pstLoop0Body v static_nafs dynamic_nafs dynamic_lookup_tables dp iter1 S1) (iter, S)

open scoped Helpers.IndexStep in
/-- The loop0_loop0 loop over the points `i ∈ [k, n)`: adds `d_i[j] • P_i`. -/
theorem pstLoop00_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec) (hasE : O.AsExtendedSpec)
    (iter : core.ops.range.Range Usize)
    (dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N))
    (j : Usize) (R : O.C) (P : ℕ → curve25519.edwards.Point)
    (hj : j.val < 256)
        (hn : iter.end.val ≤ dynamic_nafs.length ∧ iter.end.val ≤ dynamic_lookup_tables.length)
    (hT : ∀ m < iter.end.val, dynamic_lookup_tables.val[m]!.Represents (P m) ∧
        dynamic_lookup_tables.val[m]!.LimbsLt O.nB)
    (hD : ∀ m < iter.end.val, ∀ e < 256, (dynamic_nafs.val[m]!)[e]!.val ≠ 0 →
      (dynamic_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(dynamic_nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hk : iter.start.val ≤ iter.end.val) (hR : O.cOnCurve R) (hRb : O.cBnd R) :
    O.pstLoop00 iter dynamic_nafs dynamic_lookup_tables j R
      ⦃ (r : O.C) => O.cOnCurve r ∧ O.cBnd r ∧
        O.cToPoint r = O.cToPoint R + ∑ m ∈ Finset.Ico iter.start.val iter.end.val,
          (dynamic_nafs.val[m]!)[j.val]!.val • P m ⦄ := by
  unfold pstLoop00
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, R') => it.end = iter.end ∧ iter.start.val ≤ it.start.val ∧
      it.start.val ≤ iter.end.val ∧ O.cOnCurve R' ∧ O.cBnd R' ∧
      O.cToPoint R' = O.cToPoint R + ∑ m ∈ Finset.Ico iter.start.val it.start.val,
        (dynamic_nafs.val[m]!)[j.val]!.val • P m)
  · rintro ⟨it, R'⟩ ⟨hend, hst, hle, hR'on, hR'b, hR'p⟩
    unfold pstLoop00Body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      have hm : it.start.val < iter.end.val := hend ▸ hlt
      obtain ⟨hrep, hb⟩ := hT it.start.val hm
      step as ⟨a, ha⟩
      rw [← getElem!_pos] at ha
      step as ⟨d, hd⟩
      have hstep : ∀ R1 : O.C, O.cOnCurve R1 → O.cBnd R1 →
          O.cToPoint R1 = O.cToPoint R' + d.val • P it.start.val →
          it1.end = iter.end ∧ iter.start.val ≤ it1.start.val ∧ it1.start.val ≤ iter.end.val ∧
          O.cOnCurve R1 ∧ O.cBnd R1 ∧
          O.cToPoint R1 = O.cToPoint R + ∑ m ∈ Finset.Ico iter.start.val it1.start.val,
            (dynamic_nafs.val[m]!)[j.val]!.val • P m ∧
          it1.end.val - it1.start.val < it.end.val - it.start.val := by
        intro R1 h1on h1b h1p
        refine ⟨hend1.trans hend, by scalar_tac, by scalar_tac, h1on, h1b, ?_, by scalar_tac⟩
        rw [h1p, hR'p, hstart1, Finset.sum_Ico_succ_top hst, add_assoc, hd, ha]
      rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
      rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with hasE R' hR'b hR'on as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 5) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_neg hneg] at hdk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable5.select_spec (P := P it.start.val) _ tab i2
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with hsubN ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show O.nToPoint q = PointRepr.toPoint q from rfl, hq]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        exact hstep R' hR'on hR'b (by rw [hzero, zero_smul, add_zero])
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with hasE R' hR'b hR'on as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 5) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_pos hpos] at hdk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable5.select_spec (P := P it.start.val) _ tab i1
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with haddN ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show O.nToPoint q = PointRepr.toPoint q from rfl, hq]
        exact add_nsmul_eq _ _ _ _ (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : it.start.val = iter.end.val := by rw [← hend]; scalar_tac
      exact ⟨hR'on, hR'b, this ▸ hR'p⟩
  · exact ⟨rfl, le_refl _, hk, hR, hRb, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

open scoped Helpers.IndexStep in
/-- The loop0_loop1 loop over the points `i ∈ [k, n)`: adds `d_i[j] • P_i`. -/
theorem pstLoop01_spec (haddA : O.AddASpec) (hsubA : O.SubASpec) (hasE : O.AsExtendedSpec)
    (iter : core.ops.range.Range Usize)
    (static_nafs : alloc.vec.Vec (Array I8 256#usize))
    (v : alloc.vec.Vec (window.NafLookupTable8 O.An))
    (j : Usize) (R : O.C) (P : ℕ → curve25519.edwards.Point)
    (hj : j.val < 256) (hn : iter.end.val ≤ static_nafs.length ∧ iter.end.val ≤ v.length)
    (hT : ∀ m < iter.end.val, v.val[m]!.Represents (P m) ∧ v.val[m]!.LimbsLt O.aB)
    (hD : ∀ m < iter.end.val, ∀ e < 256, (static_nafs.val[m]!)[e]!.val ≠ 0 →
      (static_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(static_nafs.val[m]!)[e]!.val| < 2 ^ 8)
    (hk : iter.start.val ≤ iter.end.val) (hR : O.cOnCurve R) (hRb : O.cBnd R) :
    O.pstLoop01 iter v static_nafs j R
      ⦃ (r : O.C) => O.cOnCurve r ∧ O.cBnd r ∧
        O.cToPoint r = O.cToPoint R + ∑ m ∈ Finset.Ico iter.start.val iter.end.val,
          (static_nafs.val[m]!)[j.val]!.val • P m ⦄ := by
  unfold pstLoop01
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, R') => it.end = iter.end ∧ iter.start.val ≤ it.start.val ∧
      it.start.val ≤ iter.end.val ∧ O.cOnCurve R' ∧ O.cBnd R' ∧
      O.cToPoint R' = O.cToPoint R + ∑ m ∈ Finset.Ico iter.start.val it.start.val,
        (static_nafs.val[m]!)[j.val]!.val • P m)
  · rintro ⟨it, R'⟩ ⟨hend, hst, hle, hR'on, hR'b, hR'p⟩
    unfold pstLoop01Body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      have hm : it.start.val < iter.end.val := hend ▸ hlt
      obtain ⟨hrep, hb⟩ := hT it.start.val hm
      step as ⟨a, ha⟩
      rw [← getElem!_pos] at ha
      step as ⟨d, hd⟩
      have hstep : ∀ R1 : O.C, O.cOnCurve R1 → O.cBnd R1 →
          O.cToPoint R1 = O.cToPoint R' + d.val • P it.start.val →
          it1.end = iter.end ∧ iter.start.val ≤ it1.start.val ∧ it1.start.val ≤ iter.end.val ∧
          O.cOnCurve R1 ∧ O.cBnd R1 ∧
          O.cToPoint R1 = O.cToPoint R + ∑ m ∈ Finset.Ico iter.start.val it1.start.val,
            (static_nafs.val[m]!)[j.val]!.val • P m ∧
          it1.end.val - it1.start.val < it.end.val - it.start.val := by
        intro R1 h1on h1b h1p
        refine ⟨hend1.trans hend, by scalar_tac, by scalar_tac, h1on, h1b, ?_, by scalar_tac⟩
        rw [h1p, hR'p, hstart1, Finset.sum_Ico_succ_top hst, add_assoc, hd, ha]
      rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
      rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with hasE R' hR'b hR'on as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 8) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_neg hneg] at hdk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable8.select_spec (P := P it.start.val) _ tab i2
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with hsubA ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show O.aToPoint q = PointRepr.toPoint q from rfl, hq]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        exact hstep R' hR'on hR'b (by rw [hzero, zero_smul, add_zero])
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with hasE R' hR'b hR'on as ⟨ep, hepon, hep, hepb⟩
        step as ⟨tab, htab⟩
        rw [← getElem!_pos] at htab
        have hdk := naf_digit_abs (w := 8) (by norm_num)
          (hD it.start.val hm j.val hj (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_pos hpos] at hdk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable8.select_spec (P := P it.start.val) _ tab i1
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with haddA ep q hepb hqb hepon hqon as ⟨R1, h1on, h1p, h1b⟩
        refine hstep R1 h1on h1b ?_
        rw [h1p, hep, show O.aToPoint q = PointRepr.toPoint q from rfl, hq]
        exact add_nsmul_eq _ _ _ _ (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : it.start.val = iter.end.val := by rw [← hend]; scalar_tac
      exact ⟨hR'on, hR'b, this ▸ hR'p⟩
  · exact ⟨rfl, le_refl _, hk, hR, hRb, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The outer loop over the digit positions, from the top. -/
theorem pstLoop0_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec) (haddA : O.AddASpec)
    (hsubA : O.SubASpec) (hasE : O.AsExtendedSpec) (hdbl : O.PDoubleSpec)
    (hasP : O.CAsProjectiveSpec)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (v : alloc.vec.Vec (window.NafLookupTable8 O.An))
    (static_nafs dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N))
    (dp : Usize) (S : O.Pr) (P Q : ℕ → curve25519.edwards.Point)
    (hdp : dp.val ≤ dynamic_nafs.length ∧ dp.val ≤ dynamic_lookup_tables.length)
    (hsl : static_nafs.length ≤ v.length)
    (hT : ∀ m < dp.val, dynamic_lookup_tables.val[m]!.Represents (Q m) ∧
      dynamic_lookup_tables.val[m]!.LimbsLt O.nB)
    (hD : ∀ m < dp.val, ∀ e < 256, (dynamic_nafs.val[m]!)[e]!.val ≠ 0 →
      (dynamic_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(dynamic_nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hV : ∀ m < static_nafs.length, v.val[m]!.Represents (P m) ∧ v.val[m]!.LimbsLt O.aB)
    (hE : ∀ m < static_nafs.length, ∀ e < 256, (static_nafs.val[m]!)[e]!.val ≠ 0 →
      (static_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(static_nafs.val[m]!)[e]!.val| < 2 ^ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hS : O.pOnCurve S) (hSb : O.pBnd S)
    (hSp : O.pToPoint S =
      (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! iter.iter.end.val • Q m) +
        ∑ m ∈ Finset.range static_nafs.length,
          nafTail static_nafs.val[m]! iter.iter.end.val • P m) :
    O.pstLoop0 iter v static_nafs dynamic_nafs dynamic_lookup_tables dp S
      ⦃ (r : O.Pr) => O.pOnCurve r ∧ O.pBnd r ∧ O.pToPoint r =
        (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! 0 • Q m) +
          ∑ m ∈ Finset.range static_nafs.length, nafTail static_nafs.val[m]! 0 • P m ⦄ := by
  unfold pstLoop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, q) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ O.pOnCurve q ∧
      O.pBnd q ∧ O.pToPoint q =
        (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! it.iter.end.val • Q m) +
          ∑ m ∈ Finset.range static_nafs.length,
            nafTail static_nafs.val[m]! it.iter.end.val • P m)
  · rintro ⟨it, q⟩ ⟨hst, hen, hqon, hqb, hqp⟩
    unfold pstLoop0Body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, j, ho, hj, hstart1, hend1⟩
      subst ho
      have hj256 : j.val < 256 := by scalar_tac
      step with hdbl q hqb hqon as ⟨R, hRon, hRp, hRb⟩
      step with O.pstLoop00_spec haddN hsubN hasE
        { start := 0#usize, «end» := dp } dynamic_nafs dynamic_lookup_tables j R Q hj256 hdp hT hD
        (Nat.zero_le _) hRon hRb as ⟨R1, hR1on, hR1b, hR1⟩
      step with O.pstLoop01_spec haddA hsubA hasE
        { start := 0#usize, «end» := alloc.vec.Vec.len static_nafs } static_nafs v j R1 P hj256
        ⟨by simp, by simpa using hsl⟩ (by simpa using hV) (by simpa using hE) (Nat.zero_le _)
        hR1on hR1b as ⟨R2, hR2on, hR2b, hR2⟩
      step with hasP R2 hR2b hR2on as ⟨q1, hq1on, hq1, hq1b⟩
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

end Curve25519Dalek.EdwardsOps
