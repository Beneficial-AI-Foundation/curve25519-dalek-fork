/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Backend.Serial.CurveModels.AddAffineNiels
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.CompletedAsProjective
import Proofs.Backend.Serial.CurveModels.ProjectiveAsExtended
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Backend.Serial.CurveModels.ProjectiveIdentity
import Proofs.Backend.Serial.CurveModels.SubAffineNiels
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointPoint
import Proofs.Helpers.Iterator
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Scalar.NonAdjacentForm
import Proofs.Window.NafLookupTable5From
import Proofs.Window.NafLookupTable5Select
import Proofs.Window.NafLookupTable8Select
import Proofs.Backend.Serial.U64.Constants.AffineOddMultiplesOfBasepoint
public section

/-! # `vartime_double_base::mul`

`a • A + b • B` for the basepoint `B`, in variable time: the non-adjacent forms of `a` (width
`5`) and `b` (width `8` with the precomputed table `AFFINE_ODD_MULTIPLES_OF_BASEPOINT` in the
`x86_64-tables` configuration, width `5` with a table built from `ED25519_BASEPOINT_POINT`
otherwise), Horner's rule from the highest nonzero digit down, adding `d • A` and `d • B` for
each nonzero digit from the tables of odd multiples. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.vartime_double_base

/-- One step of Horner's rule on two points. -/
private theorem horner_step (x y d e : ℤ) (A B : curve25519.edwards.Point) :
    2 • (x • A + y • B) + d • A + e • B = (d + 2 * x) • A + (e + 2 * y) • B := by
  rw [smul_add, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, add_smul, add_smul]
  push_cast
  abel

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (sub_spec_point)

namespace «x86_64-tables»

open scoped Helpers.IndexStep in
/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
@[local step]
private theorem mul_loop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    mul.«x86_64-tables_loop0» iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  unfold mul.«x86_64-tables_loop0»
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, j) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ j.val < 256 ∧
      ∀ k, it.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0)
  · rintro ⟨it, j⟩ ⟨hst, hen, hj, hzk⟩
    unfold mul.«x86_64-tables_loop0».body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, e, ho, he, hstart1, hend1⟩
      subst ho
      step as ⟨x, hx⟩
      by_cases hx0 : x.val = 0
      · have hx' : (x != 0#i8) = false := by
          rw [bne_eq_false_iff_eq]; scalar_tac
        simp only [hx', Bool.false_eq_true, ↓reduceIte]
        step as ⟨y, hy⟩
        by_cases hy0 : y.val = 0
        · have hy' : (y != 0#i8) = false := by
            rw [bne_eq_false_iff_eq]; scalar_tac
          simp only [hy', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          refine ⟨by rw [hstart1, hst], by scalar_tac, by scalar_tac, fun k hk hk' => ?_,
            by scalar_tac⟩
          rcases Nat.eq_or_lt_of_le (hend1 ▸ hk) with h | h
          · subst h; exact ⟨hx ▸ hx0, hy ▸ hy0⟩
          · exact hzk k (by omega) hk'
        · have hy' : (y != 0#i8) = true := by
            rw [bne_iff_ne]; intro h; apply hy0; rw [h]; rfl
          simp only [hy', ↓reduceIte, WP.spec_ok]
          exact ⟨by scalar_tac, fun k hk hk' => hzk k (by omega) hk'⟩
      · have hx' : (x != 0#i8) = true := by
          rw [bne_iff_ne]; intro h; apply hx0; rw [h]; rfl
        simp only [hx', ↓reduceIte, WP.spec_ok]
        exact ⟨by scalar_tac, fun k hk hk' => hzk k (by omega) hk'⟩
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      exact ⟨hj, fun k _ hk' => hzk k (by omega) hk'⟩
  · exact ⟨hstart, hend, hi, hz⟩

set_option linter.style.longLine false in
open scoped Helpers.IndexStep in
/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
@[local step]
private theorem mul_loop1_spec (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«x86_64-tables»)
    (r : ProjectivePoint.«x86_64-tables») (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt 54)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt 54)
    (ha : ∀ k < 256, a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧ 2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k < 256, b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧ 2 * |b_naf[k]!.val| < 2 ^ 8)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    mul.«x86_64-tables_loop1» a_naf b_naf i table_A table_B r
      ⦃ (res : edwards.EdwardsPoint.«x86_64-tables») => res.OnCurve ∧
        res.toPoint = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ res.LimbsLt 52 ⦄ := by
  unfold mul.«x86_64-tables_loop1»
  apply loop.spec_decr_nat (measure := fun (j, _) => j.val)
    (inv := fun (j, q) => j.val < 256 ∧ q.OnCurve ∧ q.LimbsLt 52 ∧
      q.toPoint = nafTail a_naf (j.val + 1) • A + nafTail b_naf (j.val + 1) • B)
  · rintro ⟨j, q⟩ ⟨hj, hq, hqb, hqp⟩
    unfold mul.«x86_64-tables_loop1».body
    step with «ProjectivePointx86_64-tables».double_spec_point as ⟨t, hton, htp, htb⟩
    step as ⟨d, hd⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
    apply spec_bind (Pₘ := fun t1 => t1.OnCurve ∧ t1.toPoint = t.toPoint + d.val • A ∧
      t1.LimbsLt 54)
    · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (ha j.val hj (by rw [← hd]; omega))
        rw [← hd, abs_of_neg hneg] at hk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable5.select_spec (P := A) _ table_A i2 hAb hA
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with sub_spec_point ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
        refine ⟨ht1on, ?_, ht1b⟩
        rw [ht1p, hep, show ProjectiveNielsPoint.«x86_64-tables».toPoint pnp = PointRepr.toPoint pnp
            from rfl, hpp]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        rw [hzero, zero_smul, add_zero]
        exact ⟨hton, rfl, htb⟩
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (ha j.val hj (by rw [← hd]; omega))
        rw [← hd, abs_of_pos hpos] at hk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable5.select_spec (P := A) _ table_A i1 hAb hA
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with add_spec_point ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
        refine ⟨ht1on, ?_, ht1b⟩
        rw [ht1p, hep, show ProjectiveNielsPoint.«x86_64-tables».toPoint pnp = PointRepr.toPoint pnp
            from rfl, hpp]
        exact add_nsmul_eq _ _ _ _ (by omega)
    rintro t1 ⟨ht1on, ht1p, ht1b⟩
    step as ⟨e, he⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp e 0#i8) = ok (compare e.val 0) from rfl, bind_ok]
    apply spec_bind (Pₘ := fun t2 => t2.OnCurve ∧ t2.toPoint = t1.toPoint + e.val • B ∧
      t2.LimbsLt 54)
    · rcases lt_trichotomy e.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 8) (by norm_num) (hb j.val hj (by rw [← he]; omega))
        rw [← he, abs_of_neg hneg] at hk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable8.select_spec (P := B) _ table_B i2 hBb hB
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with
            «CoreOpsArithSubSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables».sub_spec_point
          ep pnp hepb hpb hepon hpon as ⟨t2, ht2on, ht2p, ht2b⟩
        refine ⟨ht2on, ?_, ht2b⟩
        rw [ht2p, hep, show AffineNielsPoint.«x86_64-tables».toPoint pnp = PointRepr.toPoint pnp
            from rfl, hpp]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        rw [hzero, zero_smul, add_zero]
        exact ⟨ht1on, rfl, ht1b⟩
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 8) (by norm_num) (hb j.val hj (by rw [← he]; omega))
        rw [← he, abs_of_pos hpos] at hk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable8.select_spec (P := B) _ table_B i1 hBb hB
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with
            «CoreOpsArithAddSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables».add_spec_point
          ep pnp hepb hpb hepon hpon as ⟨t2, ht2on, ht2p, ht2b⟩
        refine ⟨ht2on, ?_, ht2b⟩
        rw [ht2p, hep, show AffineNielsPoint.«x86_64-tables».toPoint pnp = PointRepr.toPoint pnp
            from rfl, hpp]
        exact add_nsmul_eq _ _ _ _ (by omega)
    rintro t2 ⟨ht2on, ht2p, ht2b⟩
    step with «CompletedPointx86_64-tables».as_projective_spec_point as ⟨r1, hr1on, hr1p, hr1b⟩
    have hval : r1.toPoint = nafTail a_naf j.val • A + nafTail b_naf j.val • B := by
      rw [hr1p, ht2p, ht1p, htp, hqp, horner_step, nafTail_eq _ _ hj, nafTail_eq _ _ hj, ← hd, ← he]
    split
    · step with «ProjectivePointx86_64-tables».as_extended_spec_point as ⟨res, hreson, hresp, hresb⟩
      have hj0 : j.val = 0 := by scalar_tac
      refine ⟨hreson, ?_, hresb⟩
      rw [hresp, hval, hj0]
    · step as ⟨j1, hj1⟩
      have hj1' : j1.val + 1 = j.val := by scalar_tac
      refine ⟨by scalar_tac, hr1on, hr1b, ?_, by scalar_tac⟩
      rw [hval, hj1']
  · exact ⟨hi, hr, hrb, hrp⟩

set_option linter.style.longLine false in
open scoped Helpers.IndexStep in
/-- `vartime_double_base::mul`: `a • A + b • B` for the basepoint `B` (unreduced scalars
`< 2^255`, the precondition of `non_adjacent_form`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«x86_64-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    mul.«x86_64-tables» a A b ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul.«x86_64-tables»
  step as ⟨a_naf, haval, hadig, hanaf⟩
  step as ⟨b_naf, hbval, hbdig, hbnaf⟩
  step as ⟨iter, hiter⟩
  step with mul_loop0_spec iter a_naf b_naf 255#usize (by rw [hiter]; rfl) (by rw [hiter]; decide)
    (by decide) (fun k hk hk' => absurd hk' (by rw [hiter] at hk; simp at hk; omega))
    as ⟨i, hi, hz⟩
  step with
      window.«NafLookupTable5ProjectiveNielsPointx86_64-tables».Insts.«CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec
    as ⟨tA, htA, htAb⟩
  step as ⟨tB, htB, htBb⟩
  step with ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail a_naf (i.val + 1) • A.toPoint +
      nafTail b_naf (i.val + 1) • basepoint := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2, zero_smul, zero_smul, add_zero]
  step with mul_loop1_spec a_naf b_naf i tA tB r A.toPoint basepoint htA htAb htB htBb
    (fun k hk h => hadig k hk h) (fun k hk h => hbdig k hk h) hi hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  refine ⟨hreson, ?_, hresb⟩
  rw [hresp, nafTail_zero, nafTail_zero, haval, hbval, natCast_zsmul, natCast_zsmul]

end «x86_64-tables»

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
  (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
  (sub_spec_point)

namespace «x86_64-no-tables»

open scoped Helpers.IndexStep in
/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
@[local step]
private theorem mul_loop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    mul.«x86_64-no-tables_loop0» iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  unfold mul.«x86_64-no-tables_loop0»
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, j) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ j.val < 256 ∧
      ∀ k, it.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0)
  · rintro ⟨it, j⟩ ⟨hst, hen, hj, hzk⟩
    unfold mul.«x86_64-no-tables_loop0».body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, e, ho, he, hstart1, hend1⟩
      subst ho
      step as ⟨x, hx⟩
      by_cases hx0 : x.val = 0
      · have hx' : (x != 0#i8) = false := by
          rw [bne_eq_false_iff_eq]; scalar_tac
        simp only [hx', Bool.false_eq_true, ↓reduceIte]
        step as ⟨y, hy⟩
        by_cases hy0 : y.val = 0
        · have hy' : (y != 0#i8) = false := by
            rw [bne_eq_false_iff_eq]; scalar_tac
          simp only [hy', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          refine ⟨by rw [hstart1, hst], by scalar_tac, by scalar_tac, fun k hk hk' => ?_,
            by scalar_tac⟩
          rcases Nat.eq_or_lt_of_le (hend1 ▸ hk) with h | h
          · subst h; exact ⟨hx ▸ hx0, hy ▸ hy0⟩
          · exact hzk k (by omega) hk'
        · have hy' : (y != 0#i8) = true := by
            rw [bne_iff_ne]; intro h; apply hy0; rw [h]; rfl
          simp only [hy', ↓reduceIte, WP.spec_ok]
          exact ⟨by scalar_tac, fun k hk hk' => hzk k (by omega) hk'⟩
      · have hx' : (x != 0#i8) = true := by
          rw [bne_iff_ne]; intro h; apply hx0; rw [h]; rfl
        simp only [hx', ↓reduceIte, WP.spec_ok]
        exact ⟨by scalar_tac, fun k hk hk' => hzk k (by omega) hk'⟩
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      exact ⟨hj, fun k _ hk' => hzk k (by omega) hk'⟩
  · exact ⟨hstart, hend, hi, hz⟩

open scoped Helpers.IndexStep in
/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
@[local step]
private theorem mul_loop1_spec (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A table_B : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»)
    (r : ProjectivePoint.«x86_64-no-tables») (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt 54)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt 54)
    (ha : ∀ k < 256, a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧ 2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k < 256, b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧ 2 * |b_naf[k]!.val| < 2 ^ 5)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    mul.«x86_64-no-tables_loop1» a_naf b_naf i table_A table_B r
      ⦃ (res : edwards.EdwardsPoint.«x86_64-no-tables») => res.OnCurve ∧
        res.toPoint = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ res.LimbsLt 52 ⦄ := by
  unfold mul.«x86_64-no-tables_loop1»
  apply loop.spec_decr_nat (measure := fun (j, _) => j.val)
    (inv := fun (j, q) => j.val < 256 ∧ q.OnCurve ∧ q.LimbsLt 52 ∧
      q.toPoint = nafTail a_naf (j.val + 1) • A + nafTail b_naf (j.val + 1) • B)
  · rintro ⟨j, q⟩ ⟨hj, hq, hqb, hqp⟩
    unfold mul.«x86_64-no-tables_loop1».body
    step with «ProjectivePointx86_64-no-tables».double_spec_point as ⟨t, hton, htp, htb⟩
    step as ⟨d, hd⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
    apply spec_bind (Pₘ := fun t1 => t1.OnCurve ∧ t1.toPoint = t.toPoint + d.val • A ∧
      t1.LimbsLt 54)
    · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (ha j.val hj (by rw [← hd]; omega))
        rw [← hd, abs_of_neg hneg] at hk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable5.select_spec (P := A) _ table_A i2 hAb hA
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with sub_spec_point ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
        refine ⟨ht1on, ?_, ht1b⟩
        rw [ht1p, hep, show ProjectiveNielsPoint.«x86_64-no-tables».toPoint pnp = PointRepr.toPoint
            pnp from rfl, hpp]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        rw [hzero, zero_smul, add_zero]
        exact ⟨hton, rfl, htb⟩
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (ha j.val hj (by rw [← hd]; omega))
        rw [← hd, abs_of_pos hpos] at hk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable5.select_spec (P := A) _ table_A i1 hAb hA
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with add_spec_point ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
        refine ⟨ht1on, ?_, ht1b⟩
        rw [ht1p, hep, show ProjectiveNielsPoint.«x86_64-no-tables».toPoint pnp = PointRepr.toPoint
            pnp from rfl, hpp]
        exact add_nsmul_eq _ _ _ _ (by omega)
    rintro t1 ⟨ht1on, ht1p, ht1b⟩
    step as ⟨e, he⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp e 0#i8) = ok (compare e.val 0) from rfl, bind_ok]
    apply spec_bind (Pₘ := fun t2 => t2.OnCurve ∧ t2.toPoint = t1.toPoint + e.val • B ∧
      t2.LimbsLt 54)
    · rcases lt_trichotomy e.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (hb j.val hj (by rw [← he]; omega))
        rw [← he, abs_of_neg hneg] at hk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable5.select_spec (P := B) _ table_B i2 hBb hB
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with sub_spec_point ep pnp hepb hpb hepon hpon as ⟨t2, ht2on, ht2p, ht2b⟩
        refine ⟨ht2on, ?_, ht2b⟩
        rw [ht2p, hep, show ProjectiveNielsPoint.«x86_64-no-tables».toPoint pnp = PointRepr.toPoint
            pnp from rfl, hpp]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        rw [hzero, zero_smul, add_zero]
        exact ⟨ht1on, rfl, ht1b⟩
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (hb j.val hj (by rw [← he]; omega))
        rw [← he, abs_of_pos hpos] at hk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable5.select_spec (P := B) _ table_B i1 hBb hB
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with add_spec_point ep pnp hepb hpb hepon hpon as ⟨t2, ht2on, ht2p, ht2b⟩
        refine ⟨ht2on, ?_, ht2b⟩
        rw [ht2p, hep, show ProjectiveNielsPoint.«x86_64-no-tables».toPoint pnp = PointRepr.toPoint
            pnp from rfl, hpp]
        exact add_nsmul_eq _ _ _ _ (by omega)
    rintro t2 ⟨ht2on, ht2p, ht2b⟩
    step with «CompletedPointx86_64-no-tables».as_projective_spec_point as ⟨r1, hr1on, hr1p, hr1b⟩
    have hval : r1.toPoint = nafTail a_naf j.val • A + nafTail b_naf j.val • B := by
      rw [hr1p, ht2p, ht1p, htp, hqp, horner_step, nafTail_eq _ _ hj, nafTail_eq _ _ hj, ← hd, ← he]
    split
    · step with «ProjectivePointx86_64-no-tables».as_extended_spec_point as
        ⟨res, hreson, hresp, hresb⟩
      have hj0 : j.val = 0 := by scalar_tac
      refine ⟨hreson, ?_, hresb⟩
      rw [hresp, hval, hj0]
    · step as ⟨j1, hj1⟩
      have hj1' : j1.val + 1 = j.val := by scalar_tac
      refine ⟨by scalar_tac, hr1on, hr1b, ?_, by scalar_tac⟩
      rw [hval, hj1']
  · exact ⟨hi, hr, hrb, hrp⟩

set_option linter.style.longLine false in
open scoped Helpers.IndexStep in
/-- `vartime_double_base::mul`: `a • A + b • B` for the basepoint `B` (unreduced scalars
`< 2^255`, the precondition of `non_adjacent_form`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«x86_64-no-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    mul.«x86_64-no-tables» a A b ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul.«x86_64-no-tables»
  step as ⟨a_naf, haval, hadig, hanaf⟩
  step as ⟨b_naf, hbval, hbdig, hbnaf⟩
  step as ⟨iter, hiter⟩
  step with mul_loop0_spec iter a_naf b_naf 255#usize (by rw [hiter]; rfl) (by rw [hiter]; decide)
    (by decide) (fun k hk hk' => absurd hk' (by rw [hiter] at hk; simp at hk; omega))
    as ⟨i, hi, hz⟩
  step with
      window.«NafLookupTable5ProjectiveNielsPointx86_64-no-tables».Insts.«CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from_spec
    as ⟨tA, htA, htAb⟩
  step with backend.serial.u64.constants.«x86_64-no-tables».ED25519_BASEPOINT_POINT_spec_point
    as ⟨bp, hbpon, hbp, hbpb⟩
  step with
      window.«NafLookupTable5ProjectiveNielsPointx86_64-no-tables».Insts.«CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from_spec
    as ⟨tB, htB, htBb⟩
  step with
      ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail a_naf (i.val + 1) • A.toPoint +
      nafTail b_naf (i.val + 1) • bp.toPoint := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2, zero_smul, zero_smul, add_zero]
  step with mul_loop1_spec a_naf b_naf i tA tB r A.toPoint bp.toPoint htA htAb htB htBb
    (fun k hk h => hadig k hk h) (fun k hk h => hbdig k hk h) hi hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  refine ⟨hreson, ?_, hresb⟩
  rw [hresp, nafTail_zero, nafTail_zero, haval, hbval, hbp, natCast_zsmul, natCast_zsmul]

end «x86_64-no-tables»

end
end Curve25519Dalek.backend.serial.scalar_mul.vartime_double_base
