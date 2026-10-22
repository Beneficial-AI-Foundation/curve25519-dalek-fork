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
import Proofs.Edwards.Identity
import Proofs.Edwards.MulByPow2
import Proofs.Helpers.Cmp
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.AsRadix16
import Proofs.Window.LookupTableFrom
import Proofs.Window.LookupTableSelect
import Zeroize
public section

/-! # `Straus::multiscalar_mul`

Constant-time Straus: the lookup tables of `P, 2 P, …, 8 P` of the points, the radix-`16` digits
of the scalars, and Horner's rule over the `64` digit positions, adding `d_i[j] • P_i` for every
point (up to the shorter of the two inputs, as the patched index loop) after `16 •` the
accumulator. The inputs are `IntoIterator`s (`IntoIterator.Yields`) whose items are borrowed as
scalars and points. -/

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

/-- One digit position: `16 •` the sum, plus the digits, is the sum of the next tails. -/
private theorem horner16 (n j : ℕ) (d : ℕ → Array I8 64#usize) (P : ℕ → curve25519.edwards.Point)
    (hj : j < 64) :
    2 ^ 4 • (∑ k ∈ Finset.range n, radix16Tail (d k) (j + 1) • P k) +
      ∑ k ∈ Finset.range n, (d k)[j]!.val • P k =
      ∑ k ∈ Finset.range n, radix16Tail (d k) j • P k := by
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [radix16Tail_eq _ _ hj, ← natCast_zsmul, smul_smul, ← add_smul, add_comm]
  push_cast
  ring_nf

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
    (add_spec_point)

namespace «MultiscalarMulStrausEdwardsPointx86_64-tables».multiscalar_mul

open window.«LookupTableProjectiveNielsPointx86_64-tables».Insts in
/-- The points' lookup tables. -/
@[local step]
private theorem lookup_tables_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«x86_64-tables»)
    (points : It) (ys : List Clause0_Item) (hit : iterInst.Yields points ys)
    (ps : List edwards.EdwardsPoint.«x86_64-tables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : edwards.EdwardsPoint.«x86_64-tables») => P' = P ⦄) ys
          ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hlen : ys.length ≤ Usize.max) :
    lookup_tables iterInst borrowInst points
      ⦃ (r : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-tables»)) =>
        List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) ps r.val ⦄ := by
  unfold lookup_tables lookup_tables_loop
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPointx86_64-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) points ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec
      P (hps P hP).1 (hps P hP).2) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

/-- The scalars' radix-`16` digits. -/
@[local step]
private theorem scalar_digits_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    scalar_digits iterInst borrowInst scalars
      ⦃ (r : alloc.vec.Vec (Array I8 64#usize)) =>
        List.Forall₂ (fun s d => d.asInt 4 = s.asNat ∧
          ∀ i < 64, -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8) ss r.val ⦄ := by
  unfold scalar_digits scalar_digits_loop
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow scalar.Scalar.as_radix_16
    (fun s d => d.asInt 4 = s.asNat ∧ ∀ i < 64, -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8)
    scalars xs hit ss hborrow (fun s hs => spec_mono (scalar.Scalar.as_radix_16_spec s (hss s hs))
      fun d ⟨hval, hlow, h63l, h63u⟩ => ⟨hval, fun i hi => by
        rcases Nat.lt_or_ge i 63 with h | h
        · exact ⟨(hlow i h).1, (hlow i h).2.le⟩
        · rw [show i = 63 by omega]; exact ⟨h63l, h63u⟩⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end «MultiscalarMulStrausEdwardsPointx86_64-tables».multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables»

open scoped Helpers.IndexStep in
/-- The inner loop: adds `d_k[j] • P_k` for `k = i, …, n - 1`. -/
@[local step]
private theorem multiscalar_mul_loop0_loop0_spec
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize)) (Q : edwards.EdwardsPoint.«x86_64-tables»)
    (j n i : Usize) (P : ℕ → curve25519.edwards.Point) (hj : j.val < 64)
    (hn : n.val ≤ lookup_tables.length ∧ n.val ≤ scalar_digits.length)
    (hT : ∀ k < n.val, lookup_tables.val[k]!.Represents (P k) ∧ lookup_tables.val[k]!.LimbsLt 54)
    (hD : ∀ k < n.val, ∀ e < 64, -8 ≤ (scalar_digits.val[k]!)[e]!.val ∧
      (scalar_digits.val[k]!)[e]!.val ≤ 8)
    (hi : i.val ≤ n.val) (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    multiscalar_mul_loop0_loop0 lookup_tables scalar_digits Q j n i
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») => r.OnCurve ∧ r.LimbsLt 52 ∧
        r.toPoint = Q.toPoint + ∑ k ∈ Finset.Ico i.val n.val,
          (scalar_digits.val[k]!)[j.val]!.val • P k ⦄ := by
  unfold multiscalar_mul_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (Q', i') => i.val ≤ i'.val ∧ i'.val ≤ n.val ∧ Q'.OnCurve ∧ Q'.LimbsLt 52 ∧
      Q'.toPoint = Q.toPoint + ∑ k ∈ Finset.Ico i.val i'.val,
        (scalar_digits.val[k]!)[j.val]!.val • P k)
  · rintro ⟨Q', i'⟩ ⟨hii, hin, hQ'on, hQ'b, hQ'p⟩
    unfold multiscalar_mul_loop0_loop0.body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      have hk : i'.val < n.val := hlt
      step as ⟨lt, hlt'⟩
      step as ⟨d, hd⟩
      rw [← getElem!_pos] at hlt' hd
      step as ⟨x, hx⟩
      obtain ⟨hrep, hb⟩ := hT i'.val hk
      step with window.«LookupTableProjectiveNielsPointx86_64-tables».select_spec lt x (P i'.val)
        (hlt' ▸ hb) (hlt' ▸ hrep) (by rw [hx, hd]; exact hD i'.val hk j.val hj)
        as ⟨q, hqon, hq, hqb⟩
      step with add_spec_point Q' q hQ'b hqb hQ'on hqon as ⟨c, hcon, hc, hcb⟩
      step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨Q1, hQ1on, hQ1, hQ1b⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by scalar_tac, hQ1on, hQ1b, ?_, by scalar_tac⟩
      rw [hQ1, hc, hQ'p, hq, hx, hd, show i1.val = i'.val + 1 by scalar_tac,
        Finset.sum_Ico_succ_top hii, add_assoc]
    · simp only [hlt, ite_false, WP.spec_ok]
      have : i'.val = n.val := by scalar_tac
      exact ⟨hQ'on, hQ'b, this ▸ hQ'p⟩
  · exact ⟨le_refl _, hi, hon, hQ, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The outer loop: after the digit positions `e, …, 63`, the accumulator represents
`∑_{k < n} radix16Tail d_k e • P_k`. -/
@[local step]
private theorem multiscalar_mul_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize)) (Q : edwards.EdwardsPoint.«x86_64-tables»)
    (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min scalar_digits.length lookup_tables.length)
    (hT : ∀ k < n, lookup_tables.val[k]!.Represents (P k) ∧ lookup_tables.val[k]!.LimbsLt 54)
    (hD : ∀ k < n, ∀ e < 64, -8 ≤ (scalar_digits.val[k]!)[e]!.val ∧
      (scalar_digits.val[k]!)[e]!.val ≤ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 64)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve)
    (hQp : Q.toPoint = ∑ k ∈ Finset.range n,
      radix16Tail scalar_digits.val[k]! iter.iter.end.val • P k) :
    multiscalar_mul_loop0 iter lookup_tables scalar_digits Q
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») => r.OnCurve ∧ r.LimbsLt 52 ∧
        r.toPoint = ∑ k ∈ Finset.range n, radix16Tail scalar_digits.val[k]! 0 • P k ⦄ := by
  unfold multiscalar_mul_loop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, Q') => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 64 ∧ Q'.OnCurve ∧
      Q'.LimbsLt 52 ∧ Q'.toPoint = ∑ k ∈ Finset.range n,
        radix16Tail scalar_digits.val[k]! it.iter.end.val • P k)
  · rintro ⟨it, Q'⟩ ⟨hst, hen, hQ'on, hQ'b, hQ'p⟩
    unfold multiscalar_mul_loop0.body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, j, ho, hj, hstart1, hend1⟩
      subst ho
      step with edwards.«EdwardsPointx86_64-tables».mul_by_pow_2_spec Q' 4#u32 hQ'b hQ'on
          (by decide)
        as ⟨Q1, hQ1on, hQ1, hQ1b⟩
      step as ⟨m, hm⟩
      have hmn : m.val = n := by rw [hn]; scalar_tac
      step with multiscalar_mul_loop0_loop0_spec lookup_tables scalar_digits Q1 j m 0#usize P
        (by scalar_tac) (by scalar_tac) (hmn ▸ hT) (hmn ▸ hD) (by scalar_tac) hQ1b hQ1on
        as ⟨Q2, hQ2on, hQ2b, hQ2⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, hQ2on, hQ2b, ?_, by scalar_tac⟩
      rw [hQ2, hQ1, hQ'p, hmn, ← Finset.range_eq_Ico,
        hend1, ← hj, horner16 n j.val (fun k => scalar_digits.val[k]!) P (by scalar_tac)]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at hQ'p
      exact ⟨hQ'on, hQ'b, hQ'p⟩
  · exact ⟨hstart, hend, hon, hQ, hQp⟩

/-- `Straus::multiscalar_mul`: `∑ s_i • P_i` over the scalars and points the two inputs yield,
up to the shorter one (unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«x86_64-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«x86_64-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«x86_64-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  unfold multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  step with hpoints' as ⟨it, hit⟩
  step with «MultiscalarMulStrausEdwardsPointx86_64-tables».multiscalar_mul.lookup_tables_spec _ _
      it ys
    hit ps hborrow_points hps hys as ⟨tables, htables⟩
  step with hscalars' as ⟨it1, hit1⟩
  step with «MultiscalarMulStrausEdwardsPointx86_64-tables».multiscalar_mul.scalar_digits_spec _ _
      it1
    xs hit1 ss hborrow_scalars hss hxs as ⟨digits, hdigits⟩
  step with
      edwards.EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨Q, hQon, hQ, hQb⟩
  step as ⟨iter, hiter⟩
  obtain ⟨hTlen, hT⟩ := forall₂_getElem! htables
  obtain ⟨hDlen, hD⟩ := forall₂_getElem! hdigits
  have hn : min ss.length ps.length = min digits.length tables.length := by
    rw [hTlen, hDlen]
  step with multiscalar_mul_loop0_spec iter tables digits Q (fun k => ps[k]!.toPoint)
    (min ss.length ps.length) hn
    (fun k hk => hT k (by have := min_le_right ss.length ps.length; omega))
    (fun k hk => (hD k (by have := min_le_left ss.length ps.length; omega)).2)
    (by rw [hiter]; rfl) (by rw [hiter]; decide) hQb hQon
    (by
      rw [hQ, hiter]
      exact (Finset.sum_eq_zero fun k _ => by
        rw [show ({ start := 0#usize, «end» := 64#usize } : core.ops.range.Range Usize).end.val
          = 64 from rfl, radix16Tail_sixtyFour, zero_smul]).symm)
    as ⟨r, hron, hrb, hr⟩
  have hzer : ∀ x ∈ digits.val, (Array.Insts.ZeroizeZeroize 64#usize
      (zeroize.Zeroize.Blanket I8.Insts.ZeroizeDefaultIsZeroes)).zeroize x ⦃ _ => True ⦄ :=
    fun x _ => spec_mono (_root_.Array.Insts.ZeroizeZeroize.zeroize_spec (post := fun _ => True) _ x
      fun y _ => spec_mono (I8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec y) fun _ _ => trivial)
      fun _ _ => trivial
  step with alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec _ _ hzer as ⟨z, hz⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, sum_zipWith_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [radix16Tail_zero, (hD k (by have := min_le_left ss.length ps.length; omega)).1,
    natCast_zsmul]

end Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables»

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    (add_spec_point)

namespace «MultiscalarMulStrausEdwardsPointx86_64-no-tables».multiscalar_mul

open window.«LookupTableProjectiveNielsPointx86_64-no-tables».Insts in
/-- The points' lookup tables. -/
@[local step]
private theorem lookup_tables_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«x86_64-no-tables»)
    (points : It) (ys : List Clause0_Item) (hit : iterInst.Yields points ys)
    (ps : List edwards.EdwardsPoint.«x86_64-no-tables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : edwards.EdwardsPoint.«x86_64-no-tables») => P' = P ⦄)
          ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hlen : ys.length ≤ Usize.max) :
    lookup_tables iterInst borrowInst points
      ⦃ (r : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-no-tables»)) =>
        List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) ps r.val ⦄ := by
  unfold lookup_tables lookup_tables_loop
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) points ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from_spec
      P (hps P hP).1 (hps P hP).2) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

/-- The scalars' radix-`16` digits. -/
@[local step]
private theorem scalar_digits_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    scalar_digits iterInst borrowInst scalars
      ⦃ (r : alloc.vec.Vec (Array I8 64#usize)) =>
        List.Forall₂ (fun s d => d.asInt 4 = s.asNat ∧
          ∀ i < 64, -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8) ss r.val ⦄ := by
  unfold scalar_digits scalar_digits_loop
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow scalar.Scalar.as_radix_16
    (fun s d => d.asInt 4 = s.asNat ∧ ∀ i < 64, -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8)
    scalars xs hit ss hborrow (fun s hs => spec_mono (scalar.Scalar.as_radix_16_spec s (hss s hs))
      fun d ⟨hval, hlow, h63l, h63u⟩ => ⟨hval, fun i hi => by
        rcases Nat.lt_or_ge i 63 with h | h
        · exact ⟨(hlow i h).1, (hlow i h).2.le⟩
        · rw [show i = 63 by omega]; exact ⟨h63l, h63u⟩⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end «MultiscalarMulStrausEdwardsPointx86_64-no-tables».multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables»

open scoped Helpers.IndexStep in
/-- The inner loop: adds `d_k[j] • P_k` for `k = i, …, n - 1`. -/
@[local step]
private theorem multiscalar_mul_loop0_loop0_spec
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-no-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
        (Q : edwards.EdwardsPoint.«x86_64-no-tables»)
    (j n i : Usize) (P : ℕ → curve25519.edwards.Point) (hj : j.val < 64)
    (hn : n.val ≤ lookup_tables.length ∧ n.val ≤ scalar_digits.length)
    (hT : ∀ k < n.val, lookup_tables.val[k]!.Represents (P k) ∧ lookup_tables.val[k]!.LimbsLt 54)
    (hD : ∀ k < n.val, ∀ e < 64, -8 ≤ (scalar_digits.val[k]!)[e]!.val ∧
      (scalar_digits.val[k]!)[e]!.val ≤ 8)
    (hi : i.val ≤ n.val) (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    multiscalar_mul_loop0_loop0 lookup_tables scalar_digits Q j n i
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») => r.OnCurve ∧ r.LimbsLt 52 ∧
        r.toPoint = Q.toPoint + ∑ k ∈ Finset.Ico i.val n.val,
          (scalar_digits.val[k]!)[j.val]!.val • P k ⦄ := by
  unfold multiscalar_mul_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (Q', i') => i.val ≤ i'.val ∧ i'.val ≤ n.val ∧ Q'.OnCurve ∧ Q'.LimbsLt 52 ∧
      Q'.toPoint = Q.toPoint + ∑ k ∈ Finset.Ico i.val i'.val,
        (scalar_digits.val[k]!)[j.val]!.val • P k)
  · rintro ⟨Q', i'⟩ ⟨hii, hin, hQ'on, hQ'b, hQ'p⟩
    unfold multiscalar_mul_loop0_loop0.body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      have hk : i'.val < n.val := hlt
      step as ⟨lt, hlt'⟩
      step as ⟨d, hd⟩
      rw [← getElem!_pos] at hlt' hd
      step as ⟨x, hx⟩
      obtain ⟨hrep, hb⟩ := hT i'.val hk
      step with window.«LookupTableProjectiveNielsPointx86_64-no-tables».select_spec lt x (P i'.val)
        (hlt' ▸ hb) (hlt' ▸ hrep) (by rw [hx, hd]; exact hD i'.val hk j.val hj)
        as ⟨q, hqon, hq, hqb⟩
      step with add_spec_point Q' q hQ'b hqb hQ'on hqon as ⟨c, hcon, hc, hcb⟩
      step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨Q1, hQ1on, hQ1, hQ1b⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by scalar_tac, hQ1on, hQ1b, ?_, by scalar_tac⟩
      rw [hQ1, hc, hQ'p, hq, hx, hd, show i1.val = i'.val + 1 by scalar_tac,
        Finset.sum_Ico_succ_top hii, add_assoc]
    · simp only [hlt, ite_false, WP.spec_ok]
      have : i'.val = n.val := by scalar_tac
      exact ⟨hQ'on, hQ'b, this ▸ hQ'p⟩
  · exact ⟨le_refl _, hi, hon, hQ, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The outer loop: after the digit positions `e, …, 63`, the accumulator represents
`∑_{k < n} radix16Tail d_k e • P_k`. -/
@[local step]
private theorem multiscalar_mul_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-no-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
        (Q : edwards.EdwardsPoint.«x86_64-no-tables»)
    (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min scalar_digits.length lookup_tables.length)
    (hT : ∀ k < n, lookup_tables.val[k]!.Represents (P k) ∧ lookup_tables.val[k]!.LimbsLt 54)
    (hD : ∀ k < n, ∀ e < 64, -8 ≤ (scalar_digits.val[k]!)[e]!.val ∧
      (scalar_digits.val[k]!)[e]!.val ≤ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 64)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve)
    (hQp : Q.toPoint = ∑ k ∈ Finset.range n,
      radix16Tail scalar_digits.val[k]! iter.iter.end.val • P k) :
    multiscalar_mul_loop0 iter lookup_tables scalar_digits Q
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») => r.OnCurve ∧ r.LimbsLt 52 ∧
        r.toPoint = ∑ k ∈ Finset.range n, radix16Tail scalar_digits.val[k]! 0 • P k ⦄ := by
  unfold multiscalar_mul_loop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, Q') => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 64 ∧ Q'.OnCurve ∧
      Q'.LimbsLt 52 ∧ Q'.toPoint = ∑ k ∈ Finset.range n,
        radix16Tail scalar_digits.val[k]! it.iter.end.val • P k)
  · rintro ⟨it, Q'⟩ ⟨hst, hen, hQ'on, hQ'b, hQ'p⟩
    unfold multiscalar_mul_loop0.body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, j, ho, hj, hstart1, hend1⟩
      subst ho
      step with edwards.«EdwardsPointx86_64-no-tables».mul_by_pow_2_spec Q' 4#u32 hQ'b hQ'on
          (by decide)
        as ⟨Q1, hQ1on, hQ1, hQ1b⟩
      step as ⟨m, hm⟩
      have hmn : m.val = n := by rw [hn]; scalar_tac
      step with multiscalar_mul_loop0_loop0_spec lookup_tables scalar_digits Q1 j m 0#usize P
        (by scalar_tac) (by scalar_tac) (hmn ▸ hT) (hmn ▸ hD) (by scalar_tac) hQ1b hQ1on
        as ⟨Q2, hQ2on, hQ2b, hQ2⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, hQ2on, hQ2b, ?_, by scalar_tac⟩
      rw [hQ2, hQ1, hQ'p, hmn, ← Finset.range_eq_Ico,
        hend1, ← hj, horner16 n j.val (fun k => scalar_digits.val[k]!) P (by scalar_tac)]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at hQ'p
      exact ⟨hQ'on, hQ'b, hQ'p⟩
  · exact ⟨hstart, hend, hon, hQ, hQp⟩

open edwards.EdwardsPoint.«x86_64-no-tables».Insts in
/-- `Straus::multiscalar_mul`: `∑ s_i • P_i` over the scalars and points the two inputs yield,
up to the shorter one (unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«x86_64-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«x86_64-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«x86_64-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  unfold multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  step with hpoints' as ⟨it, hit⟩
  step with «MultiscalarMulStrausEdwardsPointx86_64-no-tables».multiscalar_mul.lookup_tables_spec _
      _ it ys
    hit ps hborrow_points hps hys as ⟨tables, htables⟩
  step with hscalars' as ⟨it1, hit1⟩
  step with «MultiscalarMulStrausEdwardsPointx86_64-no-tables».multiscalar_mul.scalar_digits_spec _
      _ it1
    xs hit1 ss hborrow_scalars hss hxs as ⟨digits, hdigits⟩
  step with Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨Q, hQon, hQ, hQb⟩
  step as ⟨iter, hiter⟩
  obtain ⟨hTlen, hT⟩ := forall₂_getElem! htables
  obtain ⟨hDlen, hD⟩ := forall₂_getElem! hdigits
  have hn : min ss.length ps.length = min digits.length tables.length := by
    rw [hTlen, hDlen]
  step with multiscalar_mul_loop0_spec iter tables digits Q (fun k => ps[k]!.toPoint)
    (min ss.length ps.length) hn
    (fun k hk => hT k (by have := min_le_right ss.length ps.length; omega))
    (fun k hk => (hD k (by have := min_le_left ss.length ps.length; omega)).2)
    (by rw [hiter]; rfl) (by rw [hiter]; decide) hQb hQon
    (by
      rw [hQ, hiter]
      exact (Finset.sum_eq_zero fun k _ => by
        rw [show ({ start := 0#usize, «end» := 64#usize } : core.ops.range.Range Usize).end.val
          = 64 from rfl, radix16Tail_sixtyFour, zero_smul]).symm)
    as ⟨r, hron, hrb, hr⟩
  have hzer : ∀ x ∈ digits.val, (Array.Insts.ZeroizeZeroize 64#usize
      (zeroize.Zeroize.Blanket I8.Insts.ZeroizeDefaultIsZeroes)).zeroize x ⦃ _ => True ⦄ :=
    fun x _ => spec_mono (_root_.Array.Insts.ZeroizeZeroize.zeroize_spec (post := fun _ => True) _ x
      fun y _ => spec_mono (I8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec y) fun _ _ => trivial)
      fun _ _ => trivial
  step with alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec _ _ hzer as ⟨z, hz⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, sum_zipWith_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [radix16Tail_zero, (hD k (by have := min_le_left ss.length ps.length; omega)).1,
    natCast_zsmul]

end Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables»

end

end Curve25519Dalek.backend.serial.scalar_mul.straus
