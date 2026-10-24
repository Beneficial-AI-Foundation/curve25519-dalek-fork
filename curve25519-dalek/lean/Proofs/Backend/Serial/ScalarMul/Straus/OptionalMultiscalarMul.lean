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
public import Proofs.Backend.Serial.ScalarMul.Straus.OptionalMultiscalarMulGeneric
public section

/-! # `Straus::optional_multiscalar_mul`

Variable-time Straus: the width-`5` non-adjacent forms of the scalars, the tables of odd
multiples of the points (`None` as soon as a point is `None`, as the patched helper), and
Horner's rule in base `2` over the `256` digit positions, adding `d • P_i` for each nonzero digit
(up to the shorter of the two inputs). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

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
