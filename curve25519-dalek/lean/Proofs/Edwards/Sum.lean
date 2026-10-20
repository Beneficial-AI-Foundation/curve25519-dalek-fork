/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
import Proofs.Edwards.Add
import Proofs.Edwards.Identity
public section

/-! # `Sum for EdwardsPoint`

The patched loop (`while let Some(item) = iter.next()`) adds the borrowed items to the identity.
The iterator is described by `Iterator.Yields` and `borrow` by its results on the yielded items,
as for `Sum for Scalar`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace CoreIterTraitsAccumSum

open «CoreOpsArithAddSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
  (add_spec_point)

/-- The loop of `sum` adds the remaining items to the accumulator. -/
private theorem sum_loop_spec {T I : Type}
    (borrowInst : core.borrow.Borrow T EdwardsPoint.«x86_64-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (hiter : iterInst.Yields iter xs) (ps : List EdwardsPoint.«x86_64-tables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«x86_64-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.Bounded) (hps_on : ∀ P ∈ ps, P.OnCurve)
    (acc : EdwardsPoint.«x86_64-tables») (hacc : acc.Bounded) (hacc_on : acc.OnCurve) :
    sum_loop borrowInst iterInst iter acc ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = acc.toPoint + (ps.map (·.toPoint)).sum ∧ r.Bounded ⦄ := by
  induction hiter generalizing acc ps with
  | nil hnext =>
    cases hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp [hacc_on, hacc]
  | cons hnext _ ih =>
    obtain _ | ⟨hb, hrest⟩ := hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with hb as ⟨P, hP⟩
    subst hP
    step with add_spec_point acc P hacc (hps P List.mem_cons_self) hacc_on
      (hps_on P List.mem_cons_self) as ⟨acc1, hacc1on, hacc1, hacc1b⟩
    apply WP.spec_mono (ih _ hrest (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ => hps_on Q (List.mem_cons_of_mem _ hQ)) acc1 hacc1b hacc1on)
    rintro r ⟨hron, hr, hrb⟩
    refine ⟨hron, ?_, hrb⟩
    rw [hr, hacc1, List.map_cons, List.sum_cons, add_assoc]

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`);
limbs `< 2^52`. -/
@[step]
theorem sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«x86_64-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«x86_64-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«x86_64-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.Bounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.Bounded ⦄ := by
  unfold sum
  step with Curve25519_dalekTraitsIdentity.identity_spec_point as ⟨acc, hacc_on, hacc, haccb⟩
  apply WP.spec_mono (sum_loop_spec borrowInst iterInst iter xs hiter ps hborrow hps hps_on acc
    haccb hacc_on)
  rintro r ⟨hron, hr, hrb⟩
  exact ⟨hron, by rw [hr, hacc, zero_add], hrb⟩

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace CoreIterTraitsAccumSum

open «CoreOpsArithAddSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
  (add_spec_point)

/-- The loop of `sum` adds the remaining items to the accumulator. -/
private theorem sum_loop_spec {T I : Type}
    (borrowInst : core.borrow.Borrow T EdwardsPoint.«x86_64-no-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (hiter : iterInst.Yields iter xs) (ps : List EdwardsPoint.«x86_64-no-tables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«x86_64-no-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.Bounded) (hps_on : ∀ P ∈ ps, P.OnCurve)
    (acc : EdwardsPoint.«x86_64-no-tables») (hacc : acc.Bounded) (hacc_on : acc.OnCurve) :
    sum_loop borrowInst iterInst iter acc ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = acc.toPoint + (ps.map (·.toPoint)).sum ∧ r.Bounded ⦄ := by
  induction hiter generalizing acc ps with
  | nil hnext =>
    cases hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp [hacc_on, hacc]
  | cons hnext _ ih =>
    obtain _ | ⟨hb, hrest⟩ := hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with hb as ⟨P, hP⟩
    subst hP
    step with add_spec_point acc P hacc (hps P List.mem_cons_self) hacc_on
      (hps_on P List.mem_cons_self) as ⟨acc1, hacc1on, hacc1, hacc1b⟩
    apply WP.spec_mono (ih _ hrest (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ => hps_on Q (List.mem_cons_of_mem _ hQ)) acc1 hacc1b hacc1on)
    rintro r ⟨hron, hr, hrb⟩
    refine ⟨hron, ?_, hrb⟩
    rw [hr, hacc1, List.map_cons, List.sum_cons, add_assoc]

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`);
limbs `< 2^52`. -/
@[step]
theorem sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«x86_64-no-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«x86_64-no-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«x86_64-no-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.Bounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.Bounded ⦄ := by
  unfold sum
  step with Curve25519_dalekTraitsIdentity.identity_spec_point as ⟨acc, hacc_on, hacc, haccb⟩
  apply WP.spec_mono (sum_loop_spec borrowInst iterInst iter xs hiter ps hborrow hps hps_on acc
    haccb hacc_on)
  rintro r ⟨hron, hr, hrb⟩
  exact ⟨hron, by rw [hr, hacc, zero_add], hrb⟩

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts


