/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Vec
public import Defs.Iterator
import Aeneas.Tactic.Step.StepStar
import Proofs.Helpers.Vec
public section

/-! # Generic forms of the collecting loops

The translation patches replace `iter.map(f).collect()` by `while let Some(x) = it.next()`
loops pushing onto a `Vec` (aeneas#1057). They come in three shapes, defined here generically
(the translated loop bodies are definitionally equal to them) with their specs:

- `collectBody`: push each item;
- `collectMapBody`: push `f (borrow x)` for each item `x`;
- `collectOptBody`: for items `Option P`, push `f P`, and stop with `none` at the first `none`.

The iterator is described by `Iterator.Yields`, `borrow` by its results on the items. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP ControlFlow

namespace Curve25519Dalek.collect

variable {It T Y Z : Type}

/-- Push each item of the iterator. -/
@[expose] def collectBody (iterInst : core.iter.traits.iterator.Iterator It T) (it : It)
    (out : alloc.vec.Vec T) : Result (ControlFlow (It × alloc.vec.Vec T) (alloc.vec.Vec T)) := do
  let (o, it1) ← iterInst.next it
  match o with
  | none => ok (done out)
  | some x =>
    let out1 ← alloc.vec.Vec.push out x
    ok (cont (it1, out1))

/-- Push `f (borrow x)` for each item `x` of the iterator. -/
@[expose] def collectMapBody (iterInst : core.iter.traits.iterator.Iterator It T)
    (borrow : T → Result Y) (f : Y → Result Z) (it : It) (out : alloc.vec.Vec Z) :
    Result (ControlFlow (It × alloc.vec.Vec Z) (alloc.vec.Vec Z)) := do
  let (o, it1) ← iterInst.next it
  match o with
  | none => ok (done out)
  | some x =>
    let y ← borrow x
    let z ← f y
    let out1 ← alloc.vec.Vec.push out z
    ok (cont (it1, out1))

/-- For items `Option P`: push `f P`; stop with `none` at the first `none`. -/
@[expose] def collectOptBody (iterInst : core.iter.traits.iterator.Iterator It (Option Y))
    (f : Y → Result Z) (it : It) (out : alloc.vec.Vec Z) :
    Result (ControlFlow (It × alloc.vec.Vec Z) (Option (alloc.vec.Vec Z))) := do
  let (o, it1) ← iterInst.next it
  match o with
  | none => ok (done (some out))
  | some P_opt =>
    match P_opt with
    | none => ok (done none)
    | some P =>
      let z ← f P
      let out1 ← alloc.vec.Vec.push out z
      ok (cont (it1, out1))

theorem collectLoop_spec (iterInst : core.iter.traits.iterator.Iterator It T) (it : It)
    (xs : List T) (hit : iterInst.Yields it xs) (out : alloc.vec.Vec T)
    (hlen : out.length + xs.length ≤ Usize.max) :
    loop (fun ((it1, out1) : It × alloc.vec.Vec T) => collectBody iterInst it1 out1) (it, out)
      ⦃ (r : alloc.vec.Vec T) => r.val = out.val ++ xs ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold loop collectBody
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    unfold loop collectBody
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with alloc.vec.Vec.push_spec out _
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    intro r hr
    rw [hr, hout1, List.append_assoc, List.singleton_append]

theorem collectMapLoop_spec (iterInst : core.iter.traits.iterator.Iterator It T)
    (borrow : T → Result Y) (f : Y → Result Z) (Pf : Y → Z → Prop) (it : It) (xs : List T)
    (hit : iterInst.Yields it xs) (ys : List Y)
    (hborrow : List.Forall₂ (fun x y => borrow x ⦃ (y' : Y) => y' = y ⦄) xs ys)
    (hf : ∀ y ∈ ys, f y ⦃ (z : Z) => Pf y z ⦄) (out : alloc.vec.Vec Z)
    (hlen : out.length + xs.length ≤ Usize.max) :
    loop (fun ((it1, out1) : It × alloc.vec.Vec Z) => collectMapBody iterInst borrow f it1 out1)
      (it, out) ⦃ (r : alloc.vec.Vec Z) =>
        ∃ zs, r.val = out.val ++ zs ∧ List.Forall₂ Pf ys zs ⦄ := by
  induction hit generalizing out ys with
  | nil hnext =>
    cases hborrow
    unfold loop collectMapBody
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    obtain _ | ⟨hb, hrest⟩ := hborrow
    unfold loop collectMapBody
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with hb as ⟨y, hy⟩
    subst hy
    step with hf y List.mem_cons_self as ⟨z, hz⟩
    step with alloc.vec.Vec.push_spec out z
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih (out := out1) _ hrest
      (fun y' hy' => hf y' (List.mem_cons_of_mem _ hy')) (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    rintro r ⟨zs, hr, hzs⟩
    exact ⟨z :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
      List.Forall₂.cons hz hzs⟩

theorem collectOptLoop_spec (iterInst : core.iter.traits.iterator.Iterator It (Option Y))
    (f : Y → Result Z) (Pf : Y → Z → Prop) (it : It) (xs : List (Option Y))
    (hit : iterInst.Yields it xs) (hf : ∀ y, some y ∈ xs → f y ⦃ (z : Z) => Pf y z ⦄)
    (out : alloc.vec.Vec Z) (hlen : out.length + xs.length ≤ Usize.max) :
    loop (fun ((it1, out1) : It × alloc.vec.Vec Z) => collectOptBody iterInst f it1 out1)
      (it, out) ⦃ (r : Option (alloc.vec.Vec Z)) =>
        (r = none ↔ none ∈ xs) ∧
        ∀ v, r = some v → ∃ zs, v.val = out.val ++ zs ∧
          List.Forall₂ Pf (xs.filterMap id) zs ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold loop collectOptBody
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' x xs' hnext _ ih =>
    unfold loop collectOptBody
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    rcases x with _ | y
    · simp
    · step with hf y List.mem_cons_self as ⟨z, hz⟩
      step with alloc.vec.Vec.push_spec out z
        (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
      apply WP.spec_mono (ih (fun y' hy' => hf y' (List.mem_cons_of_mem _ hy')) out1 (by
        rw [alloc.vec.Vec.length_of_val_eq_append hout1]
        simp only [List.length_cons] at hlen; omega))
      rintro r ⟨hnone, hsome⟩
      refine ⟨by simp [hnone], fun v hv => ?_⟩
      obtain ⟨zs, hr, hzs⟩ := hsome v hv
      exact ⟨z :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
        by simpa using List.Forall₂.cons hz hzs⟩

end Curve25519Dalek.collect
