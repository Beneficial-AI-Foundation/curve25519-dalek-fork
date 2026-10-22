/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Types
@[expose] public section
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek

/-! # Consistency witness for the `zeroize` axiom (not trusted, no axioms)

Concrete models of the four opaque `zeroize` functions. Each model satisfies its field of
`zeroize.Contract` in `Zeroize/Basic.lean`, with the opaque constant replaced by the model.
Replacing each opaque constant by its model therefore turns the axiom `RustAx.zeroize` into a
theorem, so it is satisfiable: it cannot prove `False`.
-/

namespace ZeroizeModel

/-- Model of `zeroize::{impl Zeroize for Z}::zeroize`. Like Rust, it ignores the old value. -/
@[nolint unusedArguments]
def blanket {Z : Type} (inst : zeroize.DefaultIsZeroes Z) (_x : Z) : Result Z :=
  inst.coredefaultDefaultInst.default

/-- Model of `zeroize::{impl Zeroize for IterMut<'_, Z>}::zeroize`. -/
def iterMut {Z : Type} (inst : zeroize.Zeroize Z) (it : core.slice.iter.IterMut Z) :
    Result ((core.slice.iter.IterMut Z) ×
      (core.slice.iter.IterMut Z → core.slice.iter.IterMut Z)) := do
  let rest ← List.mapM_with_length inst.zeroize (it.slice.val.drop it.i)
  let slice : Slice Z :=
    .from (it.slice.val.take it.i ++ rest.val) (by
      have h := rest.property
      have := it.slice.property
      simp only [List.length_append, List.length_take, List.length_drop] at h ⊢
      scalar_tac)
  ok ({ slice, i := slice.length }, id)

/-- Model of `zeroize::{impl Zeroize for [Z; N]}::zeroize`. -/
def array {Z : Type} {N : Std.Usize} (inst : zeroize.Zeroize Z) (a : Array Z N) :
    Result (Array Z N) := do
  let (s, to_slice_mut_back) ← lift (Array.to_slice_mut a)
  let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
  let (im1, zeroize_back) ← iterMut inst im
  ok (to_slice_mut_back (iter_mut_back (zeroize_back im1)))

/-- Model of `zeroize::{impl Zeroize for Vec<Z>}::zeroize`. -/
def vec {Z : Type} (inst : zeroize.Zeroize Z) (v : alloc.vec.Vec Z) :
    Result (alloc.vec.Vec Z) := do
  let (im, _) ← core.slice.Slice.iter_mut v.slice
  let _ ← iterMut inst im
  ok (alloc.vec.Vec.new Z)

theorem blanket_eq {Z : Type} (inst : zeroize.DefaultIsZeroes Z) (x : Z) :
    blanket inst x = inst.coredefaultDefaultInst.default := rfl

theorem iterMut_spec {Z : Type} (inst : zeroize.Zeroize Z) (it : core.slice.iter.IterMut Z)
    {post : Z → Prop} (h : ∀ x ∈ it.slice.val.drop it.i, inst.zeroize x ⦃ post ⦄) :
    iterMut inst it ⦃ it' back =>
      back = id ∧ it'.i = it.slice.length ∧ it'.slice.length = it.slice.length ∧
      it'.slice.val.take it.i = it.slice.val.take it.i ∧
      ∀ y ∈ it'.slice.val.drop it.i, post y ⦄ := by
  unfold iterMut
  apply spec_bind (List.mapM_with_length_spec (post := fun _ y => post y)
    (fun i hi => h _ (List.getElem_mem hi)))
  intro rest hrest
  have hlen := rest.property
  have hi : it.i ≤ it.slice.val.length ∨ it.slice.val.length < it.i := by scalar_tac
  simp only [List.length_drop] at hlen
  simp only [spec_ok, Slice.from_val, Slice.length]
  simp only [uncurry', Slice.from_val, List.length_append, List.length_take, hlen, true_and]
  rcases hi with hi | hi
  · refine ⟨by scalar_tac, by scalar_tac, ?_, ?_⟩
    · rw [List.take_append]; simp [Nat.min_eq_left hi]
    · intro y hy
      rw [List.drop_append_of_le_length (by simp only [List.length_take]; scalar_tac)] at hy
      simp only [List.length_take, hi, inf_of_le_left, Std.le_refl, List.drop_of_length_le,
        List.nil_append] at hy
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      exact hrest j hj
  · have : rest.val = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
    simp_all
    omega

theorem array_spec {Z : Type} {N : Std.Usize} (inst : zeroize.Zeroize Z) (a : Array Z N)
    {post : Z → Prop} (h : ∀ x ∈ a.val, inst.zeroize x ⦃ post ⦄) :
    array inst a ⦃ a' => ∀ y ∈ a'.val, post y ⦄ := by
  unfold array
  simp only [lift, Array.to_slice_mut, core.slice.Slice.iter_mut, bind_ok]
  apply spec_bind (iterMut_spec inst _ (post := post) (by simpa [Array.to_slice] using h))
  rintro ⟨it, back⟩ ⟨rfl, -, hlen, -, hpost⟩
  refine (spec_ok _).mpr ?_
  simp only [id]
  have hlen' : it.slice.val.length = N.val := by
    simpa [Slice.length, Array.to_slice] using hlen
  rw [Array.from_slice_val _ _ hlen']
  simpa [Array.to_slice] using hpost

theorem vec_spec {Z : Type} (inst : zeroize.Zeroize Z) (v : alloc.vec.Vec Z)
    (h : ∀ x ∈ v.val, inst.zeroize x ⦃ _ => True ⦄) :
    vec inst v ⦃ v' => v' = alloc.vec.Vec.new Z ⦄ := by
  unfold vec
  simp only [core.slice.Slice.iter_mut, bind_ok]
  apply spec_bind (iterMut_spec inst _ (post := fun _ => True)
    (by simpa [alloc.vec.Vec.val] using h))
  intro _ _
  simp [spec_ok]

end ZeroizeModel
