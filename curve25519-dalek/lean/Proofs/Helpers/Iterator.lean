/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.RangeIter
public import Aeneas.Std.VecIter
public import Defs.Iterator
public section

/-! # Iterators

The iterator over a list (state: the remaining items) yields exactly that list, so specs assuming
`Yields` are not vacuous; so does `Vec::into_iter`. Also the specs of `next` on a reversed `Usize`
range. -/

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace Aeneas.Std.core.iter.adapters.rev.Rev

/-- `next` on a reversed `Usize` range that is not empty yields its last element. -/
theorem next_Usize_some_spec (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (hlt : it.iter.start.val < it.iter.end.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) it
    ⦃ (o : Option Usize) (it' : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) =>
      ∃ e : Usize, o = some e ∧ e.val + 1 = it.iter.end.val ∧ it'.iter.start = it.iter.start ∧
        it'.iter.end = e ⦄ := by
  unfold core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  have hb : (1#usize).val ≤ it.iter.end.val := by scalar_tac
  simp only [core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.backward_checked, hb, ↓reduceDIte,
    bind_tc_ok, core.cmp.impls.PartialOrdUsize.lt, hlt, decide_true, ↓reduceIte, WP.spec_ok]
  exact ⟨_, rfl, by simp only [UScalar.ofNatCore_val_eq]; scalar_tac, rfl, rfl⟩

/-- `next` on an empty reversed `Usize` range yields `none`. -/
theorem next_Usize_none_spec (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (hge : it.iter.end.val ≤ it.iter.start.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) it
    ⦃ (o : Option Usize) (_ : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) =>
      o = none ⦄ := by
  unfold core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  have h_lt : ∀ a b : Usize, core.iter.range.StepUsize.partialOrdInst.lt a b
      = .ok (decide (a.val < b.val)) := fun _ _ => rfl
  simp only [core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back, h_lt,
    show ¬ it.iter.start.val < it.iter.end.val from Nat.not_lt.mpr hge, decide_false,
    Bool.false_eq_true, ↓reduceIte, bind_tc_ok, WP.spec_ok]
  exact rfl

end Aeneas.Std.core.iter.adapters.rev.Rev

namespace Aeneas.Std.core.iter.traits.iterator.Iterator

/-- The iterator over a list: its state is the list of remaining items. -/
def ofList (T : Type) : core.iter.traits.iterator.Iterator (List T) T where
  next l := Result.ok (l.head?, l.tail)

/-- The list iterator yields its list. -/
theorem ofList_yields {T : Type} (l : List T) : (ofList T).Yields l l := by
  induction l with
  | nil => exact .nil (by simp [ofList, spec_ok])
  | cons x xs ih => exact .cons (by simp [ofList, spec_ok]) ih

end Aeneas.Std.core.iter.traits.iterator.Iterator

namespace Aeneas.Std.core.iter.traits.collect

/-- The iterator of a vector yields its entries. -/
theorem IteratorVecIntoIter_yields {T : Type} (l : List T) (v : alloc.vec.Vec T)
    (hv : v.val = l) :
    (core.iter.traits.iterator.IteratorVecIntoIter T).Yields v l := by
  induction l generalizing v with
  | nil =>
    refine .nil ?_
    change alloc.vec.into_iter.IteratorIntoIter.next v ⦃ _ => _ ⦄
    unfold alloc.vec.into_iter.IteratorIntoIter.next
    split
    · simp only [WP.spec_ok]
      rfl
    · rename_i h; rw [hv] at h; cases h
  | cons x xs ih =>
    have hlen : xs.length ≤ Usize.max := by
      have := v.property; rw [hv] at this; simp at this; omega
    refine .cons (it' := alloc.vec.Vec.from xs hlen) ?_ (ih _ (alloc.vec.Vec.from_val xs hlen))
    change alloc.vec.into_iter.IteratorIntoIter.next v ⦃ _ => _ ⦄
    unfold alloc.vec.into_iter.IteratorIntoIter.next
    split
    · rename_i h; rw [hv] at h; cases h
    · rename_i hd tl h
      rw [hv] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      simp only [WP.spec_ok]
      exact ⟨rfl, rfl⟩

/-- `Vec::into_iter` yields the entries of the vector. -/
theorem IntoIteratorVec_yields {T : Type} (v : alloc.vec.Vec T) :
    (IntoIteratorVec T).Yields v v.val := by
  change alloc.vec.IntoIteratorVec.into_iter v ⦃ _ => _ ⦄
  unfold alloc.vec.IntoIteratorVec.into_iter
  exact (WP.spec_ok
    (p := fun it => (core.iter.traits.iterator.IteratorVecIntoIter T).Yields it v.val) v).mpr
    (IteratorVecIntoIter_yields v.val v rfl)

end Aeneas.Std.core.iter.traits.collect
