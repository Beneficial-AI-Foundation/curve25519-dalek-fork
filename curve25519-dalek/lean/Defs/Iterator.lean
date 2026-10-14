/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas
@[expose] public section

/-! # Finite iterators (audited)

Specs of functions that consume a generic iterator (`Product`, `Sum`) assume that it yields a
given list of items and then stops. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-- Calling `next` repeatedly, starting from `it`, returns the items `xs` in order, then `none`. -/
inductive Aeneas.Std.core.iter.traits.iterator.Iterator.Yields {I T : Type}
    (inst : core.iter.traits.iterator.Iterator I T) : I → List T → Prop
  | nil {it : I} :
      inst.next it ⦃ (o : Option T) (_ : I) => o = none ⦄ → Yields inst it []
  | cons {it it' : I} {x : T} {xs : List T} :
      inst.next it ⦃ (o : Option T) (it1 : I) => o = some x ∧ it1 = it' ⦄ →
      Yields inst it' xs → Yields inst it (x :: xs)
