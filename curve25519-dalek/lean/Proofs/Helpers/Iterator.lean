/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Iterator
public section

/-! # `Iterator.Yields` is satisfiable

The iterator over a list (state: the remaining items) yields exactly that list, so specs assuming
`Yields` are not vacuous. -/

open Aeneas Aeneas.Std Aeneas.Std.WP

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
