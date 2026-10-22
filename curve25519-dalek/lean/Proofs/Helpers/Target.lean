/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Target
public section

/-! # Dispatchers on `get_target`

Every function with per-target variants is translated as the same four-way dispatch on
`get_target`. On an x86_64 target (`OnX86_64`), a spec of the two x86_64 variants is a spec of the
dispatcher (`dispatch_spec`, applied to an `OnX86_64` hypothesis). -/

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace Curve25519Dalek

/-- A four-way dispatch satisfies `P` when `get_target` returns `s₁` or `s₂` and the first two
branches satisfy `P`. The strings need not be distinct. -/
theorem dispatch_spec {α : Type} {P : α → Prop} {s₁ s₂ s₃ : String} {f g h k : Result α}
    (htgt : get_target ⦃ (t : String) => t = s₁ ∨ t = s₂ ⦄) (hf : f ⦃ P ⦄) (hg : g ⦃ P ⦄) :
    (do
      let t ← get_target
      if t = s₁ then f else if t = s₂ then g else if t = s₃ then h else k) ⦃ P ⦄ := by
  apply spec_bind htgt
  rintro t (rfl | rfl)
  · simpa using hf
  · by_cases hts : t = s₁ <;> simp [hts, hf, hg]

end Curve25519Dalek
