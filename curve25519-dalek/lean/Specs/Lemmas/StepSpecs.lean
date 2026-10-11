/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Specs.Lemmas.Array
public import Specs.Lemmas.Bitwise
public section

/-! # Opt-in `step` specifications

Alternative `step` specifications for library functions, registered as scoped attributes so that a
proof activates them with `open scoped …`. They are registered once, here: re-registering a `step`
theorem in a file that imports another registration triggers a warning. -/

open Aeneas Aeneas.Std

/- Array and slice reads described with `getElem!`. -/
namespace Specs.IndexStep
attribute [scoped step] Array.index_usize_getElem!_spec Slice.index_usize_getElem!_spec
end Specs.IndexStep

/- Array updates described with `getElem!`. -/
namespace Specs.UpdateStep
attribute [scoped step] Array.update_getElem!_spec
end Specs.UpdateStep

/- `index_usize` on array literals, with the result as a list element. -/
namespace Specs.MakeStep
attribute [scoped step] Array.index_usize_make_spec
end Specs.MakeStep

/- Masking with `2 ^ n - 1` as reduction modulo `2 ^ n` (`n` is inferred from a local
hypothesis `m.val = 2 ^ n - 1`). -/
namespace Specs.MaskStep
attribute [scoped step] UScalar.and_two_pow_sub_one_spec
end Specs.MaskStep
