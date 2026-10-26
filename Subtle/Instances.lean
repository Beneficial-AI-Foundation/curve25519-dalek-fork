/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
@[expose] public section
open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-! # `subtle` for the trait instances generated in `Curve25519Dalek/Funs.lean` (no axioms)

The generic specs of `Subtle/Contract.lean` for `[T]` and `[T; N]` take the element instance's
contract as a hypothesis, and `step` cannot discharge that by itself. These versions are
specialised to the `u8` instances (used by `CompressedEdwardsY`, `CompressedRistretto`,
`MontgomeryPoint` and `Scalar`), so `step*` fires on them.
-/

namespace Curve25519Dalek

/-- `ct_eq` on byte slices: `Choice(1)` iff the slices are equal. -/
@[step] theorem Slice.Insts.SubtleConstantTimeEq.ct_eq_U8_spec (a b : Slice Std.U8) :
    _root_.Slice.Insts.SubtleConstantTimeEq.ct_eq U8.Insts.SubtleConstantTimeEq a b ⦃ c =>
      c.IsValid ∧ (a = b → c = 1#u8) ∧ (a ≠ b → c = 0#u8) ⦄ :=
  _root_.Slice.Insts.SubtleConstantTimeEq.ct_eq_spec _
    (fun x y => spec_mono (U8.Insts.SubtleConstantTimeEq.ct_eq_spec x y) (by grind)) a b

/-- `conditional_select` on byte arrays, for a valid choice. -/
@[step] theorem Array.Insts.SubtleConditionallySelectable.conditional_select_U8_spec
    {N : Std.Usize} (a b : Array Std.U8 N) (c : subtle.Choice) (hc : c.IsValid) :
    _root_.Array.Insts.SubtleConditionallySelectable.conditional_select
      U8.Insts.SubtleConditionallySelectable a b c ⦃ r =>
      (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄ :=
  _root_.Array.Insts.SubtleConditionallySelectable.conditional_select_spec _ a b c hc
    (fun x y => U8.Insts.SubtleConditionallySelectable.conditional_assign_spec x y c hc)

end Curve25519Dalek
