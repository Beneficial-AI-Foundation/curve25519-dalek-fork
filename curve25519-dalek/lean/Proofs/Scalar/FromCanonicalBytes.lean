/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Target
public import Curve25519.Basic
public import Subtle
import Subtle.Lemmas
import Proofs.Helpers.Scalar
import Proofs.Scalar.IsCanonical
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem from_canonical_bytes_spec (bytes : Array U8 32#usize) (htgt : OnX86_64) :
    from_canonical_bytes bytes ⦃ (r : subtle.CtOption Scalar) =>
      r.is_some.IsValid ∧ r.value.bytes = bytes ∧
      (bytes.asNat 8 < L → r.is_some = 1#u8) ∧ (L ≤ bytes.asNat 8 → r.is_some = 0#u8) ⦄ := by
  unfold from_canonical_bytes
  step*
  subst r_post
  refine ⟨c1_post, rfl, fun h => ?_, fun h => ?_⟩
  · have hi : i.val < 2 ^ 5 := by
      have h31 := Scalar.bytes_31_val ⟨bytes⟩
      have hL : Scalar.asNat ⟨bytes⟩ < 2 ^ 253 := h.trans L_lt
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD] at h31
      rw [List.getElem?_eq_getElem (by simp), Option.getD_some] at h31
      rw [i_post]
      omega
    have hi1 : i1 = 0#u8 := by
      apply UScalar.eq_of_val_eq
      rw [i1_post, Nat.shiftRight_eq_div_pow]
      simp only [UScalar.ofNatCore_val_eq]
      omega
    rw [c1_post1, high_bit_unset_post1, ite_eq_left hi1, c_post1 h]
    rfl
  · rw [c1_post1, c_post2 h]
    rcases high_bit_unset_post with hb | hb <;> rw [hb] <;> rfl

end Curve25519Dalek.scalar.Scalar
