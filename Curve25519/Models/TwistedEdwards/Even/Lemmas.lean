/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Models.TwistedEdwards.Even.Defs
import all Curve25519.Models.TwistedEdwards.Even.Defs
import EllipticCurve.TwistedEdwards.Even
import EllipticCurve.TwistedEdwards.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # The Decaf/Ristretto relation on a complete twisted Edwards model: characterising lemmas

The audited statements about `Curve25519.Models.TwistedEdwards.Even.Defs`: the relation `E.Rel`
is an equivalence relation compatible with the group law, and `rel_iff` states it in coordinates,
through the 4-torsion in coordinates (`mem_torsionBy_four_iff` of
`EllipticCurve.TwistedEdwards.Even`). -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F} [E.IsComplete]

/-! ### The relation -/

/-- `E.Rel P Q` unfolds to `P - Q ∈ E.Point[4]`. -/
theorem rel_iff_sub_mem (P Q : E.Point) :
    E.Rel P Q ↔ P - Q ∈ AddSubgroup.torsionBy E.Point 4 :=
  Iff.rfl

theorem rel_refl (P : E.Point) : E.Rel P P := by
  rw [rel_iff_sub_mem, sub_self]
  exact zero_mem _

theorem rel_symm {P Q : E.Point} (h : E.Rel P Q) : E.Rel Q P := by
  rw [rel_iff_sub_mem] at h ⊢
  rw [← neg_sub]
  exact neg_mem h

theorem rel_trans {P Q R : E.Point} (hPQ : E.Rel P Q) (hQR : E.Rel Q R) : E.Rel P R := by
  rw [rel_iff_sub_mem] at hPQ hQR ⊢
  rw [← sub_add_sub_cancel P Q R]
  exact add_mem hPQ hQR

theorem rel_of_eq {P Q : E.Point} (h : P = Q) : E.Rel P Q :=
  h ▸ rel_refl P

/-- `Rel` is compatible with addition. -/
theorem rel_add {P P' Q Q' : E.Point} (hP : E.Rel P P') (hQ : E.Rel Q Q') :
    E.Rel (P + Q) (P' + Q') := by
  rw [rel_iff_sub_mem] at hP hQ ⊢
  rw [add_sub_add_comm]
  exact add_mem hP hQ

/-- `Rel` is compatible with negation. -/
theorem rel_neg {P Q : E.Point} (h : E.Rel P Q) : E.Rel (-P) (-Q) := by
  rw [rel_iff_sub_mem] at h ⊢
  rw [neg_sub_neg, ← neg_sub]
  exact neg_mem h

/-- `Rel` is compatible with subtraction. -/
theorem rel_sub {P P' Q Q' : E.Point} (hP : E.Rel P P') (hQ : E.Rel Q Q') :
    E.Rel (P - Q) (P' - Q') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact rel_add hP (rel_neg hQ)

/-- `Rel` is compatible with scalar multiplication. -/
theorem rel_nsmul (n : ℕ) {P Q : E.Point} (h : E.Rel P Q) : E.Rel (n • P) (n • Q) := by
  rw [rel_iff_sub_mem] at h ⊢
  rw [← smul_sub]
  exact nsmul_mem h n

/-- Adding 4-torsion does not change the class. -/
theorem rel_add_of_mem {P T : E.Point} (hT : T ∈ AddSubgroup.torsionBy E.Point 4) :
    E.Rel (P + T) P := by
  rw [rel_iff_sub_mem, add_sub_cancel_left]
  exact hT

/-- **`Rel` in coordinates**: `P - Q` is 4-torsion iff `x₁ y₂ = y₁ x₂` (then `P - Q ∈ {(0, ±1)}`)
or `y₁ y₂ + a x₁ x₂ = 0` (then `P - Q` has `y = 0`). -/
theorem rel_iff [NeZero (6 : F)] (P Q : E.Point) :
    E.Rel P Q ↔ P.x * Q.y = P.y * Q.x ∨ P.y * Q.y + E.a * P.x * Q.x = 0 := by
  rw [rel_iff_sub_mem, mem_torsionBy_four_iff, sub_x, sub_y]
  unfold addX addY
  rw [div_eq_zero_iff, div_eq_zero_iff, neg_x, neg_y]
  have h₁ := addDen₁_ne_zero P (-Q)
  have h₂ := addDen₂_ne_zero P (-Q)
  constructor
  · rintro ((h | h) | (h | h))
    · left
      linear_combination h
    · exact absurd h h₁
    · right
      linear_combination h
    · exact absurd h h₂
  · rintro (h | h)
    · left
      left
      linear_combination h
    · right
      left
      linear_combination h

end TwistedEdwardsModel
