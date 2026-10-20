/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Even.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import all EllipticCurve.TwistedEdwards.Even.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public section

/-! # The even quotient of a complete twisted Edwards model: characterising lemmas

The audited statements about the hidden constructions of `EllipticCurve.TwistedEdwards.Even.Defs`:
the 4-torsion in coordinates (`four_nsmul_eq_zero_iff`: `4 • P = 0 ↔ x = 0 ∨ y = 0`;
`torsion4_eq_torsionBy` relates it to Mathlib's `Submodule.torsionBy`), the
relation `E.Rel` (an equivalence relation compatible with the group law, `rel_iff` in
coordinates), the even quotient (`EvenQuotient.mk_eq_mk_iff`, `mk_surjective`, the homomorphism
lemmas `mk_zero`, `mk_add`, `mk_neg`, `mk_sub`, `mk_nsmul`, and the cardinality
`card_evenQuotient_mul_card`), and the generic half of the 2-descent: the subgroup `E.descent` of
points with `(a - d)(1 - y²)` a square contains the even points (`even_le_descent`), through the
descent map `Q ↦ B u(Q)` of the Montgomery model (`isSquare_toMontgomery_B_mul_u_iff`,
`MontgomeryModel.isSquare_B_mul_u_add`). -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F} [E.IsComplete]

/-! ### The 4-torsion in coordinates -/

/-- The 4-torsion of a complete model is `{x = 0} ∪ {y = 0}`: `4 • P = 0` exactly when `P.x = 0`
or `P.y = 0` (the points `(0, ±1)` of order dividing `2` and `(±√(1/a), 0)` of order `4`). -/
theorem four_nsmul_eq_zero_iff (P : E.Point) : 4 • P = 0 ↔ P.x = 0 ∨ P.y = 0 := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  have hden := addDen₁_ne_zero P P
  rw [show (4 : ℕ) = 2 * 2 from rfl, ← smul_smul, two_nsmul_eq_zero_iff, two_nsmul_x]
  unfold addX
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have h' : (2 * P.x) * P.y = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h' | h'
      · exact Or.inl ((mul_eq_zero.mp h').resolve_left h2)
      · exact Or.inr h'
    · exact absurd h hden
  · rintro (h | h)
    · left
      rw [h]
      ring
    · left
      rw [h]
      ring

/-- The 4-torsion in coordinates. -/
theorem mem_torsion4_iff (P : E.Point) : P ∈ E.torsion4 ↔ P.x = 0 ∨ P.y = 0 := by
  rw [mem_torsion4, four_nsmul_eq_zero_iff]

/-- The 4-torsion is Mathlib's `Submodule.torsionBy ℤ E.Point 4`. -/
theorem torsion4_eq_torsionBy (E : TwistedEdwardsModel F) [E.IsComplete] :
    E.torsion4 = (Submodule.torsionBy ℤ E.Point 4).toAddSubgroup := by
  ext P
  rw [mem_torsion4, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff,
    show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, natCast_zsmul]

/-! ### The relation -/

/-- `E.Rel P Q` unfolds to `P - Q ∈ E.torsion4`. -/
theorem rel_iff_sub_mem (P Q : E.Point) : E.Rel P Q ↔ P - Q ∈ E.torsion4 :=
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
theorem rel_add_of_mem {P T : E.Point} (hT : T ∈ E.torsion4) : E.Rel (P + T) P := by
  rw [rel_iff_sub_mem, add_sub_cancel_left]
  exact hT

/-- **`Rel` in coordinates**: `P - Q` is 4-torsion iff `x₁ y₂ = y₁ x₂` (then `P - Q ∈ {(0, ±1)}`)
or `y₁ y₂ + a x₁ x₂ = 0` (then `P - Q` has `y = 0`). -/
theorem rel_iff (P Q : E.Point) :
    E.Rel P Q ↔ P.x * Q.y = P.y * Q.x ∨ P.y * Q.y + E.a * P.x * Q.x = 0 := by
  rw [rel_iff_sub_mem, mem_torsion4_iff, sub_x, sub_y]
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

/-! ### The even quotient -/

namespace EvenQuotient

/-- **Equality in the even quotient**: two representatives give the same element iff they differ
by 4-torsion. -/
theorem mk_eq_mk_iff {P Q : E.Point} {hP : Even P} {hQ : Even Q} :
    mk P hP = mk Q hQ ↔ E.Rel P Q :=
  mk_eq_mk_iff_aux ⟨P, AddSubgroup.mem_even.mpr hP⟩ ⟨Q, AddSubgroup.mem_even.mpr hQ⟩

/-- Every element of the even quotient is the class of an even point. -/
theorem mk_surjective (q : E.EvenQuotient) : ∃ (P : E.Point) (h : Even P), mk P h = q := by
  obtain ⟨⟨P, hP⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact ⟨P, AddSubgroup.mem_even.mp hP, rfl⟩

/-- The even point `P` as an element of `AddSubgroup.even E.Point`. Internal. -/
private def toEven (P : E.Point) (h : Even P) : AddSubgroup.even E.Point :=
  ⟨P, AddSubgroup.mem_even.mpr h⟩

private theorem mk_eq_mk' (P : E.Point) (h : Even P) :
    mk P h = QuotientAddGroup.mk' (E.torsion4.addSubgroupOf (AddSubgroup.even E.Point))
      (toEven P h) := by
  rfl

theorem mk_zero (h : Even (0 : E.Point)) : mk 0 h = 0 := by
  rw [mk_eq_mk']
  exact map_zero _

theorem mk_add {P Q : E.Point} (hP : Even P) (hQ : Even Q) (h : Even (P + Q)) :
    mk (P + Q) h = mk P hP + mk Q hQ := by
  rw [mk_eq_mk', mk_eq_mk', mk_eq_mk']
  exact map_add _ (toEven P hP) (toEven Q hQ)

theorem mk_neg {P : E.Point} (hP : Even P) (h : Even (-P)) : mk (-P) h = -mk P hP := by
  rw [mk_eq_mk', mk_eq_mk']
  exact map_neg _ (toEven P hP)

theorem mk_sub {P Q : E.Point} (hP : Even P) (hQ : Even Q) (h : Even (P - Q)) :
    mk (P - Q) h = mk P hP - mk Q hQ := by
  rw [mk_eq_mk', mk_eq_mk', mk_eq_mk']
  exact map_sub _ (toEven P hP) (toEven Q hQ)

theorem mk_nsmul (n : ℕ) {P : E.Point} (hP : Even P) (h : Even (n • P)) :
    mk (n • P) h = n • mk P hP := by
  rw [mk_eq_mk', mk_eq_mk']
  exact map_nsmul _ n (toEven P hP)

theorem mk_zsmul (n : ℤ) {P : E.Point} (hP : Even P) (h : Even (n • P)) :
    mk (n • P) h = n • mk P hP := by
  rw [mk_eq_mk', mk_eq_mk']
  exact map_zsmul _ n (toEven P hP)

/-- The class of an even point is zero iff the point is 4-torsion. -/
theorem mk_eq_zero_iff {P : E.Point} {hP : Even P} : mk P hP = 0 ↔ P ∈ E.torsion4 := by
  rw [← mk_zero Even.zero, mk_eq_mk_iff, rel_iff_sub_mem, sub_zero]

/-- The cardinality of the even quotient: `|even| = |EvenQuotient| · |torsion4 ⊓ even|`. -/
theorem card_evenQuotient_mul_card (E : TwistedEdwardsModel F) [E.IsComplete] :
    Nat.card E.EvenQuotient * Nat.card ↥(E.torsion4 ⊓ AddSubgroup.even E.Point) =
      Nat.card ↥(AddSubgroup.even E.Point) := by
  rw [← Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe
    (inf_le_right (a := E.torsion4) (b := AddSubgroup.even E.Point))).toEquiv,
    AddSubgroup.inf_addSubgroupOf_right]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm

end EvenQuotient

/-! ### The 2-descent: the generic half

For a point `P` of `E` with Montgomery image `Q`,
`B u(Q) = (2 / ((a - d)(1 - y)))² · (a - d)(1 - y²)` (and both sides are `0` at `P = (0, 1)`),
so the kernel of the descent map `Q ↦ B u(Q)` modulo squares of `E.toMontgomery`
(`MontgomeryModel.isSquare_B_mul_u_add`) pulls back to the subgroup `E.descent` of points with
`(a - d)(1 - y²)` a square. It contains every double
(`MontgomeryModel.isSquare_B_mul_u_two_nsmul`), hence the even points. Over a finite field the
map has index at most `2`, so that `E.descent` is the even subgroup as soon as it is not
everything; this counting is done for each curve (`curve25519.even_iff_isSquare`). -/

private theorem isSquare_sq_mul_iff {c x : F} (hc : c ≠ 0) :
    IsSquare (c ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / c, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hc hc), ← hr]
    ring
  · rintro ⟨r, hr⟩
    exact ⟨c * r, by rw [hr]; ring⟩

/-- The descent class of a point, on the Montgomery side and on the Edwards side:
`B u(Q)` is a square iff `(a - d)(1 - y²)` is. -/
theorem isSquare_toMontgomery_B_mul_u_iff (P : E.Point) :
    IsSquare (E.toMontgomery.B * (E.toMontgomeryEquiv P).u) ↔
      IsSquare ((E.a - E.d) * (1 - P.y ^ 2)) := by
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  rw [u_toMontgomeryEquiv, toMontgomery_B]
  by_cases hy : P.y = 1
  · rw [hy]
    norm_num
  · have h1y : 1 - P.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
    have key : 4 / (E.a - E.d) * ((1 + P.y) / (1 - P.y)) =
        (2 / ((E.a - E.d) * (1 - P.y))) ^ 2 * ((E.a - E.d) * (1 - P.y ^ 2)) := by
      field_simp
      ring
    rw [key, isSquare_sq_mul_iff (div_ne_zero h2 (mul_ne_zero had h1y))]

variable (E)

/-- The 2-descent subgroup: the points `P` with `(a - d)(1 - y²)` a square, the pullback of the
kernel of the descent map `Q ↦ B u(Q)` of `E.toMontgomery`. It contains the even points
(`even_le_descent`). Hidden; see `mem_descent`. -/
def descent : AddSubgroup E.Point where
  carrier := {P | IsSquare ((E.a - E.d) * (1 - P.y ^ 2))}
  zero_mem' := by
    change IsSquare ((E.a - E.d) * (1 - (0 : E.Point).y ^ 2))
    rw [zero_y]
    norm_num
  add_mem' {P Q} hP hQ := by
    change IsSquare ((E.a - E.d) * (1 - (P + Q).y ^ 2))
    rw [← isSquare_toMontgomery_B_mul_u_iff, map_add]
    exact MontgomeryModel.isSquare_B_mul_u_add
      ((isSquare_toMontgomery_B_mul_u_iff P).mpr (Set.mem_ofPred_eq.mp hP))
      ((isSquare_toMontgomery_B_mul_u_iff Q).mpr (Set.mem_ofPred_eq.mp hQ))
  neg_mem' {P} hP := by
    change IsSquare ((E.a - E.d) * (1 - (-P).y ^ 2))
    rw [neg_y]
    exact Set.mem_ofPred_eq.mp hP

variable {E}

/-- Membership in the 2-descent subgroup. -/
theorem mem_descent {P : E.Point} : P ∈ E.descent ↔ IsSquare ((E.a - E.d) * (1 - P.y ^ 2)) :=
  Iff.rfl

/-- Doubles lie in the 2-descent subgroup. -/
theorem two_nsmul_mem_descent (P : E.Point) : 2 • P ∈ E.descent := by
  rw [mem_descent, ← isSquare_toMontgomery_B_mul_u_iff, map_nsmul]
  exact MontgomeryModel.isSquare_B_mul_u_two_nsmul _

/-- The even points lie in the 2-descent subgroup. -/
theorem even_le_descent : AddSubgroup.even E.Point ≤ E.descent := by
  intro P hP
  obtain ⟨Q, rfl⟩ := (AddSubgroup.mem_even.mp hP).exists_two_nsmul
  exact two_nsmul_mem_descent Q

/-- An even point has `(a - d)(1 - y²)` a square: the easy direction of the 2-descent. -/
theorem isSquare_of_even {P : E.Point} (h : Even P) : IsSquare ((E.a - E.d) * (1 - P.y ^ 2)) :=
  mem_descent.mp (even_le_descent (AddSubgroup.mem_even.mpr h))

end TwistedEdwardsModel
