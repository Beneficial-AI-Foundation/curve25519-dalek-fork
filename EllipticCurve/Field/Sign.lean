/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Field.ZMod
public section

/-! # The sign convention on `ZMod p`

RFC 8032 (§5.1.2) and RFC 9496 (§4.1) call an element `x` of `ZMod p` *negative* when its
canonical representative `x.val ∈ [0, p)` is odd: `ZMod.isNeg x`. For odd `p`, exactly one of
`x` and `-x` is negative when `x ≠ 0` (`isNeg_neg_iff`), so every nonzero square has exactly one
non-negative square root (`existsUnique_sq_eq_not_isNeg`). The absolute value
`ZMod.abs x = if x.isNeg then -x else x` is RFC 9496's `CT_ABS` / `|x|`.

Both definitions are exposed: `isNeg` is a `Prop` that specifications unfold, and `abs` is a
formula the kernel evaluates. The parity lemmas take the oddness of `p` as an explicit
hypothesis `(hp : p % 2 = 1)` (for a complete twisted Edwards model over `ZMod p` it follows
from `2 ≠ 0`, `mod_two_eq_one_of_two_ne_zero`). -/

namespace ZMod

variable {p : ℕ}

/-- `x` is *negative* (RFC 8032 §5.1.2, RFC 9496 §4.1): its canonical representative
`x.val ∈ [0, p)` is odd. -/
@[expose] def isNeg (x : ZMod p) : Prop :=
  x.val % 2 = 1

instance instDecidableIsNeg (x : ZMod p) : Decidable x.isNeg :=
  inferInstanceAs (Decidable (x.val % 2 = 1))

/-- `|x|` (RFC 9496's `CT_ABS`): `-x` if `x` is negative, `x` otherwise. -/
@[expose] def abs (x : ZMod p) : ZMod p :=
  if x.isNeg then -x else x

/-! ### Parity -/

theorem isNeg_iff {x : ZMod p} : x.isNeg ↔ x.val % 2 = 1 :=
  Iff.rfl

theorem isNeg_iff_odd_val {x : ZMod p} : x.isNeg ↔ Odd x.val :=
  Nat.odd_iff.symm

theorem not_isNeg_iff {x : ZMod p} : ¬ x.isNeg ↔ x.val % 2 = 0 := by
  rw [isNeg_iff]
  omega

theorem not_isNeg_iff_even_val {x : ZMod p} : ¬ x.isNeg ↔ Even x.val := by
  rw [not_isNeg_iff, Nat.even_iff]

theorem isNeg_zero : ¬ (0 : ZMod p).isNeg := by
  rw [isNeg_iff, val_zero]
  decide

theorem isNeg_one [Fact (1 < p)] : (1 : ZMod p).isNeg := by
  rw [isNeg_iff, val_one]

/-- The sign of a natural number below `p`, cast to `ZMod p`, is its parity. -/
theorem isNeg_natCast_iff {n : ℕ} (h : n < p) : (n : ZMod p).isNeg ↔ n % 2 = 1 := by
  rw [isNeg_iff, val_cast_of_lt h]

/-- The sign of a numeral below `p` is its parity. -/
theorem isNeg_ofNat_iff {n : ℕ} [n.AtLeastTwo] (h : n < p) :
    (ofNat(n) : ZMod p).isNeg ↔ n % 2 = 1 := by
  rw [isNeg_iff, val_ofNat_of_lt h]
  exact Iff.rfl

theorem ne_zero_of_isNeg {x : ZMod p} (h : x.isNeg) : x ≠ 0 :=
  fun h0 => isNeg_zero (h0 ▸ h)

/-- `p` is odd when `2 ≠ 0` in the field `ZMod p`. -/
theorem mod_two_eq_one_of_two_ne_zero [Fact p.Prime] (h : (2 : ZMod p) ≠ 0) : p % 2 = 1 := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with hp | hp
  · subst hp
    exact absurd (by exact_mod_cast ZMod.natCast_self 2) h
  · exact hp

section Odd

variable (hp : p % 2 = 1)
include hp

/-- For odd `p`, exactly one of `x` and `-x` is negative when `x ≠ 0`. -/
theorem isNeg_neg_iff {x : ZMod p} (hx : x ≠ 0) : (-x).isNeg ↔ ¬ x.isNeg := by
  have : NeZero p := ⟨by omega⟩
  rw [isNeg_iff, isNeg_iff, neg_val, ite_eq_right hx]
  have h1 := val_lt x
  have h2 : x.val ≠ 0 := fun h0 => hx ((val_eq_zero x).mp h0)
  omega

theorem isNeg_neg_of_not_isNeg {x : ZMod p} (hx : x ≠ 0) (h : ¬ x.isNeg) : (-x).isNeg :=
  (isNeg_neg_iff hp hx).mpr h

theorem not_isNeg_neg_of_isNeg {x : ZMod p} (h : x.isNeg) : ¬ (-x).isNeg :=
  fun h' => (isNeg_neg_iff hp (ne_zero_of_isNeg h)).mp h' h

theorem isNeg_or_isNeg_neg {x : ZMod p} (hx : x ≠ 0) : x.isNeg ∨ (-x).isNeg := by
  rw [isNeg_neg_iff hp hx]
  exact em _

/-- An element that is not negative and whose negation is not negative is `0` (`p` odd). -/
theorem eq_zero_of_not_isNeg_of_not_isNeg_neg {x : ZMod p} (h : ¬ x.isNeg) (h' : ¬ (-x).isNeg) :
    x = 0 := by
  by_contra hx
  exact (isNeg_or_isNeg_neg hp hx).elim h h'

/-- Two elements with the same square and the same sign are equal (`p` odd). -/
theorem eq_of_sq_eq_of_isNeg_iff [Fact p.Prime] {x y : ZMod p} (h : x ^ 2 = y ^ 2)
    (hs : x.isNeg ↔ y.isNeg) : x = y := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with hxy | hxy
  · exact hxy
  · by_cases hy : y = 0
    · rw [hxy, hy, neg_zero]
    · rw [hxy, isNeg_neg_iff hp hy] at hs
      exact absurd hs not_iff_self

end Odd

/-! ### The absolute value -/

theorem abs_of_isNeg {x : ZMod p} (h : x.isNeg) : x.abs = -x :=
  ite_eq_left h

theorem abs_of_not_isNeg {x : ZMod p} (h : ¬ x.isNeg) : x.abs = x :=
  ite_eq_right h

theorem abs_zero : (0 : ZMod p).abs = 0 :=
  abs_of_not_isNeg isNeg_zero

theorem abs_eq_or_abs_eq_neg (x : ZMod p) : x.abs = x ∨ x.abs = -x := by
  by_cases h : x.isNeg
  · exact Or.inr (abs_of_isNeg h)
  · exact Or.inl (abs_of_not_isNeg h)

theorem abs_sq (x : ZMod p) : x.abs ^ 2 = x ^ 2 := by
  rcases abs_eq_or_abs_eq_neg x with h | h <;> rw [h]
  exact neg_sq x

theorem abs_mul_self (x : ZMod p) : x.abs * x.abs = x * x := by
  rw [← sq, ← sq, abs_sq]

theorem abs_eq_zero_iff {x : ZMod p} : x.abs = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases abs_eq_or_abs_eq_neg x with h' | h'
    · exact h' ▸ h
    · exact neg_eq_zero.mp (h' ▸ h)
  · rintro rfl
    exact abs_zero

section Odd

variable (hp : p % 2 = 1)
include hp

/-- `|x|` is never negative (`p` odd). -/
theorem not_isNeg_abs (x : ZMod p) : ¬ x.abs.isNeg := by
  by_cases h : x.isNeg
  · rw [abs_of_isNeg h]
    exact not_isNeg_neg_of_isNeg hp h
  · rwa [abs_of_not_isNeg h]

theorem abs_neg (x : ZMod p) : (-x).abs = x.abs := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · by_cases h : x.isNeg
    · rw [abs_of_isNeg h, abs_of_not_isNeg (not_isNeg_neg_of_isNeg hp h)]
    · rw [abs_of_not_isNeg h, abs_of_isNeg (isNeg_neg_of_not_isNeg hp hx h), neg_neg]

theorem abs_abs (x : ZMod p) : x.abs.abs = x.abs :=
  abs_of_not_isNeg (not_isNeg_abs hp x)

/-- `|x| = y` iff `y` is `x` or `-x` and `y` is not negative (`p` odd). -/
theorem abs_eq_iff {x y : ZMod p} : x.abs = y ↔ (y = x ∨ y = -x) ∧ ¬ y.isNeg := by
  constructor
  · rintro rfl
    exact ⟨(abs_eq_or_abs_eq_neg x), not_isNeg_abs hp x⟩
  · rintro ⟨rfl | rfl, hneg⟩
    · exact abs_of_not_isNeg hneg
    · rw [← abs_neg hp]
      exact abs_of_not_isNeg hneg

/-- `|x| = |y|` iff `y = x` or `y = -x` (`p` odd). -/
theorem abs_eq_abs_iff {x y : ZMod p} : x.abs = y.abs ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    rcases abs_eq_or_abs_eq_neg x with hx | hx <;> rcases abs_eq_or_abs_eq_neg y with hy | hy <;>
      rw [hx, hy] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (neg_eq_iff_eq_neg.mp h)
    · exact Or.inl (neg_inj.mp h)
  · rintro (rfl | rfl)
    · rfl
    · exact abs_neg hp y

end Odd

/-! ### Square roots -/

section Field

variable [Fact p.Prime]

theorem eq_or_eq_neg_of_sq_eq {x y : ZMod p} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y :=
  sq_eq_sq_iff_eq_or_eq_neg.mp h

variable (hp : p % 2 = 1)
include hp

/-- Two elements with the same square have the same absolute value (`p` odd). -/
theorem abs_eq_abs_of_sq_eq {x y : ZMod p} (h : x ^ 2 = y ^ 2) : x.abs = y.abs :=
  (abs_eq_abs_iff hp).mpr (sq_eq_sq_iff_eq_or_eq_neg.mp h)

/-- A non-negative element is the absolute value of anything with the same square (`p` odd). -/
theorem eq_abs_of_sq_eq_of_not_isNeg {x y : ZMod p} (h : x ^ 2 = y ^ 2) (hx : ¬ x.isNeg) :
    x = y.abs :=
  eq_of_sq_eq_of_isNeg_iff hp (by rw [abs_sq]; exact h) (iff_of_false hx (not_isNeg_abs hp y))

/-- A square has a non-negative square root (`p` odd). -/
theorem exists_sq_eq_not_isNeg {x : ZMod p} (hx : IsSquare x) :
    ∃ r : ZMod p, r ^ 2 = x ∧ ¬ r.isNeg := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r.abs, by rw [abs_sq, sq], not_isNeg_abs hp r⟩

/-- A nonzero square has a negative square root (`p` odd). -/
theorem exists_sq_eq_isNeg {x : ZMod p} (hx : IsSquare x) (hx0 : x ≠ 0) :
    ∃ r : ZMod p, r ^ 2 = x ∧ r.isNeg := by
  obtain ⟨r, hr, hneg⟩ := exists_sq_eq_not_isNeg hp hx
  have hr0 : r ≠ 0 := fun h => hx0 (by rw [← hr, h, zero_pow two_ne_zero])
  exact ⟨-r, by rw [neg_sq, hr], isNeg_neg_of_not_isNeg hp hr0 hneg⟩

/-- **The non-negative square root**: a square has exactly one square root that is not negative
(`p` odd). -/
theorem existsUnique_sq_eq_not_isNeg {x : ZMod p} (hx : IsSquare x) :
    ∃! r : ZMod p, r ^ 2 = x ∧ ¬ r.isNeg := by
  obtain ⟨r, hr, hneg⟩ := exists_sq_eq_not_isNeg hp hx
  refine ⟨r, ⟨hr, hneg⟩, fun s ⟨hs, hsneg⟩ => ?_⟩
  exact eq_of_sq_eq_of_isNeg_iff hp (hs.trans hr.symm) (iff_of_false hsneg hneg)

end Field

end ZMod
