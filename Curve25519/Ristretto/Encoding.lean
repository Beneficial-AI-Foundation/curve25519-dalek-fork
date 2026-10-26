/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Ristretto.Encoding.Defs
import all Curve25519.Ristretto.Encoding.Defs
import Curve25519.Proofs.Ristretto.Algebra
import Curve25519.Proofs.Ristretto.Certs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # The ristretto255 encoding (RFC 9496 §4.3.1–4.3.2): properties

The audited statements about the hidden `Ristretto.decodeRep` and `Ristretto.encodeRep` of
`Curve25519.Ristretto.Encoding.Defs`, and the quotient-level `Ristretto.encode`/`Ristretto.decode`.

* Decoding: `decodeRep_eq_some_iff` (`decodeRep s = some P` iff `s < p` is non-negative, `P` has
  `y = (1 - s²) / (1 + s²)`, `x` and `x y` non-negative and `y ≠ 0`), `decodeRep_eq_none_iff`
  (the rejection reasons of RFC 9496 §4.3.1), `even_decodeRep`, `decodeRep_y`, `decodeRep_x_sq`.
* Encoding: `encodeRep_lt`, `not_isNeg_encodeRep`, the round trips `encodeRep_decodeRep` and
  `decodeRep_encodeRep`, and the invariance `encodeRep_rel` on the classes of `Ristretto`
  (`encodeRep_eq_iff`).
* The classes in coordinates: `rel_iff_coords` (the four 4-torsion translates `(x, y)`,
  `(-x, -y)`, `(y √-1, x √-1)`, `(-(y √-1), -(x √-1))`) and the uniqueness of the canonical
  representative `eq_of_rel_of_canonical` (`x` and `x y` non-negative, `y ≠ 0`, `y ≠ -1`).
* Quotient level: `encode : Ristretto → ℕ` with `encode_mk`, `decode : ℕ → Option Ristretto`
  with `decode_eq_some_iff : decode s = some x ↔ encode x = s`, `encode_injective`,
  `decode_encode`, `encode_lt`, `encode_zero`, and the encoding of the basepoint
  `encode_basepoint` (RFC 9496 §A.1, a kernel certificate in `Curve25519.Proofs.Ristretto.Certs`).

The proof of the round trips goes through the canonical representative of a class: every class
with `x y ≠ 0` has exactly one representative with `x` and `x y` non-negative (`exists_canon`,
`eq_of_rel_of_canonical`); `encodeRep` of any representative is `|D (1 - y_C)|` with
`D² (1 - y_C²) = 1` for the canonical `(x_C, y_C)` (the `rotate`/sign machinery of §4.3.2), and
`decodeRep` returns the canonical representative. -/

namespace curve25519

open TwistedEdwardsModel

/-! ### The classes in coordinates -/

/-- **The 4-torsion translates in coordinates**: `Q` is in the class of `P` iff `Q` is `(x, y)`,
`(-x, -y)` (`P + (0, -1)`), `(y √-1, x √-1)` (`P + (√-1, 0)`) or `(-(y √-1), -(x √-1))`
(`P + (-√-1, 0)`). -/
theorem rel_iff_coords (P Q : edwards.Point) :
    edwards.Rel P Q ↔
      (Q.x = P.x ∧ Q.y = P.y) ∨ (Q.x = -P.x ∧ Q.y = -P.y) ∨
        (Q.x = P.y * sqrtM1 ∧ Q.y = P.x * sqrtM1) ∨
        (Q.x = -(P.y * sqrtM1) ∧ Q.y = -(P.x * sqrtM1)) := by
  constructor
  · intro h
    have hT : Q - P ∈ edwards.torsion4 := (rel_iff_sub_mem Q P).mp (rel_symm h)
    have hQ : Q = P + (Q - P) := by abel
    rw [curve25519.mem_torsion4_iff] at hT
    rcases hT with hT | hT | hT | hT <;> rw [hT] at hQ
    · left
      rw [hQ, add_zero]
      exact ⟨rfl, rfl⟩
    · right; right; right
      rw [hQ, add_x, add_y]
      unfold addX addY addDen₁ addDen₂
      rw [eightTorsion_two_x, eightTorsion_two_y_eq, edwards_a_eq_neg_one]
      constructor <;> ring
    · right; left
      rw [hQ, add_x, add_y]
      unfold addX addY addDen₁ addDen₂
      rw [eightTorsion_four_x_eq, eightTorsion_four_y, edwards_a_eq_neg_one]
      constructor <;> ring
    · right; right; left
      rw [hQ, add_x, add_y]
      unfold addX addY addDen₁ addDen₂
      rw [eightTorsion_six_x, eightTorsion_six_y_eq, edwards_a_eq_neg_one]
      constructor <;> ring
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩) <;> rw [rel_iff_formula, hx, hy]
    · left; ring
    · left; ring
    · right; ring
    · right; ring

/-- **Uniqueness of the canonical representative**: two representatives of one class with `x`
and `x y` non-negative, `y ≠ 0` and `y ≠ -1` are equal. -/
theorem eq_of_rel_of_canonical {P Q : edwards.Point} (h : edwards.Rel P Q)
    (hPx : ¬ P.x.isNeg) (hPxy : ¬ (P.x * P.y).isNeg) (hPy : P.y ≠ 0) (hPy1 : P.y ≠ -1)
    (hQx : ¬ Q.x.isNeg) (hQxy : ¬ (Q.x * Q.y).isNeg) (hQy : Q.y ≠ 0) (hQy1 : Q.y ≠ -1) :
    P = Q := by
  rw [rel_iff_coords] at h
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact (Point.ext hx hy).symm
  · exfalso
    rw [hx] at hQx
    have hx0 : P.x = 0 := ZMod.eq_zero_of_not_isNeg_of_not_isNeg_neg p_mod_two hPx hQx
    have hy1 : P.y = 1 :=
      (y_eq_one_or_eq_neg_one_of_x_eq_zero P.equation hx0).resolve_right hPy1
    rw [hy, hy1] at hQy1
    exact hQy1 rfl
  · exfalso
    have hprod : Q.x * Q.y = -(P.x * P.y) := by
      rw [hx, hy]
      linear_combination (P.x * P.y) * sqrtM1_sq
    rw [hprod] at hQxy
    have h0 : P.x * P.y = 0 := ZMod.eq_zero_of_not_isNeg_of_not_isNeg_neg p_mod_two hPxy hQxy
    have hx0 : P.x = 0 := (mul_eq_zero.mp h0).resolve_right hPy
    rw [hy, hx0, zero_mul] at hQy
    exact hQy rfl
  · exfalso
    have hprod : Q.x * Q.y = -(P.x * P.y) := by
      rw [hx, hy]
      linear_combination (P.x * P.y) * sqrtM1_sq
    rw [hprod] at hQxy
    have h0 : P.x * P.y = 0 := ZMod.eq_zero_of_not_isNeg_of_not_isNeg_neg p_mod_two hPxy hQxy
    have hx0 : P.x = 0 := (mul_eq_zero.mp h0).resolve_right hPy
    rw [hy, hx0, zero_mul, neg_zero] at hQy
    exact hQy rfl

/-- A point in the class of an even point is even. -/
theorem even_of_rel {P Q : edwards.Point} (hP : Even P) (h : edwards.Rel P Q) : Even Q := by
  have hT : Q - P ∈ edwards.torsion4 := (rel_iff_sub_mem Q P).mp (rel_symm h)
  have hT' : Even (Q - P) := AddSubgroup.mem_even.mp (torsion4_le_even hT)
  rw [show Q = P + (Q - P) by abel]
  exact hP.add hT'

namespace Ristretto

/-! ### Decoding -/

/-! The intermediate quantities of RFC 9496 §4.3.1, internal. -/

private noncomputable def decU1 (s : ℕ) : ZMod p := 1 - (s : ZMod p) ^ 2

private noncomputable def decU2 (s : ℕ) : ZMod p := 1 + (s : ZMod p) ^ 2

private noncomputable def decV (s : ℕ) : ZMod p := -(d * decU1 s ^ 2) - decU2 s ^ 2

private noncomputable def decW (s : ℕ) : ZMod p := decV s * decU2 s ^ 2

private noncomputable def decR (s : ℕ) : ZMod p := (sqrtRatioM1 1 (decW s)).2

private noncomputable def decX (s : ℕ) : ZMod p := (2 * (s : ZMod p) * (decR s * decU2 s)).abs

private noncomputable def decY (s : ℕ) : ZMod p := decU1 s * (decR s * (decR s * decU2 s) * decV s)

private theorem decodeRep_of_not {s : ℕ} (h : ¬ (s < p ∧ ¬ (s : ZMod p).isNeg)) :
    decodeRep s = none := by
  unfold decodeRep
  rw [ite_eq_right h]

private theorem decodeRep_of_lt {s : ℕ} (h : s < p ∧ ¬ (s : ZMod p).isNeg) :
    decodeRep s =
      if hc : (sqrtRatioM1 1 (decW s)).1 = true ∧ ¬ (decX s * decY s).isNeg ∧ decY s ≠ 0 then
        some ⟨decX s, decY s, decodeRep_equation s (decR s) (sqrtRatioM1_one_of_fst hc.1)⟩
      else none := by
  unfold decodeRep
  rw [ite_eq_left h]
  rfl

/-- **The rejection reasons of decoding** (RFC 9496 §4.3.1): `decodeRep s = none` iff `s ≥ p`,
`s` is negative, `v u2²` has no inverse square root (`was_square = false`), the decoded `x y` is
negative, or the decoded `y` is `0`. -/
theorem decodeRep_eq_none_iff (s : ℕ) :
    decodeRep s = none ↔
      p ≤ s ∨ (s : ZMod p).isNeg ∨
        let s' : ZMod p := s
        let u1 := 1 - s' ^ 2
        let u2 := 1 + s' ^ 2
        let v := -(d * u1 ^ 2) - u2 ^ 2
        let r := (sqrtRatioM1 1 (v * u2 ^ 2)).2
        let x := (2 * s' * (r * u2)).abs
        let y := u1 * (r * (r * u2) * v)
        (sqrtRatioM1 1 (v * u2 ^ 2)).1 = false ∨ (x * y).isNeg ∨ y = 0 := by
  change decodeRep s = none ↔ p ≤ s ∨ (s : ZMod p).isNeg ∨
    (sqrtRatioM1 1 (decW s)).1 = false ∨ (decX s * decY s).isNeg ∨ decY s = 0
  by_cases h : s < p ∧ ¬ (s : ZMod p).isNeg
  · rw [decodeRep_of_lt h]
    by_cases hc : (sqrtRatioM1 1 (decW s)).1 = true ∧ ¬ (decX s * decY s).isNeg ∧ decY s ≠ 0
    · rw [dite_eq_left hc]
      refine iff_of_false (by simp) ?_
      rintro (h' | h' | h' | h' | h')
      · omega
      · exact h.2 h'
      · rw [hc.1] at h'
        exact absurd h' (by decide)
      · exact hc.2.1 h'
      · exact hc.2.2 h'
    · rw [dite_eq_right hc]
      refine iff_of_true rfl (Or.inr (Or.inr ?_))
      rw [not_and_or, not_and_or, not_not, not_not] at hc
      rcases hc with hc | hc | hc
      · exact Or.inl (Bool.eq_false_iff.mpr hc)
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
  · rw [decodeRep_of_not h]
    refine iff_of_true rfl ?_
    rw [not_and_or, not_not] at h
    rcases h with h | h
    · exact Or.inl (not_lt.mp h)
    · exact Or.inr (Or.inl h)

/-- **The meaning of decoding**: `decodeRep s = some P` iff `s < p` is non-negative and `P` is
the point with `y = (1 - s²) / (1 + s²)`, `x` and `x y` non-negative and `y ≠ 0`. -/
theorem decodeRep_eq_some_iff {s : ℕ} {P : edwards.Point} :
    decodeRep s = some P ↔
      s < p ∧ ¬ (s : ZMod p).isNeg ∧
        P.y = (1 - (s : ZMod p) ^ 2) / (1 + (s : ZMod p) ^ 2) ∧
        ¬ P.x.isNeg ∧ ¬ (P.x * P.y).isNeg ∧ P.y ≠ 0 := by
  constructor
  · intro h
    by_cases hs : s < p ∧ ¬ (s : ZMod p).isNeg
    · rw [decodeRep_of_lt hs] at h
      by_cases hc : (sqrtRatioM1 1 (decW s)).1 = true ∧ ¬ (decX s * decY s).isNeg ∧ decY s ≠ 0
      · rw [dite_eq_left hc, Option.some.injEq] at h
        subst h
        refine ⟨hs.1, hs.2, ?_, ZMod.not_isNeg_abs p_mod_two _, hc.2.1, hc.2.2⟩
        exact Proofs.decode_y_eq s (decR s) (sqrtRatioM1_one_of_fst hc.1)
      · rw [dite_eq_right hc] at h
        cases h
    · rw [decodeRep_of_not hs] at h
      cases h
  · rintro ⟨hs, hneg, hy, hx, hxy, hy0⟩
    have hu2 : decU2 s ≠ 0 := by
      intro h
      apply hy0
      rw [hy]
      change decU1 s / decU2 s = 0
      rw [h, div_zero]
    have hyu : P.y * (1 + (s : ZMod p) ^ 2) = 1 - (s : ZMod p) ^ 2 := (eq_div_iff hu2).mp hy
    have hv : decV s ≠ 0 := Proofs.decode_v_ne_zero s
    have hxv := Proofs.x_sq_mul_v_eq (s : ZMod p) P.equation hyu
    have hW0 : decW s ≠ 0 := mul_ne_zero hv (pow_ne_zero 2 hu2)
    have hWsq : IsSquare (decW s) := by
      by_cases hx0 : P.x = 0
      · have hs0 : (s : ZMod p) = 0 := by
          rw [hx0] at hxv
          have h4 : (4 : ZMod p) * (s : ZMod p) ^ 2 = 0 := by linear_combination -hxv
          have h4' : (4 : ZMod p) ≠ 0 := by
            rw [show (4 : ZMod p) = 2 * 2 by norm_num]
            exact mul_ne_zero two_ne_zero two_ne_zero
          exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp h4).resolve_left h4')
        refine ⟨sqrtAdMinusOne, ?_⟩
        unfold decW decV decU1 decU2
        rw [hs0]
        linear_combination -sqrtAdMinusOne_sq - d * a_def
      · refine ⟨2 * (s : ZMod p) * decU2 s / P.x, ?_⟩
        unfold decW decV decU1 decU2
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx0 hx0)]
        linear_combination (1 + (s : ZMod p) ^ 2) ^ 2 * hxv
    have hfst : (sqrtRatioM1 1 (decW s)).1 = true := (sqrtRatioM1_one_fst_iff _).mpr ⟨hW0, hWsq⟩
    have hr : decW s * decR s ^ 2 = 1 := sqrtRatioM1_one_of_fst hfst
    have hyd : decY s = P.y := (Proofs.decode_y_eq s (decR s) hr).trans hy.symm
    have hxd : decX s = P.x := by
      refine ZMod.eq_of_sq_eq_of_isNeg_iff p_mod_two ?_
        (iff_of_false (ZMod.not_isNeg_abs p_mod_two _) hx)
      exact mul_right_cancel₀ hv ((Proofs.decode_x_sq_mul_v s (decR s) hr).trans hxv.symm)
    rw [decodeRep_of_lt ⟨hs, hneg⟩,
      dite_eq_left ⟨hfst, by rw [hxd, hyd]; exact hxy, by rw [hyd]; exact hy0⟩]
    exact congrArg some (Point.ext hxd hyd)

theorem decodeRep_lt {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) : s < p :=
  (decodeRep_eq_some_iff.mp h).1

theorem not_isNeg_of_decodeRep {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) :
    ¬ (s : ZMod p).isNeg :=
  (decodeRep_eq_some_iff.mp h).2.1

/-- The decoded point has `y = (1 - s²) / (1 + s²)`. -/
theorem decodeRep_y {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) :
    P.y = (1 - (s : ZMod p) ^ 2) / (1 + (s : ZMod p) ^ 2) :=
  (decodeRep_eq_some_iff.mp h).2.2.1

theorem not_isNeg_decodeRep_x {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) :
    ¬ P.x.isNeg :=
  (decodeRep_eq_some_iff.mp h).2.2.2.1

theorem not_isNeg_decodeRep_xy {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) :
    ¬ (P.x * P.y).isNeg :=
  (decodeRep_eq_some_iff.mp h).2.2.2.2.1

theorem decodeRep_y_ne_zero {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) : P.y ≠ 0 :=
  (decodeRep_eq_some_iff.mp h).2.2.2.2.2

/-- `1 + s² ≠ 0` for a decoded `s`. -/
theorem one_add_sq_ne_zero_of_decodeRep {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) :
    1 + (s : ZMod p) ^ 2 ≠ 0 := by
  intro h0
  apply decodeRep_y_ne_zero h
  rw [decodeRep_y h, h0, div_zero]

/-- The decoded point has `y ≠ -1`: it is never `(0, -1)`. -/
theorem decodeRep_y_ne_neg_one {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) :
    P.y ≠ -1 := by
  intro h1
  have hu2 := one_add_sq_ne_zero_of_decodeRep h
  have hy := decodeRep_y h
  rw [h1, eq_div_iff hu2] at hy
  have h2 : (2 : ZMod p) = 0 := by linear_combination -hy
  exact two_ne_zero h2

/-- The decoded point has `x² v = 4 s²` for `v = -(d (1 - s²)²) - (1 + s²)²`. -/
theorem decodeRep_x_sq {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) :
    P.x ^ 2 * (-(d * (1 - (s : ZMod p) ^ 2) ^ 2) - (1 + (s : ZMod p) ^ 2) ^ 2) =
      4 * (s : ZMod p) ^ 2 :=
  Proofs.x_sq_mul_v_eq (s : ZMod p) P.equation
    ((eq_div_iff (one_add_sq_ne_zero_of_decodeRep h)).mp (decodeRep_y h))

/-- **The decoded point is even**: `1 - y² = (2 s / (1 + s²))²`. -/
theorem even_decodeRep {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) : Even P := by
  have hu2 := one_add_sq_ne_zero_of_decodeRep h
  rw [even_iff_isSquare, decodeRep_y h]
  refine ⟨2 * (s : ZMod p) / (1 + (s : ZMod p) ^ 2), ?_⟩
  field_simp
  ring

/-- `decodeRep 0 = some 0`: the encoding of the identity is `0`. -/
theorem decodeRep_zero : decodeRep 0 = some 0 := by
  rw [decodeRep_eq_some_iff, zero_x, zero_y, Nat.cast_zero]
  refine ⟨p_pos, ZMod.isNeg_zero, by norm_num, ZMod.isNeg_zero, ?_, one_ne_zero⟩
  rw [zero_mul]
  exact ZMod.isNeg_zero

/-! ### Encoding -/

/-! The intermediate quantities of RFC 9496 §4.3.2 after `z_inv = 1`, internal: the rotated
point `(xRot, yRot)` (`(y √-1, x √-1)` when `x y` is negative), its canonical `y`-coordinate
`yC` (negated when `xRot` is negative), and the denominator `denC`. -/

private noncomputable def encW (P : edwards.Point) : ZMod p :=
  (1 + P.y) * (1 - P.y) * (P.x * P.y) ^ 2

private noncomputable def encI (P : edwards.Point) : ZMod p := (sqrtRatioM1 1 (encW P)).2

private noncomputable def xRot (P : edwards.Point) : ZMod p :=
  if (P.x * P.y).isNeg then P.y * sqrtM1 else P.x

private noncomputable def yRot (P : edwards.Point) : ZMod p :=
  if (P.x * P.y).isNeg then P.x * sqrtM1 else P.y

private noncomputable def yC (P : edwards.Point) : ZMod p :=
  if (xRot P).isNeg then -yRot P else yRot P

private noncomputable def denC (P : edwards.Point) : ZMod p :=
  if (P.x * P.y).isNeg then encI P * ((1 + P.y) * (1 - P.y)) * invsqrtAMinusD
  else encI P * (P.x * P.y)

theorem encodeRep_lt (P : edwards.Point) : encodeRep P < p := by
  rw [encodeRep_eq]
  exact ZMod.val_lt _

/-- An encoding is a non-negative field element. -/
theorem not_isNeg_encodeRep (P : edwards.Point) : ¬ ((encodeRep P : ℕ) : ZMod p).isNeg := by
  rw [encodeRep_eq]
  dsimp only
  rw [ZMod.natCast_zmod_val]
  exact ZMod.not_isNeg_abs p_mod_two _

/-- The 4-torsion (`x y = 0`) encodes to `0`. -/
theorem encodeRep_of_mul_eq_zero {P : edwards.Point} (h : P.x * P.y = 0) : encodeRep P = 0 := by
  rw [encodeRep_eq]
  dsimp only
  rw [h, show (1 + P.y) * (1 - P.y) * (0 : ZMod p) ^ 2 = 0 by ring, sqrtRatioM1_one_zero]
  simp [ZMod.isNeg_zero, ZMod.abs_zero]

theorem encodeRep_zero : encodeRep 0 = 0 :=
  encodeRep_of_mul_eq_zero (by rw [zero_x, zero_mul])

/-- `W I² = 1` for an even point with `x y ≠ 0`: `W = (1 + y)(1 - y)(x y)²` is a nonzero square. -/
private theorem encW_mul_sq_eq_one {P : edwards.Point} (hP : Even P) (hxy : P.x * P.y ≠ 0) :
    encW P * encI P ^ 2 = 1 := by
  have hx : P.x ≠ 0 := fun h => hxy (by rw [h, zero_mul])
  have hW0 : encW P ≠ 0 := by
    unfold encW
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero 2 hxy)
    · intro h
      exact y_ne_neg_one_of_x_ne_zero P.equation hx (by linear_combination h)
    · intro h
      exact y_ne_one_of_x_ne_zero P.equation hx (by linear_combination -h)
  obtain ⟨q, hq⟩ := (even_iff_isSquare P).mp hP
  exact sqrtRatioM1_one_of_isSquare hW0 (Proofs.enc_W_isSquare hq)

/-- `encodeRep` after `z_inv = 1`: `|denC (1 - yC)|`. -/
private theorem encodeRep_eq_of_mul_sq_eq_one {P : edwards.Point} (hW : encW P * encI P ^ 2 = 1) :
    encodeRep P = (denC P * (1 - yC P)).abs.val := by
  rw [encodeRep_eq]
  dsimp only
  have hz : (sqrtRatioM1 1 ((1 + P.y) * (1 - P.y) * (P.x * P.y) ^ 2)).2 * ((1 + P.y) * (1 - P.y)) *
      ((sqrtRatioM1 1 ((1 + P.y) * (1 - P.y) * (P.x * P.y) ^ 2)).2 * (P.x * P.y)) * (P.x * P.y) =
        1 :=
    Proofs.enc_zInv_eq_one P.x P.y _ hW
  rw [hz, mul_one, mul_one]
  rfl

/-- The squared canonical `y`: `-x²` after a rotation, `y²` otherwise. -/
private theorem yC_sq (P : edwards.Point) :
    yC P ^ 2 = if (P.x * P.y).isNeg then -(P.x ^ 2) else P.y ^ 2 := by
  unfold yC yRot
  split_ifs
  · rw [neg_sq, mul_pow, sqrtM1_sq]; ring
  · exact neg_sq _
  · rw [mul_pow, sqrtM1_sq]; ring
  · rfl

/-- `denC² (1 - yC²) = 1`. -/
private theorem denC_sq {P : edwards.Point} (hW : encW P * encI P ^ 2 = 1) :
    denC P ^ 2 * (1 - yC P ^ 2) = 1 := by
  have hc : -P.x ^ 2 + P.y ^ 2 = 1 + d * P.x ^ 2 * P.y ^ 2 := by
    have h := P.equation
    unfold Equation at h
    rw [edwards_a_eq_neg_one, edwards_d] at h
    linear_combination h
  have hW' : (1 + P.y) * (1 - P.y) * (P.x * P.y) ^ 2 * encI P ^ 2 = 1 := hW
  rw [yC_sq]
  unfold denC
  split_ifs
  · have hK : (invsqrtAMinusD : ZMod p) ^ 2 * (-1 - d) = 1 := by
      rw [← a_def]
      exact invsqrtAMinusD_sq_mul
    have := Proofs.enc_den1_sq d sqrtM1 P.x P.y (encI P) invsqrtAMinusD sqrtM1_sq hc hW' hK
    rwa [mul_pow P.x, sqrtM1_sq, mul_neg, mul_one] at this
  · exact Proofs.enc_den2_sq P.x P.y (encI P) hW'

/-- `(-x, -y)` is on the model with `(x, y)`. -/
private theorem equation_neg_neg {x y : ZMod p} (h : edwards.Equation x y) :
    edwards.Equation (-x) (-y) := by
  unfold Equation at h ⊢
  rwa [neg_sq, neg_sq]

/-- `(y √-1, x √-1)` is on the model with `(x, y)`. -/
private theorem equation_rot {x y : ZMod p} (h : edwards.Equation x y) :
    edwards.Equation (y * sqrtM1) (x * sqrtM1) := by
  unfold Equation at h ⊢
  rw [edwards_a_eq_neg_one] at h ⊢
  rw [mul_pow, mul_pow, sqrtM1_sq]
  linear_combination h

/-- **The canonical representative**: for `x y ≠ 0`, the class of `P` contains the point
`(|xRot|, yC)`. -/
private theorem exists_canon (P : edwards.Point) :
    ∃ C : edwards.Point, edwards.Rel P C ∧ C.x = (xRot P).abs ∧ C.y = yC P := by
  unfold yC xRot yRot
  by_cases hrot : (P.x * P.y).isNeg
  · rw [ite_eq_left hrot, ite_eq_left hrot]
    by_cases hflip : (P.y * sqrtM1).isNeg
    · refine ⟨⟨-(P.y * sqrtM1), -(P.x * sqrtM1), equation_neg_neg (equation_rot P.equation)⟩,
        ?_, ?_, ?_⟩
      · rw [rel_iff_coords]
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact (ZMod.abs_of_isNeg hflip).symm
      · exact (ite_eq_left hflip).symm
    · refine ⟨⟨P.y * sqrtM1, P.x * sqrtM1, equation_rot P.equation⟩, ?_, ?_, ?_⟩
      · rw [rel_iff_coords]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact (ZMod.abs_of_not_isNeg hflip).symm
      · exact (ite_eq_right hflip).symm
  · rw [ite_eq_right hrot, ite_eq_right hrot]
    by_cases hflip : P.x.isNeg
    · refine ⟨⟨-P.x, -P.y, equation_neg_neg P.equation⟩, ?_, ?_, ?_⟩
      · rw [rel_iff_coords]
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact (ZMod.abs_of_isNeg hflip).symm
      · exact (ite_eq_left hflip).symm
    · refine ⟨P, rel_refl P, ?_, ?_⟩
      · exact (ZMod.abs_of_not_isNeg hflip).symm
      · exact (ite_eq_right hflip).symm

private theorem yC_ne_zero {P : edwards.Point} (hxy : P.x * P.y ≠ 0) : yC P ≠ 0 := by
  have hx : P.x ≠ 0 := fun h => hxy (by rw [h, zero_mul])
  have hy : P.y ≠ 0 := fun h => hxy (by rw [h, mul_zero])
  unfold yC yRot
  split_ifs
  · exact neg_ne_zero.mpr (mul_ne_zero hx sqrtM1_ne_zero)
  · exact neg_ne_zero.mpr hy
  · exact mul_ne_zero hx sqrtM1_ne_zero
  · exact hy

/-- The canonical representative has `x y` non-negative. -/
private theorem not_isNeg_abs_xRot_mul_yC (P : edwards.Point) :
    ¬ ((xRot P).abs * yC P).isNeg := by
  have hprod : (xRot P).abs * yC P = xRot P * yRot P := by
    unfold yC
    split_ifs with h
    · rw [ZMod.abs_of_isNeg h]; ring
    · rw [ZMod.abs_of_not_isNeg h]
  rw [hprod]
  unfold xRot yRot
  split_ifs with h
  · rw [show P.y * sqrtM1 * (P.x * sqrtM1) = -(P.x * P.y) by
      linear_combination (P.x * P.y) * sqrtM1_sq]
    exact ZMod.not_isNeg_neg_of_isNeg p_mod_two h
  · exact h

/-- **Encoding then decoding**: `decodeRep (encodeRep P)` is the canonical representative of the
class of an even point `P`. -/
theorem decodeRep_encodeRep {P : edwards.Point} (hP : Even P) :
    ∃ Q : edwards.Point, decodeRep (encodeRep P) = some Q ∧ edwards.Rel P Q := by
  by_cases hxy : P.x * P.y = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [encodeRep_of_mul_eq_zero hxy, decodeRep_zero]
    · rw [rel_iff_sub_mem, sub_zero, TwistedEdwardsModel.mem_torsion4_iff]
      exact mul_eq_zero.mp hxy
  · obtain ⟨C, hrel, hCx, hCy⟩ := exists_canon P
    have hW := encW_mul_sq_eq_one hP hxy
    have hD := denC_sq hW
    have hS := Proofs.sq_eq_div_of hD
    have hy1 : 1 + yC P ≠ 0 := by
      intro h
      have h' : yC P = -1 := by linear_combination h
      rw [h'] at hD
      exact one_ne_zero (by linear_combination -hD)
    refine ⟨C, ?_, hrel⟩
    rw [decodeRep_eq_some_iff, encodeRep_eq_of_mul_sq_eq_one hW, ZMod.natCast_zmod_val]
    refine ⟨ZMod.val_lt _, ZMod.not_isNeg_abs p_mod_two _, ?_, ?_, ?_, ?_⟩
    · rw [hCy, ZMod.abs_sq]
      exact (Proofs.div_eq_of_sq_eq_div hy1 hS).symm
    · rw [hCx]
      exact ZMod.not_isNeg_abs p_mod_two _
    · rw [hCx, hCy]
      exact not_isNeg_abs_xRot_mul_yC P
    · rw [hCy]
      exact yC_ne_zero hxy

/-- **Decoding then encoding**: a decoded point encodes to its encoding. -/
theorem encodeRep_decodeRep {s : ℕ} {P : edwards.Point} (h : decodeRep s = some P) :
    encodeRep P = s := by
  obtain ⟨hs, hneg, hy, hx, hxy, hy0⟩ := decodeRep_eq_some_iff.mp h
  have hu2 := one_add_sq_ne_zero_of_decodeRep h
  have hyu : P.y * (1 + (s : ZMod p) ^ 2) = 1 - (s : ZMod p) ^ 2 := (eq_div_iff hu2).mp hy
  by_cases hx0 : P.x = 0
  · have hy1 : P.y = 1 :=
      (y_eq_one_or_eq_neg_one_of_x_eq_zero P.equation hx0).resolve_right
        (decodeRep_y_ne_neg_one h)
    have hs0 : (s : ZMod p) = 0 := by
      rw [hy1, one_mul] at hyu
      have h2 : (2 : ZMod p) * (s : ZMod p) ^ 2 = 0 := by linear_combination hyu
      exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
    have hs' : s = 0 := by
      rw [← ZMod.val_cast_of_lt hs, hs0, ZMod.val_zero]
    rw [hs', encodeRep_of_mul_eq_zero (by rw [hx0, zero_mul])]
  · have hxy0 : P.x * P.y ≠ 0 := mul_ne_zero hx0 hy0
    have hW := encW_mul_sq_eq_one (even_decodeRep h) hxy0
    have hrot : xRot P = P.x := ite_eq_right hxy
    have hyC : yC P = P.y := by
      unfold yC
      rw [hrot, ite_eq_right hx]
      exact ite_eq_right hxy
    have hD := denC_sq hW
    rw [hyC] at hD
    have hS := Proofs.sq_eq_div_of hD
    have h1y : 1 + P.y ≠ 0 := fun h' =>
      y_ne_neg_one_of_x_ne_zero P.equation hx0 (by linear_combination h')
    have hs2 : (s : ZMod p) ^ 2 = (1 - P.y) / (1 + P.y) := by
      rw [eq_div_iff h1y]
      exact Proofs.sq_mul_one_add_eq hyu
    rw [encodeRep_eq_of_mul_sq_eq_one hW, hyC]
    have hSs : (denC P * (1 - P.y)).abs = (s : ZMod p) :=
      ZMod.eq_of_sq_eq_of_isNeg_iff p_mod_two (by rw [ZMod.abs_sq, hS, hs2])
        (iff_of_false (ZMod.not_isNeg_abs p_mod_two _) hneg)
    rw [hSs, ZMod.val_cast_of_lt hs]

/-- **Invariance on classes**: representatives of one class have the same encoding. -/
theorem encodeRep_rel {P Q : edwards.Point} (hP : Even P) (h : edwards.Rel P Q) :
    encodeRep P = encodeRep Q := by
  have hQ : Even Q := even_of_rel hP h
  obtain ⟨Q₁, h₁, r₁⟩ := decodeRep_encodeRep hP
  obtain ⟨Q₂, h₂, r₂⟩ := decodeRep_encodeRep hQ
  obtain ⟨-, -, -, hx₁, hxy₁, hy₁⟩ := decodeRep_eq_some_iff.mp h₁
  obtain ⟨-, -, -, hx₂, hxy₂, hy₂⟩ := decodeRep_eq_some_iff.mp h₂
  have hQ₁₂ : Q₁ = Q₂ :=
    eq_of_rel_of_canonical (rel_trans (rel_trans (rel_symm r₁) h) r₂) hx₁ hxy₁ hy₁
      (decodeRep_y_ne_neg_one h₁) hx₂ hxy₂ hy₂ (decodeRep_y_ne_neg_one h₂)
  rw [← encodeRep_decodeRep h₁, ← encodeRep_decodeRep h₂, hQ₁₂]

/-- **The encoding separates the classes**: two even points have the same encoding iff they are
in the same class. -/
theorem encodeRep_eq_iff {P Q : edwards.Point} (hP : Even P) (hQ : Even Q) :
    encodeRep P = encodeRep Q ↔ edwards.Rel P Q := by
  constructor
  · intro h
    obtain ⟨Q₁, h₁, r₁⟩ := decodeRep_encodeRep hP
    obtain ⟨Q₂, h₂, r₂⟩ := decodeRep_encodeRep hQ
    rw [h, h₂, Option.some.injEq] at h₁
    exact rel_trans r₁ (h₁ ▸ rel_symm r₂)
  · exact encodeRep_rel hP

/-! ### The quotient level -/

/-- **The ristretto255 encoding** of a group element: the encoding of any representative
(`encode_mk`), a natural number below `p` (`encode_lt`). Hidden. -/
noncomputable def encode (x : Ristretto) : ℕ :=
  encodeRep (Classical.choose (mk_surjective x))

theorem encode_mk {P : edwards.Point} (hP : Even P) : encode (mk P hP) = encodeRep P := by
  unfold encode
  obtain ⟨h, hmk⟩ := Classical.choose_spec (mk_surjective (mk P hP))
  exact encodeRep_rel h (mk_eq_mk_iff.mp hmk)

theorem encode_lt (x : Ristretto) : encode x < p := by
  obtain ⟨P, hP, rfl⟩ := mk_surjective x
  rw [encode_mk]
  exact encodeRep_lt P

theorem not_isNeg_encode (x : Ristretto) : ¬ ((encode x : ℕ) : ZMod p).isNeg := by
  obtain ⟨P, hP, rfl⟩ := mk_surjective x
  rw [encode_mk]
  exact not_isNeg_encodeRep P

/-- **The ristretto255 decoding** of a natural number: the class of `decodeRep s`
(`decode_eq_some_iff : decode s = some x ↔ encode x = s`). Hidden. -/
noncomputable def decode (s : ℕ) : Option Ristretto :=
  if h : ∃ P, decodeRep s = some P then
    some (mk (Classical.choose h) (even_decodeRep (Classical.choose_spec h)))
  else none

/-- `decode s` is the class of `decodeRep s`. -/
theorem decode_eq_some_iff_decodeRep {s : ℕ} {x : Ristretto} :
    decode s = some x ↔ ∃ (P : edwards.Point) (h : decodeRep s = some P),
      mk P (even_decodeRep h) = x := by
  unfold decode
  constructor
  · intro hx
    by_cases h : ∃ P, decodeRep s = some P
    · rw [dite_eq_left h, Option.some.injEq] at hx
      exact ⟨_, Classical.choose_spec h, hx⟩
    · rw [dite_eq_right h] at hx
      cases hx
  · rintro ⟨P, hP, rfl⟩
    have h : ∃ P, decodeRep s = some P := ⟨P, hP⟩
    rw [dite_eq_left h]
    congr 1
    have hPQ : P = Classical.choose h := Option.some.inj (hP.symm.trans (Classical.choose_spec h))
    rw [mk_eq_mk_iff]
    exact rel_of_eq hPQ.symm

theorem decode_eq_none_iff {s : ℕ} : decode s = none ↔ decodeRep s = none := by
  unfold decode
  by_cases h : ∃ P, decodeRep s = some P
  · rw [dite_eq_left h]
    refine iff_of_false (Option.some_ne_none _) fun h' => ?_
    obtain ⟨P, hP⟩ := h
    rw [h'] at hP
    cases hP
  · rw [dite_eq_right h]
    refine iff_of_true rfl ?_
    rcases hd : decodeRep s with _ | P
    · rfl
    · exact absurd ⟨P, hd⟩ h

/-- **Decoding is the partial inverse of encoding**: `decode s = some x ↔ encode x = s`. -/
theorem decode_eq_some_iff {s : ℕ} {x : Ristretto} : decode s = some x ↔ encode x = s := by
  rw [decode_eq_some_iff_decodeRep]
  constructor
  · rintro ⟨P, hP, rfl⟩
    rw [encode_mk]
    exact encodeRep_decodeRep hP
  · intro hs
    obtain ⟨P, hP, rfl⟩ := mk_surjective x
    rw [encode_mk] at hs
    obtain ⟨Q, hQ, hrel⟩ := decodeRep_encodeRep hP
    rw [hs] at hQ
    exact ⟨Q, hQ, mk_eq_mk_iff.mpr (rel_symm hrel)⟩

theorem decode_encode (x : Ristretto) : decode (encode x) = some x :=
  decode_eq_some_iff.mpr rfl

theorem encode_decode {s : ℕ} {x : Ristretto} (h : decode s = some x) : encode x = s :=
  decode_eq_some_iff.mp h

/-- **The encoding is injective.** -/
theorem encode_injective : Function.Injective encode := by
  intro x y h
  have hx := decode_encode x
  rw [h, decode_encode, Option.some.injEq] at hx
  exact hx.symm

theorem encode_inj {x y : Ristretto} : encode x = encode y ↔ x = y :=
  encode_injective.eq_iff

theorem decode_isSome_iff {s : ℕ} : (decode s).isSome ↔ ∃ x, encode x = s := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun x => decode_eq_some_iff

/-- The identity encodes to `0`. -/
theorem encode_zero : encode 0 = 0 := by
  rw [← mk_zero Even.zero, encode_mk, encodeRep_zero]

theorem decode_zero : decode 0 = some 0 :=
  decode_eq_some_iff.mpr encode_zero

/-! ### The basepoint -/

/-- **The encoding of the basepoint** (RFC 9496 §A.1, dalek's `RISTRETTO_BASEPOINT_COMPRESSED`):
the bytes `e2 f2 ae 0a 6a bc 4e 71 a8 84 a9 61 c5 00 51 5f 58 e3 0b 6a a5 82 dd 8d b6 a6 59 45
e0 8d 2d 76`, little-endian. -/
theorem encodeRep_basepoint : encodeRep curve25519.basepoint =
    53453403443306840533278073560698739391446669128918427283046925944918568268514 :=
  Proofs.encodeRep_of_basepoint_coords _ basepoint_x_eq basepoint_y_eq

theorem encode_basepoint : encode basepoint =
    53453403443306840533278073560698739391446669128918427283046925944918568268514 := by
  rw [basepoint_def, encode_mk, encodeRep_basepoint]

theorem decode_basepoint : decode
    53453403443306840533278073560698739391446669128918427283046925944918568268514 =
      some basepoint :=
  decode_eq_some_iff.mpr encode_basepoint

end Ristretto

end curve25519
