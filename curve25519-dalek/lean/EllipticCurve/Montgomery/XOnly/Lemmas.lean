/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.Montgomery.XOnly.Defs
import all EllipticCurve.Montgomery.XOnly.Defs
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # Montgomery models: x-only arithmetic, lemmas

The audited statements about the x-only arithmetic of `EllipticCurve.Montgomery.XOnly.Defs`:

- which `u` are `u`-coordinates of points (`exists_point_with_u_iff`), and the twist dichotomy
  over a finite field (`exists_point_u_or_twist`);
- the well-definedness of `xMul` (`xMul_eq_u_nsmul`, `xMul_eq_u_nsmul_twist`) and its values at
  `0` and `1`;
- the correctness of the RFC 7748 formulas with respect to `XZ.Represents`
  (`XZ.represents_xDBL`, `XZ.represents_xADD`, with the degenerate cases: the point at
  infinity, the 2-torsion point `(0, 0)`, `Q₁ = ± Q₂`);
- the ladder: `ladder_eq_u_nsmul` (`u(k • Q)` for `u(Q) ≠ 0`, `k < 2 ^ bits`), `ladder_zero`,
  `ladder_twist` (the ladder only depends on `A`), and `ladder_eq_xMul`.

The ladder invariant: after the bits `bits - 1, …, t` of `k` have been processed, the canonical
pair `cswap swap (x_2 : z_2) (x_3 : z_3)` represents `(m • Q, (m + 1) • Q)` with
`m = k / 2 ^ t` (stated bottom-up as `m ↦ m · 2 ^ t + k % 2 ^ t`, `ladderLoop_inv`). -/

universe u

namespace MontgomeryModel

variable {F : Type u} [Field F] {M : MontgomeryModel F}

/-! ### The twist -/

/-- The twist has the same ladder constant. -/
@[simp]
theorem a24_twist (M : MontgomeryModel F) (c : F) : (M.twist c).a24 = M.a24 := by
  simp only [a24, twist_A]

/-- `0` is a square, so a non-square is nonzero. -/
theorem ne_zero_of_not_isSquare {c : F} (hc : ¬ IsSquare c) : c ≠ 0 := fun h =>
  hc (h ▸ IsSquare.zero)

/-! ### Points with a given `u`-coordinate -/

section Points

variable [M.IsNonsingular]

/-- `u` is the `u`-coordinate of a point of `M` iff `u = 0` (the points `∞` and `(0, 0)`) or
`rhs u / B` is a square. -/
theorem exists_point_with_u_iff (u : F) :
    (∃ P : M.Point, P.u = u) ↔ u = 0 ∨ IsSquare (M.rhs u / M.B) := by
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  constructor
  · rintro ⟨P, rfl⟩
    rcases Point.cases P with rfl | ⟨u, v, h, rfl⟩
    · exact Or.inl u_zero
    · refine Or.inr ⟨v, ?_⟩
      rw [u_some, div_eq_iff hB]
      linear_combination -(equation_iff_rhs.mp h)
  · rintro (rfl | ⟨r, hr⟩)
    · exact ⟨0, u_zero⟩
    · refine ⟨Point.some u r ?_, u_some _⟩
      rw [equation_iff_rhs]
      rw [div_eq_iff hB] at hr
      linear_combination -hr

/-- Over a finite field, every `u` is the `u`-coordinate of a point of `M` or of its twist by a
non-square `c`: `rhs u / B` or `rhs u / (B c)` is a square. -/
theorem exists_point_u_or_twist [Finite F] {c : F} (hc : ¬ IsSquare c) (u : F) :
    (∃ P : M.Point, P.u = u) ∨ ∃ P : (M.twist c).Point, P.u = u := by
  classical
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  have := M.isNonsingular_twist hc0
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  rw [exists_point_with_u_iff, exists_point_with_u_iff, twist_B, twist_rhs]
  by_cases hu : u = 0
  · exact Or.inl (Or.inl hu)
  by_cases hr : IsSquare (M.rhs u / M.B)
  · exact Or.inl (Or.inr hr)
  refine Or.inr (Or.inr ?_)
  by_cases hr0 : M.rhs u = 0
  · rw [hr0, zero_div]
    exact IsSquare.zero
  let _ := Fintype.ofFinite F
  have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr hr
  have h2 := quadraticChar_neg_one_iff_not_isSquare.mpr hc
  rw [← quadraticChar_one_iff_isSquare (div_ne_zero hr0 (mul_ne_zero hB hc0))]
  have h : M.rhs u / M.B = M.rhs u / (M.B * c) * c := by
    field_simp
  rw [h, map_mul, h2] at h1
  linear_combination -h1

end Points

/-! ### Multiples of 2-torsion points and of points with the same `u` -/

private theorem nsmul_of_add_self_eq_zero {G : Type*} [AddMonoid G] {Q : G} (h : Q + Q = 0)
    (n : ℕ) : n • Q = if Even n then 0 else Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih]
    by_cases hn : Even n
    · rw [ite_eq_left hn, ite_eq_right (by rwa [Nat.even_add_one, not_not]), zero_add]
    · rw [ite_eq_right hn, ite_eq_left (by rwa [Nat.even_add_one]), h]

section Nsmul

variable [M.IsNonsingular]

/-- A point with `u = 0` (`∞` or `(0, 0)`) is 2-torsion. -/
theorem add_self_eq_zero_of_u_eq_zero {Q : M.Point} (h : Q.u = 0) : Q + Q = 0 := by
  rcases Point.cases Q with rfl | ⟨u, v, hQ, rfl⟩
  · exact add_zero 0
  · rw [u_some] at h
    subst h
    obtain rfl := v_eq_zero_of_u_eq_zero IsNonsingular.B_ne_zero hQ rfl
    exact some_add_some_eq_zero hQ hQ rfl (by rw [neg_zero])

/-- All multiples of a point with `u = 0` have `u = 0`. -/
theorem u_nsmul_of_u_eq_zero {Q : M.Point} (h : Q.u = 0) (n : ℕ) : (n • Q).u = 0 := by
  rw [nsmul_of_add_self_eq_zero (add_self_eq_zero_of_u_eq_zero h)]
  split_ifs
  · exact u_zero
  · exact h

/-- Two points with the same nonzero `u`-coordinate are equal or opposite. -/
theorem eq_or_eq_neg_of_u_eq {Q Q' : M.Point} (h : Q.u = Q'.u) (hu : Q.u ≠ 0) :
    Q' = Q ∨ Q' = -Q := by
  rcases Point.cases Q with rfl | ⟨u, v, hQ, rfl⟩
  · exact absurd u_zero hu
  rw [u_some] at hu
  rcases Point.cases Q' with rfl | ⟨u', v', hQ', rfl⟩
  · rw [u_some, u_zero] at h
    exact absurd h hu
  rw [u_some, u_some] at h
  subst h
  have hsq : v' ^ 2 = v ^ 2 := by
    apply mul_left_cancel₀ (IsNonsingular.B_ne_zero (M := M))
    unfold Equation at hQ hQ'
    rw [hQ, hQ']
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by rw [neg_some])

/-- The `u`-coordinate of `n • Q` only depends on the `u`-coordinate of `Q`. -/
theorem u_nsmul_eq_of_u_eq {Q Q' : M.Point} (h : Q.u = Q'.u) (n : ℕ) :
    (n • Q).u = (n • Q').u := by
  by_cases hu : Q.u = 0
  · rw [u_nsmul_of_u_eq_zero hu, u_nsmul_of_u_eq_zero (h ▸ hu)]
  · rcases eq_or_eq_neg_of_u_eq h hu with rfl | rfl
    · rfl
    · rw [neg_nsmul, u_neg]

/-- A `u`-coordinate attained both on `M` and on its twist by a non-square `c` is `0` or that
of a 2-torsion point, and the multiples of the two points have the same `u`. -/
theorem u_nsmul_eq_u_nsmul_twist {c : F} (hc : ¬ IsSquare c) [(M.twist c).IsNonsingular]
    {P : M.Point} {Q : (M.twist c).Point} (h : P.u = Q.u) (n : ℕ) : (n • P).u = (n • Q).u := by
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  by_cases hu : P.u = 0
  · rw [u_nsmul_of_u_eq_zero hu, u_nsmul_of_u_eq_zero (h ▸ hu)]
  rcases Point.cases P with rfl | ⟨u, v, hP, rfl⟩
  · exact absurd u_zero hu
  rw [u_some] at hu
  rcases Point.cases Q with rfl | ⟨u', w, hQ, rfl⟩
  · rw [u_some, u_zero] at h
    exact absurd h hu
  rw [u_some, u_some] at h
  subst h
  have hP' : M.B * v ^ 2 = M.rhs u := equation_iff_rhs.mp hP
  have hQ' : M.B * c * w ^ 2 = M.rhs u := by
    have := equation_iff_rhs.mp hQ
    rwa [twist_B, twist_rhs] at this
  by_cases hv : v = 0
  · subst hv
    have hw : w = 0 := by
      have h0 : M.B * c * w ^ 2 = 0 := by rw [hQ', ← hP']; ring
      exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h0).resolve_left (mul_ne_zero hB hc0))
    subst hw
    rw [nsmul_of_add_self_eq_zero (some_add_some_eq_zero hP hP rfl (by rw [neg_zero])),
      nsmul_of_add_self_eq_zero (some_add_some_eq_zero hQ hQ rfl (by rw [neg_zero]))]
    split_ifs
    · rw [u_zero, u_zero]
    · rw [u_some, u_some]
  · exfalso
    have hw : w ≠ 0 := by
      rintro rfl
      apply hv
      have h0 : M.B * v ^ 2 = 0 := by rw [hP', ← hQ']; ring
      exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h0).resolve_left hB)
    apply hc
    refine ⟨v / w, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hw hw)]
    apply mul_left_cancel₀ hB
    linear_combination hQ' - hP'

end Nsmul

/-! ### `xMul` -/

section XMul

variable [M.IsNonsingular]

/-- `xMul` computes `u(n • Q)` on the `u`-coordinate of any point `Q` of `M`. -/
theorem xMul_eq_u_nsmul (c : F) (n : ℕ) (Q : M.Point) : M.xMul c n Q.u = (n • Q).u := by
  have h : ∃ P : M.Point, P.u = Q.u := ⟨Q, rfl⟩
  unfold xMul
  rw [dite_eq_left h]
  exact u_nsmul_eq_of_u_eq h.choose_spec n

/-- `xMul` computes `u(n • Q)` on the `u`-coordinate of any point `Q` of the twist by a
non-square `c`. -/
theorem xMul_eq_u_nsmul_twist {c : F} (hc : ¬ IsSquare c) [(M.twist c).IsNonsingular] (n : ℕ)
    (Q : (M.twist c).Point) : M.xMul c n Q.u = (n • Q).u := by
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  unfold xMul
  by_cases h : ∃ P : M.Point, P.u = Q.u
  · rw [dite_eq_left h]
    exact u_nsmul_eq_u_nsmul_twist hc h.choose_spec n
  · have h' : ∃ Q' : (M.twist c).Point, Q'.u = Q.u := ⟨Q, rfl⟩
    rw [dite_eq_right h, dite_eq_right hc0, dite_eq_left h']
    exact u_nsmul_eq_of_u_eq h'.choose_spec n

/-- `xMul` at `u = 0` is `0`. -/
@[simp]
theorem xMul_zero_right (c : F) (n : ℕ) : M.xMul c n 0 = 0 := by
  have h := xMul_eq_u_nsmul c n (0 : M.Point)
  rwa [u_zero, smul_zero, u_zero] at h

/-- `xMul` by `0` is `0`. -/
@[simp]
theorem xMul_zero_left (c : F) (u : F) : M.xMul c 0 u = 0 := by
  unfold xMul
  split_ifs <;> simp only [zero_nsmul, u_zero]

/-- `xMul` by `1` is the identity, over a finite field and for a non-square `c` (every `u`
lifts to `M` or to the twist). -/
theorem xMul_one [Finite F] {c : F} (hc : ¬ IsSquare c) (u : F) : M.xMul c 1 u = u := by
  have := M.isNonsingular_twist (ne_zero_of_not_isSquare hc)
  rcases exists_point_u_or_twist (M := M) hc u with ⟨Q, rfl⟩ | ⟨Q, rfl⟩
  · rw [xMul_eq_u_nsmul, one_nsmul]
  · rw [xMul_eq_u_nsmul_twist hc, one_nsmul]

end XMul

private theorem four_ne_zero' (M : MontgomeryModel F) [M.IsNonsingular] : (4 : F) ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := IsNonsingular.two_ne_zero (M := M)
  rw [show (4 : F) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

/-- `4 a24 = A - 2`. -/
theorem four_mul_a24 (M : MontgomeryModel F) [M.IsNonsingular] : 4 * M.a24 = M.A - 2 := by
  have h4 := four_ne_zero' M
  rw [a24]
  field_simp

namespace XZ

/-! ### The representation predicate -/

section Represents

variable [M.IsNonsingular]

/-- `(U : W)` represents `∞` iff `W = 0` and `U ≠ 0`. -/
theorem represents_zero_iff {P : XZ F} : P.Represents (0 : M.Point) ↔ P.W = 0 ∧ P.U ≠ 0 := by
  simp [Represents]

/-- `(U : W)` represents the affine point `(u, v)` iff `W ≠ 0` and `U = u W`. -/
theorem represents_some_iff {P : XZ F} {u v : F} (h : M.Equation u v) :
    P.Represents (Point.some u v h) ↔ P.W ≠ 0 ∧ P.U = u * P.W := by
  simp [Represents, some_ne_zero h]

/-- The affine coordinate of a representative is the `u`-coordinate of the point. -/
theorem toU_of_represents {P : XZ F} {Q : M.Point} (h : P.Represents Q) : P.toU = Q.u := by
  rcases h with ⟨rfl, hW, _⟩ | ⟨_, hW, hU⟩
  · rw [toU, hW, div_zero, u_zero]
  · rw [toU, hU, mul_div_assoc, div_self hW, mul_one]

end Represents

/-! ### Correctness of `xDBL` and `xADD` -/

private theorem cert_dbl_W (a24 A B u v W : F) (h4 : 4 * a24 = A - 2)
    (h : B * v ^ 2 = u ^ 3 + A * u ^ 2 + u) :
    ((u * W + W) ^ 2 - (u * W - W) ^ 2) *
      ((u * W + W) ^ 2 + a24 * ((u * W + W) ^ 2 - (u * W - W) ^ 2)) =
      4 * W ^ 4 * (B * v ^ 2) := by
  linear_combination (4 * u ^ 2 * W ^ 4) * h4 - (4 * W ^ 4) * h

private theorem cert_dbl_U (B u v W u₂ : F) (key : B * u₂ * (2 * v) ^ 2 = (u ^ 2 - 1) ^ 2) :
    (u * W + W) ^ 2 * (u * W - W) ^ 2 = u₂ * (4 * W ^ 4 * (B * v ^ 2)) := by
  linear_combination (-(W ^ 4)) * key

section Formulas

variable [M.IsNonsingular]

/-- `xDBL` doubles: if `(U : W)` represents `Q` then `xDBL (U : W)` represents `2 • Q`. All
cases: `Q = ∞`, `Q` of order `2` (`v = 0`, where `2 • Q = ∞` and `u² ≠ 1` by
nonsingularity), and `v ≠ 0` (the tangent identity `B u(2 Q) (2 v)² = (u² - 1)²`). -/
theorem represents_xDBL {P : XZ F} {Q : M.Point} (h : P.Represents Q) :
    (M.xDBL P).Represents (2 • Q) := by
  have h2 : (2 : F) ≠ 0 := IsNonsingular.two_ne_zero (M := M)
  have h4 : (4 : F) ≠ 0 := four_ne_zero' M
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  have ha24 := four_mul_a24 M
  obtain ⟨U, W⟩ := P
  rcases Point.cases Q with rfl | ⟨u, v, hQ, rfl⟩
  · rw [represents_zero_iff] at h
    obtain ⟨hW, hU⟩ := h
    change W = 0 at hW
    change U ≠ 0 at hU
    subst hW
    rw [smul_zero, represents_zero_iff]
    refine ⟨by change _ * _ = (0 : F); ring, ?_⟩
    change (U + 0) ^ 2 * (U - 0) ^ 2 ≠ 0
    rw [add_zero, sub_zero]
    exact mul_ne_zero (pow_ne_zero 2 hU) (pow_ne_zero 2 hU)
  · rw [represents_some_iff] at h
    obtain ⟨hW, hU⟩ := h
    change W ≠ 0 at hW
    change U = u * W at hU
    subst hU
    have hQ' : M.B * v ^ 2 = u ^ 3 + M.A * u ^ 2 + u := hQ
    have hW₂ : (M.xDBL ⟨u * W, W⟩).W = 4 * W ^ 4 * (M.B * v ^ 2) :=
      cert_dbl_W M.a24 M.A M.B u v W ha24 hQ'
    have hU₂ : (M.xDBL ⟨u * W, W⟩).U = (u * W + W) ^ 2 * (u * W - W) ^ 2 := rfl
    by_cases hv : v = 0
    · subst hv
      rw [two_nsmul, some_add_some_eq_zero hQ hQ rfl (by rw [neg_zero]), represents_zero_iff,
        hW₂, hU₂]
      refine ⟨by ring, ?_⟩
      have hu1 : u + 1 ≠ 0 := by
        intro h1
        obtain rfl : u = -1 := by linear_combination h1
        apply IsNonsingular.A_sq_ne_four (M := M)
        have hA : M.A = 2 := by linear_combination -hQ'
        rw [hA]
        norm_num
      have hu2 : u - 1 ≠ 0 := by
        intro h1
        obtain rfl : u = 1 := by linear_combination h1
        apply IsNonsingular.A_sq_ne_four (M := M)
        have hA : M.A = -2 := by linear_combination -hQ'
        rw [hA]
        norm_num
      rw [show u * W + W = W * (u + 1) by ring, show u * W - W = W * (u - 1) by ring]
      exact mul_ne_zero (pow_ne_zero 2 (mul_ne_zero hW hu1)) (pow_ne_zero 2 (mul_ne_zero hW hu2))
    · have key := B_mul_u_two_nsmul_mul_sq hQ hv
      rw [two_nsmul, some_add_self hQ hv, represents_some_iff, hW₂, hU₂]
      rw [two_nsmul, some_add_self hQ hv, u_some] at key
      refine ⟨mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 4 hW)) (mul_ne_zero hB (pow_ne_zero 2 hv)),
        ?_⟩
      exact cert_dbl_U M.B u v W _ key

/-- `xADD` adds: if `P₁`, `P₂` represent `Q₁`, `Q₂` and `u₁ = u(Q₁ - Q₂) ≠ 0` then
`xADD P₁ P₂ u₁` represents `Q₁ + Q₂`. All cases: `Q₁ = ∞` or `Q₂ = ∞`, `Q₁ = -Q₂` (then
`u₁ = u(2 Q₁) ≠ 0` and the sum is `∞`), `Q₁ = Q₂` (excluded by `u₁ ≠ 0`), and distinct
`u`-coordinates (the identity `u(Q₁ + Q₂) u(Q₁ - Q₂) (u₁ - u₂)² = (u₁ u₂ - 1)²`). -/
theorem represents_xADD {P₁ P₂ : XZ F} {Q₁ Q₂ : M.Point} (h₁ : P₁.Represents Q₁)
    (h₂ : P₂.Represents Q₂) {u₁ : F} (hd : (Q₁ - Q₂).u = u₁) (hu : u₁ ≠ 0) :
    (xADD P₁ P₂ u₁).Represents (Q₁ + Q₂) := by
  have h2 : (2 : F) ≠ 0 := IsNonsingular.two_ne_zero (M := M)
  have h4 : (4 : F) ≠ 0 := four_ne_zero' M
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  obtain ⟨U₁, W₁⟩ := P₁
  obtain ⟨U₂, W₂⟩ := P₂
  have hU₃ : (xADD ⟨U₁, W₁⟩ ⟨U₂, W₂⟩ u₁).U = 4 * (U₁ * U₂ - W₁ * W₂) ^ 2 := by
    change ((U₂ - W₂) * (U₁ + W₁) + (U₂ + W₂) * (U₁ - W₁)) ^ 2 = _
    ring
  have hW₃ : (xADD ⟨U₁, W₁⟩ ⟨U₂, W₂⟩ u₁).W = 4 * u₁ * (U₂ * W₁ - U₁ * W₂) ^ 2 := by
    change u₁ * ((U₂ - W₂) * (U₁ + W₁) - (U₂ + W₂) * (U₁ - W₁)) ^ 2 = _
    ring
  rcases Point.cases Q₁ with rfl | ⟨a, b, hQ₁, rfl⟩
  · rw [represents_zero_iff] at h₁
    obtain ⟨hW₁, hU₁⟩ := h₁
    change W₁ = 0 at hW₁
    change U₁ ≠ 0 at hU₁
    subst hW₁
    rw [zero_sub, u_neg] at hd
    rw [zero_add]
    rcases Point.cases Q₂ with rfl | ⟨c, d, hQ₂, rfl⟩
    · rw [u_zero] at hd
      exact absurd hd.symm hu
    rw [u_some] at hd
    subst hd
    rw [represents_some_iff] at h₂ ⊢
    obtain ⟨hW₂, hU₂⟩ := h₂
    change W₂ ≠ 0 at hW₂
    change U₂ = c * W₂ at hU₂
    subst hU₂
    rw [hU₃, hW₃]
    refine ⟨?_, by ring⟩
    rw [show (c * W₂ * 0 - U₁ * W₂) ^ 2 = (U₁ * W₂) ^ 2 by ring]
    exact mul_ne_zero (mul_ne_zero h4 hu) (pow_ne_zero 2 (mul_ne_zero hU₁ hW₂))
  rcases Point.cases Q₂ with rfl | ⟨c, d, hQ₂, rfl⟩
  · rw [represents_zero_iff] at h₂
    obtain ⟨hW₂, hU₂⟩ := h₂
    change W₂ = 0 at hW₂
    change U₂ ≠ 0 at hU₂
    subst hW₂
    rw [sub_zero, u_some] at hd
    subst hd
    rw [add_zero, represents_some_iff]
    rw [represents_some_iff] at h₁
    obtain ⟨hW₁, hU₁⟩ := h₁
    change W₁ ≠ 0 at hW₁
    change U₁ = a * W₁ at hU₁
    subst hU₁
    rw [hU₃, hW₃]
    refine ⟨?_, by ring⟩
    rw [show (U₂ * W₁ - a * W₁ * 0) ^ 2 = (U₂ * W₁) ^ 2 by ring]
    exact mul_ne_zero (mul_ne_zero h4 hu) (pow_ne_zero 2 (mul_ne_zero hU₂ hW₁))
  rw [represents_some_iff] at h₁ h₂
  obtain ⟨hW₁, hU₁⟩ := h₁
  obtain ⟨hW₂, hU₂⟩ := h₂
  change W₁ ≠ 0 at hW₁
  change U₁ = a * W₁ at hU₁
  change W₂ ≠ 0 at hW₂
  change U₂ = c * W₂ at hU₂
  subst hU₁ hU₂
  have hQ₁' : M.B * b ^ 2 = a ^ 3 + M.A * a ^ 2 + a := hQ₁
  have hQ₂' : M.B * d ^ 2 = c ^ 3 + M.A * c ^ 2 + c := hQ₂
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = -d
    · rw [some_add_some_eq_zero hQ₁ hQ₂ rfl hbd, represents_zero_iff, hU₃, hW₃]
      refine ⟨by ring, ?_⟩
      have hQ₁₂ : Point.some a (-d) (equation_neg hQ₂) = Point.some a b hQ₁ := by
        subst hbd
        rfl
      have hd' : (2 • Point.some a b hQ₁).u = u₁ := by
        rw [two_nsmul, ← hd, sub_eq_add_neg, neg_some, hQ₁₂]
      have hb : b ≠ 0 := by
        rintro rfl
        rw [two_nsmul, some_add_some_eq_zero hQ₁ hQ₁ rfl (by rw [neg_zero]), u_zero] at hd'
        exact hu hd'.symm
      have key := B_mul_u_two_nsmul_mul_sq hQ₁ hb
      rw [hd'] at key
      have ha : a ^ 2 - 1 ≠ 0 := by
        intro h0
        have h' : M.B * u₁ * (2 * b) ^ 2 = 0 := by rw [key, h0]; ring
        exact mul_ne_zero (mul_ne_zero hB hu) (pow_ne_zero 2 (mul_ne_zero h2 hb)) h'
      rw [show a * W₁ * (a * W₂) - W₁ * W₂ = W₁ * W₂ * (a ^ 2 - 1) by ring]
      exact mul_ne_zero h4 (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hW₁ hW₂) ha))
    · exfalso
      have hsq : b ^ 2 = d ^ 2 := mul_left_cancel₀ hB (by rw [hQ₁', hQ₂'])
      obtain rfl := (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_right hbd
      rw [sub_eq_add_neg, neg_some, some_add_some_eq_zero hQ₁ _ rfl (neg_neg b).symm, u_zero]
        at hd
      exact hu hd.symm
  · have key := u_add_mul_u_sub_of_u_ne hQ₁ hQ₂ hac
    rw [hd, some_add_some_of_u_ne hQ₁ hQ₂ hac, u_some] at key
    rw [some_add_some_of_u_ne hQ₁ hQ₂ hac, represents_some_iff, hU₃, hW₃]
    refine ⟨?_, ?_⟩
    · rw [show c * W₂ * W₁ - a * W₁ * W₂ = W₁ * W₂ * (c - a) by ring]
      exact mul_ne_zero (mul_ne_zero h4 hu) (pow_ne_zero 2
        (mul_ne_zero (mul_ne_zero hW₁ hW₂) (sub_ne_zero.mpr (Ne.symm hac))))
    · linear_combination (-(4 * W₁ ^ 2 * W₂ ^ 2)) * key

/-- The affine coordinate of `xDBL (U : W)` for `(U : W)` representing `Q` is `u(2 • Q)`. -/
theorem toU_xDBL {P : XZ F} {Q : M.Point} (h : P.Represents Q) : (M.xDBL P).toU = (2 • Q).u :=
  toU_of_represents (represents_xDBL h)

/-- The affine coordinate of `xADD P₁ P₂ u₁` is `u(Q₁ + Q₂)`, under the hypotheses of
`represents_xADD`. -/
theorem toU_xADD {P₁ P₂ : XZ F} {Q₁ Q₂ : M.Point} (h₁ : P₁.Represents Q₁)
    (h₂ : P₂.Represents Q₂) {u₁ : F} (hd : (Q₁ - Q₂).u = u₁) (hu : u₁ ≠ 0) :
    (xADD P₁ P₂ u₁).toU = (Q₁ + Q₂).u :=
  toU_of_represents (represents_xADD h₁ h₂ hd hu)

end Formulas

/-! ### The ladder invariant -/

/-- The canonical pair of a ladder state: `cswap swap (x_2 : z_2) (x_3 : z_3)`. -/
private def canon (s : LadderState F) : XZ F × XZ F :=
  cswap s.swap s.R₀ s.R₁

section Ladder

variable [M.IsNonsingular]

/-- The "even" step: from `(X, Y)` representing `(m • Q, (m + 1) • Q)` to
`(xDBL X, xADD X Y u(Q))` representing `(2 m • Q, (2 m + 1) • Q)`. -/
private theorem step_even {Q : M.Point} (hu : Q.u ≠ 0) {X Y : XZ F} {m : ℕ}
    (h₀ : X.Represents (m • Q)) (h₁ : Y.Represents ((m + 1) • Q)) :
    (dbl M.a24 X).Represents ((2 * m) • Q) ∧ (add X Y Q.u).Represents ((2 * m + 1) • Q) := by
  have e₀ : (2 * m) • Q = 2 • m • Q := by rw [smul_smul]
  have e₁ : (2 * m + 1) • Q = m • Q + (m + 1) • Q := by
    rw [← add_nsmul, show m + (m + 1) = 2 * m + 1 by omega]
  have hd : (m • Q - (m + 1) • Q).u = Q.u := by rw [succ_nsmul, sub_add_cancel_left, u_neg]
  rw [e₀, e₁]
  exact ⟨represents_xDBL h₀, represents_xADD h₀ h₁ hd hu⟩

/-- The "odd" step: from `(X, Y)` representing `(m • Q, (m + 1) • Q)` to
`(xADD Y X u(Q), xDBL Y)` representing `((2 m + 1) • Q, (2 m + 2) • Q)`. -/
private theorem step_odd {Q : M.Point} (hu : Q.u ≠ 0) {X Y : XZ F} {m : ℕ}
    (h₀ : X.Represents (m • Q)) (h₁ : Y.Represents ((m + 1) • Q)) :
    (add Y X Q.u).Represents ((2 * m + 1) • Q) ∧
      (dbl M.a24 Y).Represents ((2 * m + 1 + 1) • Q) := by
  have e₀ : (2 * m + 1) • Q = (m + 1) • Q + m • Q := by
    rw [← add_nsmul, show m + 1 + m = 2 * m + 1 by omega]
  have e₁ : (2 * m + 1 + 1) • Q = 2 • (m + 1) • Q := by
    rw [smul_smul, show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
  have hd : ((m + 1) • Q - m • Q).u = Q.u := by rw [succ_nsmul, add_sub_cancel_left]
  rw [e₀, e₁]
  exact ⟨represents_xADD h₁ h₀ hd hu, represents_xDBL h₁⟩

/-- One ladder step preserves the invariant, with `m ↦ 2 m + k_t`. -/
private theorem ladderStep_inv {Q : M.Point} (hu : Q.u ≠ 0) {s : LadderState F} {m : ℕ}
    (h₀ : (canon s).1.Represents (m • Q)) (h₁ : (canon s).2.Represents ((m + 1) • Q))
    (kt : Bool) :
    (canon (ladderStep M.a24 Q.u s kt)).1.Represents ((2 * m + kt.toNat) • Q) ∧
      (canon (ladderStep M.a24 Q.u s kt)).2.Represents ((2 * m + kt.toNat + 1) • Q) := by
  obtain ⟨R₀, R₁, swap⟩ := s
  cases swap <;> cases kt <;> simp only [canon, ladderStep, cswap, Bool.xor_false, Bool.xor_true,
    Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true, add_zero,
    Bool.false_eq_true, ↓reduceIte] at h₀ h₁ ⊢
  · exact step_even hu h₀ h₁
  · exact step_odd hu h₀ h₁
  · exact step_even hu h₀ h₁
  · exact step_odd hu h₀ h₁

/-- The ladder invariant: the loop over the bits `t - 1, …, 0` maps a state representing
`(m • Q, (m + 1) • Q)` to one representing `(m' • Q, (m' + 1) • Q)` with
`m' = m · 2 ^ t + k % 2 ^ t`. -/
private theorem ladderLoop_inv {Q : M.Point} (hu : Q.u ≠ 0) (k : ℕ) (t : ℕ) :
    ∀ (s : LadderState F) (m : ℕ), (canon s).1.Represents (m • Q) →
      (canon s).2.Represents ((m + 1) • Q) →
      (canon (ladderLoop M.a24 Q.u k t s)).1.Represents ((m * 2 ^ t + k % 2 ^ t) • Q) ∧
        (canon (ladderLoop M.a24 Q.u k t s)).2.Represents ((m * 2 ^ t + k % 2 ^ t + 1) • Q) := by
  induction t with
  | zero =>
    intro s m h₀ h₁
    simpa only [ladderLoop, pow_zero, mul_one, Nat.mod_one, add_zero] using ⟨h₀, h₁⟩
  | succ t ih =>
    intro s m h₀ h₁
    obtain ⟨h₀', h₁'⟩ := ladderStep_inv hu h₀ h₁ (k.testBit t)
    have h := ih _ _ h₀' h₁'
    have e : (2 * m + (k.testBit t).toNat) * 2 ^ t + k % 2 ^ t =
        m * 2 ^ (t + 1) + k % 2 ^ (t + 1) := by
      rw [Nat.toNat_testBit, Nat.mod_pow_succ, pow_succ]
      ring
    rwa [e] at h

end Ladder

/-! ### The ladder at `u = 0` -/

private theorem dbl_W_eq_zero (a24 : F) {P : XZ F} (h : P.U * P.W = 0) : (dbl a24 P).W = 0 := by
  change ((P.U + P.W) ^ 2 - (P.U - P.W) ^ 2) * _ = 0
  rw [show (P.U + P.W) ^ 2 - (P.U - P.W) ^ 2 = 4 * (P.U * P.W) by ring, h]
  ring

private theorem add_W_zero (P Q : XZ F) : (add P Q 0).W = 0 :=
  zero_mul _

private theorem ladderStep_zero (a24 : F) {s : LadderState F} (h₀ : s.R₀.U * s.R₀.W = 0)
    (h₁ : s.R₁.U * s.R₁.W = 0) (kt : Bool) :
    (ladderStep a24 0 s kt).R₀.U * (ladderStep a24 0 s kt).R₀.W = 0 ∧
      (ladderStep a24 0 s kt).R₁.U * (ladderStep a24 0 s kt).R₁.W = 0 := by
  obtain ⟨R₀, R₁, swap⟩ := s
  dsimp only at h₀ h₁
  cases swap <;> cases kt <;>
    simp [ladderStep, cswap, dbl_W_eq_zero a24 h₀, dbl_W_eq_zero a24 h₁, add_W_zero]

private theorem ladderLoop_zero (a24 : F) (k t : ℕ) :
    ∀ s : LadderState F, s.R₀.U * s.R₀.W = 0 → s.R₁.U * s.R₁.W = 0 →
      (ladderLoop a24 0 k t s).R₀.U * (ladderLoop a24 0 k t s).R₀.W = 0 ∧
        (ladderLoop a24 0 k t s).R₁.U * (ladderLoop a24 0 k t s).R₁.W = 0 := by
  induction t with
  | zero => exact fun s h₀ h₁ => ⟨h₀, h₁⟩
  | succ t ih =>
    intro s h₀ h₁
    obtain ⟨h₀', h₁'⟩ := ladderStep_zero a24 h₀ h₁ (k.testBit t)
    exact ih _ h₀' h₁'

/-- The ladder at `u = 0` returns `0`: with `x₁ = 0` every state has `U W = 0` in both pairs. -/
theorem ladder_zero (a24 : F) (bits k : ℕ) : ladder a24 bits k 0 = 0 := by
  obtain ⟨h₀, h₁⟩ := ladderLoop_zero a24 k bits ⟨⟨1, 0⟩, ⟨0, 1⟩, false⟩ (mul_zero 1) (zero_mul 1)
  change (cswap _ _ _).1.toU = 0
  generalize ladderLoop a24 0 k bits ⟨⟨1, 0⟩, ⟨0, 1⟩, false⟩ = s at h₀ h₁
  obtain ⟨R₀, R₁, swap⟩ := s
  unfold toU
  cases swap <;> simp only [cswap, Bool.false_eq_true, ↓reduceIte] <;> rw [div_eq_zero_iff]
  · exact mul_eq_zero.mp h₀
  · exact mul_eq_zero.mp h₁

end XZ

namespace XZ

/-- The ladder loop over the bits `t - 1, …, 0` of `k` is the loop body folded over those bits. -/
theorem ladderLoop_eq_foldl (a24 x₁ : F) (k t : ℕ) (s : LadderState F) :
    ladderLoop a24 x₁ k t s =
      ((List.range t).reverse.map k.testBit).foldl (ladderStep a24 x₁) s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    rw [ladderLoop, ih, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, List.foldl_cons]

/-- The ladder over `bits` bits of `k` is the ladder over the bit sequence
`k.testBit (bits - 1), …, k.testBit 0`. -/
theorem ladderXZ_eq_ladderBitsXZ (a24 : F) (bits k : ℕ) (u : F) :
    ladderXZ a24 bits k u = ladderBitsXZ a24 ((List.range bits).reverse.map k.testBit) u := by
  simp only [ladderXZ, ladderBitsXZ, ladderLoop_eq_foldl]

end XZ

/-- The integer with the big-endian bits `bs`. -/
private def ofBitsBE (bs : List Bool) : ℕ :=
  bs.foldl (fun n b => 2 * n + b.toNat) 0

private theorem ofBitsBE_append (bs : List Bool) (b : Bool) :
    ofBitsBE (bs ++ [b]) = 2 * ofBitsBE bs + b.toNat := by
  simp only [ofBitsBE, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem ofBitsBE_lt (bs : List Bool) : ofBitsBE bs < 2 ^ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp [ofBitsBE]
  | append_singleton bs b ih =>
    rw [ofBitsBE_append, List.length_append, List.length_singleton, pow_succ]
    have := Bool.toNat_le b
    omega

private theorem testBits_ofBitsBE (bs : List Bool) :
    (List.range bs.length).reverse.map (ofBitsBE bs).testBit = bs := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
    rw [ofBitsBE_append, List.length_append, List.length_singleton, List.range_succ_eq_map,
      List.reverse_cons, List.map_append, List.map_reverse, List.map_map]
    have hbit : ∀ i, (2 * ofBitsBE bs + b.toNat).testBit (i + 1) = (ofBitsBE bs).testBit i := by
      intro i
      rw [Nat.testBit_succ]
      congr 1
      have := Bool.toNat_le b
      omega
    have h0 : (2 * ofBitsBE bs + b.toNat).testBit 0 = b := by
      rw [Nat.testBit_zero]
      cases b <;> simp
    simp only [Function.comp_def, Nat.succ_eq_add_one, hbit, List.map_cons, List.map_nil, h0]
    rw [← List.map_reverse, ih]

namespace XZ

/-- The ladder over the bit sequence `bs` is the ladder over `bs.length` bits of the integer
with these big-endian bits. -/
private theorem ladderBits_eq_ladder (a24 : F) (bs : List Bool) (u : F) :
    ladderBits a24 bs u = ladder a24 bs.length (ofBitsBE bs) u := by
  rw [ladder, ladderXZ_eq_ladderBitsXZ, testBits_ofBitsBE]
  rfl

end XZ

/-! ### The ladder of a model -/

/-- The ladder at `u = 0` returns `0`. -/
@[simp]
theorem ladder_zero (M : MontgomeryModel F) (bits k : ℕ) : M.ladder bits k 0 = 0 :=
  XZ.ladder_zero M.a24 bits k

/-- The ladder only depends on `A`: the twist has the same ladder. -/
@[simp]
theorem ladder_twist (M : MontgomeryModel F) (c : F) : (M.twist c).ladder = M.ladder := by
  funext bits k u
  simp only [ladder, a24_twist]

section LadderXMul

variable [M.IsNonsingular]

/-- The ladder computes `u(k • Q)` from `u(Q) ≠ 0`, for `k < 2 ^ bits`. -/
theorem ladder_eq_u_nsmul (Q : M.Point) (hu : Q.u ≠ 0) {bits k : ℕ} (hk : k < 2 ^ bits) :
    M.ladder bits k Q.u = (k • Q).u := by
  have h₀ : (XZ.canon ⟨⟨1, 0⟩, ⟨Q.u, 1⟩, false⟩).1.Represents ((0 : ℕ) • Q) := by
    rw [zero_nsmul, XZ.represents_zero_iff]
    exact ⟨rfl, one_ne_zero⟩
  have h₁ : (XZ.canon ⟨⟨1, 0⟩, ⟨Q.u, 1⟩, false⟩).2.Represents ((0 + 1 : ℕ) • Q) := by
    rw [zero_add, one_nsmul]
    rcases Point.cases Q with rfl | ⟨u, v, h, rfl⟩
    · exact absurd u_zero hu
    · rw [XZ.represents_some_iff]
      refine ⟨one_ne_zero, ?_⟩
      change (Point.some u v h).u = u * 1
      rw [u_some, mul_one]
  obtain ⟨h, _⟩ := XZ.ladderLoop_inv hu k bits _ 0 h₀ h₁
  rw [zero_mul, zero_add, Nat.mod_eq_of_lt hk] at h
  exact XZ.toU_of_represents h

omit [M.IsNonsingular] in
/-- The ladder computes `u(k • Q)` from `u(Q) ≠ 0` for a point `Q` of the twist, too. -/
theorem ladder_eq_u_nsmul_twist {c : F} [(M.twist c).IsNonsingular] (Q : (M.twist c).Point)
    (hu : Q.u ≠ 0) {bits k : ℕ} (hk : k < 2 ^ bits) : M.ladder bits k Q.u = (k • Q).u := by
  rw [← ladder_twist M c]
  exact ladder_eq_u_nsmul Q hu hk

/-- The ladder agrees with `xMul` on every `u` that lifts to `M` or to the twist by a
non-square `c`, for `k < 2 ^ bits`. -/
theorem ladder_eq_xMul_of_exists {c : F} (hc : ¬ IsSquare c) {bits k : ℕ} (hk : k < 2 ^ bits)
    {u : F} (h : (∃ P : M.Point, P.u = u) ∨ ∃ P : (M.twist c).Point, P.u = u) :
    M.ladder bits k u = M.xMul c k u := by
  have := M.isNonsingular_twist (ne_zero_of_not_isSquare hc)
  by_cases hu : u = 0
  · subst hu
    rw [ladder_zero, xMul_zero_right]
  rcases h with ⟨Q, rfl⟩ | ⟨Q, rfl⟩
  · rw [ladder_eq_u_nsmul Q hu hk, xMul_eq_u_nsmul]
  · rw [ladder_eq_u_nsmul_twist Q hu hk, xMul_eq_u_nsmul_twist hc]

/-- Over a finite field, the ladder is `xMul` for a non-square `c` and `k < 2 ^ bits`. -/
theorem ladder_eq_xMul [Finite F] {c : F} (hc : ¬ IsSquare c) {bits k : ℕ} (hk : k < 2 ^ bits)
    (u : F) : M.ladder bits k u = M.xMul c k u :=
  ladder_eq_xMul_of_exists hc hk (exists_point_u_or_twist hc u)

/-- Over a finite field, the ladder over a bit sequence `bs` is `xMul` for a non-square `c` at
the integer `n` with the big-endian bits `bs`: `u ↦ u(n • Q)` on the curve and on the twist. -/
theorem ladderBits_eq_xMul [Finite F] {c : F} (hc : ¬ IsSquare c) (bs : List Bool) (u : F) :
    ∃ n < 2 ^ bs.length, (List.range bs.length).reverse.map n.testBit = bs ∧
      M.ladderBits bs u = M.xMul c n u :=
  ⟨ofBitsBE bs, ofBitsBE_lt bs, testBits_ofBitsBE bs, by
    rw [ladderBits, XZ.ladderBits_eq_ladder, ← ladder, ladder_eq_xMul hc (ofBitsBE_lt bs)]⟩

end LadderXMul

end MontgomeryModel
