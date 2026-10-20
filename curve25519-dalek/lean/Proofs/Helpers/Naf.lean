/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Scalar.Notations
public import Curve25519.Edwards.Basic
public import Defs.Array
import Proofs.Helpers.AsInt
public section

/-! # The value of the top digits of a signed-digit recoding

The scalar multiplications run Horner's rule over the signed digits of a scalar from the top
down: the `256` digits of a non-adjacent form (`non_adjacent_form`) in base `2`, or the `64`
digits of `as_radix_16` in base `16`. After the digits `d[e], …` the accumulator represents
`nafTail d e • P` (resp. `radix16Tail d e • P`). Also the sum of a `zipWith` as a sum over
indices, for the multiscalar multiplications. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

/-- The value `∑_{k < 256 - e} 2^k d[e + k]` of the digits `d[e], …, d[255]`. -/
def nafTail (d : Array I8 256#usize) (e : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (256 - e), 2 ^ k * d[e + k]!.val

theorem nafTail_eq (d : Array I8 256#usize) (e : ℕ) (he : e < 256) :
    nafTail d e = d[e]!.val + 2 * nafTail d (e + 1) := by
  unfold nafTail
  rw [show 256 - e = 256 - (e + 1) + 1 by omega, Finset.sum_range_succ', Finset.mul_sum,
    pow_zero, one_mul, add_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ, show e + (k + 1) = e + 1 + k by omega]
  ring

/-- All digits are summed from `e = 0`: the value `asInt 1` of the digits. -/
theorem nafTail_zero (d : Array I8 256#usize) : nafTail d 0 = d.asInt 1 := by
  rw [Array.asInt_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zero_add, one_mul]

/-- If the digits from `e` on vanish, so does their value. -/
theorem nafTail_eq_zero (d : Array I8 256#usize) (e : ℕ)
    (h : ∀ k, e ≤ k → k < 256 → d[k]!.val = 0) : nafTail d e = 0 :=
  Finset.sum_eq_zero fun k hk => by
    rw [h (e + k) (Nat.le_add_right e k) (by have := Finset.mem_range.mp hk; omega), mul_zero]

/-- The value `∑_{k < 64 - e} 16^k d[e + k]` of the radix-`16` digits `d[e], …, d[63]`. -/
def radix16Tail (d : Array I8 64#usize) (e : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (64 - e), 16 ^ k * d[e + k]!.val

theorem radix16Tail_eq (d : Array I8 64#usize) (e : ℕ) (he : e < 64) :
    radix16Tail d e = d[e]!.val + 16 * radix16Tail d (e + 1) := by
  unfold radix16Tail
  rw [show 64 - e = 64 - (e + 1) + 1 by omega, Finset.sum_range_succ', Finset.mul_sum,
    pow_zero, one_mul, add_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ, show e + (k + 1) = e + 1 + k by omega]
  ring

theorem radix16Tail_zero (d : Array I8 64#usize) : radix16Tail d 0 = d.asInt 4 := by
  rw [Array.asInt_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zero_add, pow_mul]
  norm_num

theorem radix16Tail_sixtyFour (d : Array I8 64#usize) : radix16Tail d 64 = 0 := by
  simp [radix16Tail]

/-- The sum of `zipWith f l₁ l₂` is the sum of `f l₁[k] l₂[k]` over the indices of the shorter
list. -/
theorem sum_zipWith_eq {α β G : Type} [Inhabited α] [Inhabited β] [AddCommMonoid G]
    (f : α → β → G) (l₁ : List α) (l₂ : List β) :
    (List.zipWith f l₁ l₂).sum =
      ∑ k ∈ Finset.range (min l₁.length l₂.length), f l₁[k]! l₂[k]! := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      rw [List.zipWith_cons_cons, List.sum_cons, ih, List.length_cons, List.length_cons,
        Nat.add_min_add_right, Finset.sum_range_succ']
      simp [add_comm]

/-! ### Adding a signed digit -/

theorem sub_nsmul_eq (P Q : curve25519.edwards.Point) (n : ℕ) (d : ℤ)
    (h : (n : ℤ) = -d) : P - n • Q = P + d • Q := by
  rw [← natCast_zsmul, h, neg_zsmul, sub_neg_eq_add]

theorem add_nsmul_eq (P Q : curve25519.edwards.Point) (n : ℕ) (d : ℤ)
    (h : (n : ℤ) = d) : P + n • Q = P + d • Q := by
  rw [← natCast_zsmul, h]

/-- The digit `d` of a NAF of width `w ≤ 8` is odd and `|d| < 2^(w-1)`: its absolute value as a
`Usize` selects `|d| • P` from a table of odd multiples. -/
theorem naf_digit_abs {d : ℤ} {w : ℕ} (hw : w ≤ 8) (hd : d % 2 = 1 ∧ 2 * |d| < 2 ^ w) :
    |d| % 2 = 1 ∧ 2 * |d| < 2 ^ w ∧ -128 < d ∧ d < 128 := by
  have h8 : (2 : ℤ) ^ w ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) hw
  refine ⟨?_, hd.2, ?_, ?_⟩
  · rcases abs_cases d with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
  · have := neg_abs_le d; omega
  · have := le_abs_self d; omega

/-- One step of Horner's rule in base `2` over several points. -/
theorem horner2 (n e : ℕ) (d : ℕ → Array I8 256#usize) (P : ℕ → curve25519.edwards.Point)
    (he : e < 256) :
    2 • (∑ k ∈ Finset.range n, nafTail (d k) (e + 1) • P k) +
      ∑ k ∈ Finset.range n, (d k)[e]!.val • P k =
      ∑ k ∈ Finset.range n, nafTail (d k) e • P k := by
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nafTail_eq _ _ he, ← natCast_zsmul, smul_smul, ← add_smul, add_comm]
  push_cast
  ring_nf

end Curve25519Dalek
