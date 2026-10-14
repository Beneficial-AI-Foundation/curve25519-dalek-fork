/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar
@[expose] public section

/-! # Curve25519 parameters

The field prime, the prime-order subgroup's order, and the constants of the twisted Edwards form
`a x² + y² = 1 + d x² y²` (RFC 8032 §5.1) and the Montgomery form `y² = x³ + A x² + x`
(RFC 7748 §4.1). -/

namespace curve25519

/-- The field prime `p = 2^255 - 19`. -/
def p : ℕ := 2 ^ 255 - 19

/-- The order of the prime-order subgroup, `ℓ = 2^252 + 27742317777372353535851937790883648493`. -/
def L : ℕ := 2 ^ 252 + 27742317777372353535851937790883648493

/-- The Edwards coefficient `a = -1`. -/
def a : ZMod p := -1

/-- The Edwards coefficient `d = -121665 / 121666`. -/
def d : ZMod p := -121665 * (121666 : ZMod p)⁻¹

/-- The Montgomery coefficient `A = 486662`. -/
def A : ℕ := 486662

/-- The square root of `-1` used by RFC 8032 (§5.1.3), `2^((p-1)/4) mod p`, as a natural number
below `p`. -/
def sqrtM1 : ℕ := 19681161376707505956807079304988542015446066515923890162744021073123829784752

/-! ## Characterisation of `p` and `L` -/

theorem p_add_nineteen : p + 19 = 2 ^ 255 := by decide

theorem p_pos : 0 < p := by decide

theorem p_lt : p < 2 ^ 255 := by decide

theorem two_pow_255_mod_p : 2 ^ 255 % p = 19 := by decide

theorem two_pow_255_eq_nineteen : (2 : ZMod p) ^ 255 = 19 := by
  rw [← Nat.cast_ofNat, ← Nat.cast_pow, ← p_add_nineteen]
  simp

theorem lt_p_iff {x : ℕ} : x < p ↔ x + 19 < 2 ^ 255 := by
  rw [← p_add_nineteen, Nat.add_lt_add_iff_right]

/-- Folding `2^255 ≡ 19`: reduces `x % p` to a smaller argument. -/
theorem mod_p_fold (x : ℕ) : x % p = (x % 2 ^ 255 + 19 * (x / 2 ^ 255)) % p := by
  have h : x = x % 2 ^ 255 + 19 * (x / 2 ^ 255) + p * (x / 2 ^ 255) := by
    have := Nat.mod_add_div x (2 ^ 255)
    rw [← p_add_nineteen] at this ⊢
    rw [add_mul, Nat.add_comm (p * _), ← Nat.add_assoc] at this
    exact this.symm
  conv_lhs => rw [h]
  rw [Nat.add_mul_mod_self_left]

/-- `x % p` for `x < 2^255`, without `p`. -/
theorem mod_p_of_lt {x : ℕ} (hx : x < 2 ^ 255) :
    x % p = if x + 19 < 2 ^ 255 then x else x + 19 - 2 ^ 255 := by
  have h := p_add_nineteen
  split_ifs with hx'
  · exact Nat.mod_eq_of_lt (by grind)
  · rw [Nat.mod_eq_sub_mod (by grind), Nat.mod_eq_of_lt (by grind)]
    grind

/-- `d = -121665 / 121666` as a natural number below `p`. -/
theorem d_eq :
    d = ((37095705934669439343138083508754565189542113879843219016388785533085940283555 : ℕ) :
      ZMod p) := by
  have hinv : (121666 : ZMod p) * (121666 : ZMod p)⁻¹ = 1 := by
    exact_mod_cast ZMod.coe_mul_inv_eq_one 121666 (by decide)
  have hd : ((121666 *
      37095705934669439343138083508754565189542113879843219016388785533085940283555 +
      121665 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (by decide)
  rw [Nat.cast_add, Nat.cast_mul] at hd
  simp only [Nat.cast_ofNat] at hd ⊢
  rw [d, neg_eq_of_add_eq_zero_left hd, mul_comm (121666 : ZMod p), mul_assoc, hinv,
    mul_one]

theorem L_pos : 0 < L := by decide

theorem L_lt : L < 2 ^ 253 := by decide

theorem two_pow_252_lt_L : 2 ^ 252 < L := by decide

/-- `L` in radix `2^52`, the representation of dalek's `Scalar52`. -/
theorem L_eq_limbs :
    L = 671914833335277 + 2 ^ 52 * 3916664325105025 + 2 ^ 104 * 1367801 + 2 ^ 156 * 0
      + 2 ^ 208 * 17592186044416 := by
  decide

theorem L_mod_two_pow_52 : L % 2 ^ 52 = 671914833335277 := by decide

theorem L_mod_two : L % 2 = 1 := by decide

theorem L_lt_two_pow_260 : L < 2 ^ 260 := by
  rw [show 260 = 253 + 7 from rfl, pow_add]
  exact L_lt.trans_le (Nat.le_mul_of_pos_right _ (by decide))

/-- The Montgomery radix `2^260` modulo `L`. -/
theorem two_pow_260_mod_L :
    2 ^ 260 % L =
      7237005577332262213973186563042994233755083008372585100823854863819240236781 := by
  decide +kernel

theorem two_pow_520_mod_L :
    2 ^ 520 % L =
      4185850391763183796333492317919282507600454137915443218209456916606550724923 := by
  decide +kernel

/-! ## Characterisation of `sqrtM1` -/

theorem sqrtM1_lt : sqrtM1 < p := by decide

theorem sqrtM1_sq_add_one : (sqrtM1 ^ 2 + 1) % p = 0 := by decide

/-- `sqrtM1` in radix `2^51`, the representation of dalek's `FieldElement51`. -/
theorem sqrtM1_eq_limbs :
    sqrtM1 = 1718705420411056 + 2 ^ 51 * 234908883556509 + 2 ^ 102 * 2233514472574048
      + 2 ^ 153 * 2117202627021982 + 2 ^ 204 * 765476049583133 := by
  decide

/-- `sqrtM1` is the RFC 8032 value `2^((p-1)/4)`. -/
theorem sqrtM1_eq_pow : (2 : ZMod p) ^ ((p - 1) / 4) = sqrtM1 := by
  have hp : p = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
    decide
  rw [hp, sqrtM1]
  reduce_mod_char

attribute [irreducible] p L sqrtM1

end curve25519
