/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ReduceModChar
public section

/-! # Curve25519 parameters

The field prime, the prime-order subgroup's order, and the constants of the twisted Edwards form
`a x² + y² = 1 + d x² y²` (RFC 8032 §5.1) and the Montgomery form `y² = x³ + A x² + x`
(RFC 7748 §4.1).

The definitions are not exposed: importing modules cannot unfold them (neither the elaborator nor
the kernel), and use the characterisation lemmas below instead. -/

namespace curve25519

/-- The field prime `p = 2^255 - 19`. -/
def p : ℕ := 2 ^ 255 - 19

/-- The order of the prime-order subgroup, `L = 2^252 + 27742317777372353535851937790883648493`. -/
def L : ℕ := 2 ^ 252 + 27742317777372353535851937790883648493

/-- The Edwards coefficient `a = -1`. -/
noncomputable def a : ZMod p := -1

/-- The Edwards coefficient `d = -121665 / 121666`. -/
noncomputable def d : ZMod p := -121665 * (121666 : ZMod p)⁻¹

/-- The Montgomery coefficient `A = 486662`. -/
def A : ℕ := 486662

/-- The order of the prime-order subgroup of the quadratic twist of curve25519,
`L' = 2^253 - 55484635554744707071703875581767296995` (a prime, not proved here): the twist has
`4 L'` points (`card_twist` in `Curve25519.Montgomery`), since `2 p + 2 = 8 L + 4 L'`
(`two_mul_p_add_two`). -/
def twistL : ℕ := 2 ^ 253 - 55484635554744707071703875581767296995

/-- The square root of `-1` used by RFC 8032 (§5.1.3), `2^((p-1)/4) mod p`, as a natural number
below `p`. -/
def sqrtM1 : ℕ := 19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- A square root of `-(A + 2) = -486664` modulo `p`, as a natural number below `p`: the scaling
`v ↦ sqrtNegAAddTwo · v` identifies the Montgomery model `(A, 1)` with the Montgomery model
`(A, 4 / (a - d))` of the Edwards model (`sqrtNegAAddTwo_sq`, `four_eq_sqrtNegAAddTwo_sq_mul`).
Of the two roots, the even one. -/
def sqrtNegAAddTwo : ℕ :=
  6853475219497561581579357271197624642482790079785650197046958215289687604742

/-- RFC 9496 §4.1 `SQRT_AD_MINUS_ONE`: a square root of `a d - 1 = -d - 1` modulo `p`, as a
natural number below `p` (`sqrtAdMinusOne_sq`). The RFC's value is odd, i.e. negative in the
sense of `ZMod.isNeg` (`sqrtAdMinusOne_mod_two`). -/
def sqrtAdMinusOne : ℕ :=
  25063068953384623474111414158702152701244531502492656460079210482610430750235

/-- RFC 9496 §4.1 `INVSQRT_A_MINUS_D`: the inverse of a square root of `a - d = -1 - d` modulo
`p`, as a natural number below `p` (`invsqrtAMinusD_sq_mul`); even (`invsqrtAMinusD_mod_two`). -/
def invsqrtAMinusD : ℕ :=
  54469307008909316920995813868745141605393597292927456921205312896311721017578

/-- RFC 9496 §4.1 `ONE_MINUS_D_SQ = 1 - d²` modulo `p`, as a natural number below `p`
(`oneMinusDSq_eq`). -/
def oneMinusDSq : ℕ :=
  1159843021668779879193775521855586647937357759715417654439879720876111806838

/-- RFC 9496 §4.1 `D_MINUS_ONE_SQ = (d - 1)²` modulo `p`, as a natural number below `p`
(`dMinusOneSq_eq`). -/
def dMinusOneSq : ℕ :=
  40440834346308536858101042469323190826248399146238708352240133220865137265952

/-! ## Characterisation of `p` and `L` -/

/-! The defining equations (`<name>_def`), then the other characterisations. -/

theorem p_def : p = 2 ^ 255 - 19 := by
  unfold p
  rfl

theorem L_def : L = 2 ^ 252 + 27742317777372353535851937790883648493 := by
  unfold L
  rfl

theorem d_def : d = -121665 * (121666 : ZMod p)⁻¹ := by
  unfold d
  rfl

theorem sqrtM1_def :
    sqrtM1 = 19681161376707505956807079304988542015446066515923890162744021073123829784752 := by
  unfold sqrtM1
  rfl

/-- `p` as a numeral. -/
theorem p_eq_numeral :
    p = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  decide

theorem p_add_nineteen : p + 19 = 2 ^ 255 := by rw [p_eq_numeral]; decide

theorem p_pos : 0 < p := by rw [p_eq_numeral]; decide

theorem two_lt_p : 2 < p := by rw [p_eq_numeral]; decide

theorem p_mod_two : p % 2 = 1 := by rw [p_eq_numeral]

/-- `p ≡ 5 (mod 8)`: `2` is not a square modulo `p` (`not_isSquare_two` in
`Curve25519.X25519`). -/
theorem p_mod_eight : p % 8 = 5 := by rw [p_eq_numeral]

theorem p_lt_two_pow_255 : p < 2 ^ 255 := by rw [p_eq_numeral]; decide

theorem nine_lt_p : 9 < p := by rw [p_eq_numeral]; decide

theorem two_pow_255_mod_p : 2 ^ 255 % p = 19 := by rw [p_eq_numeral]; decide

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

/-- `A = 486662`. -/
theorem A_def : A = 486662 := by rfl

/-- `a = -1`. -/
theorem a_def : a = -1 := by rfl

/-- `d = -121665 / 121666` as a natural number below `p`. -/
theorem d_eq_natCast :
    d = ((37095705934669439343138083508754565189542113879843219016388785533085940283555 : ℕ) :
      ZMod p) := by
  have hinv : (121666 : ZMod p) * (121666 : ZMod p)⁻¹ = 1 := by
    exact_mod_cast ZMod.coe_mul_inv_eq_one 121666 (by rw [p_eq_numeral]; decide)
  have hd : ((121666 *
      37095705934669439343138083508754565189542113879843219016388785533085940283555 +
      121665 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (by rw [p_eq_numeral]; decide)
  rw [Nat.cast_add, Nat.cast_mul] at hd
  simp only [Nat.cast_ofNat] at hd ⊢
  rw [d, neg_eq_of_add_eq_zero_left hd, mul_comm (121666 : ZMod p), mul_assoc, hinv,
    mul_one]

theorem d_ne_zero : d ≠ 0 := by
  rw [d_eq_natCast, Ne, ZMod.natCast_eq_zero_iff, p_eq_numeral]
  decide

/-- `a - d ≠ 0`: the Edwards model is not degenerate. -/
theorem a_sub_d_ne_zero : a - d ≠ 0 := by
  rw [a_def, d_eq_natCast, p_eq_numeral]
  reduce_mod_char
  decide

/-- Euler's criterion for `d`: `d^((p-1)/2) = -1`, so `d` is not a square (`not_isSquare_d` in
`Curve25519.Edwards.Basic`). -/
theorem d_pow_p_div_two : d ^ (p / 2) = -1 := by
  rw [d_eq_natCast, p_eq_numeral]
  norm_num
  reduce_mod_char

/-- `A = 2 (a + d) / (a - d)`: the Montgomery coefficient of the Edwards model is `A`. -/
theorem two_mul_a_add_d : 2 * (a + d) = A * (a - d) := by
  rw [a_def, d_eq_natCast, A_def, p_eq_numeral]
  push_cast
  reduce_mod_char

/-- `A² ≠ 4`: the Montgomery model is nonsingular. -/
theorem A_sq_ne_four : (A : ZMod p) ^ 2 ≠ 4 := by
  intro h
  rw [A_def] at h
  have h' : ((486662 ^ 2 : ℕ) : ZMod p) = ((4 : ℕ) : ZMod p) := by exact_mod_cast h
  rw [ZMod.natCast_eq_natCast_iff', p_eq_numeral] at h'
  exact absurd h' (by decide)

/-- `2 ≠ 0` in `ZMod p`. -/
instance instNeZeroTwo : NeZero (2 : ZMod p) := by
  refine ⟨fun h => ?_⟩
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact absurd (Nat.le_of_dvd two_pos h') (not_le.mpr two_lt_p)

/-- `5 ≠ 0` in `ZMod p`. -/
theorem five_ne_zero : (5 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact absurd (Nat.le_of_dvd (by norm_num) h') (not_le.mpr (by rw [p_eq_numeral]; decide))

/-- `L` as a numeral. -/
theorem L_eq_numeral :
    L = 7237005577332262213973186563042994240857116359379907606001950938285454250989 := by
  decide

theorem L_pos : 0 < L := by rw [L_eq_numeral]; decide

theorem L_lt_two_pow_253 : L < 2 ^ 253 := by rw [L_eq_numeral]; decide

theorem two_pow_252_lt_L : 2 ^ 252 < L := by rw [L_eq_numeral]; decide

/-- `L` in radix `2^52`, the representation of dalek's `Scalar52`. -/
theorem L_eq_limbs :
    L = 671914833335277 + 2 ^ 52 * 3916664325105025 + 2 ^ 104 * 1367801 + 2 ^ 156 * 0
      + 2 ^ 208 * 17592186044416 := by
  rw [L_eq_numeral]
  decide

theorem L_mod_two_pow_52 : L % 2 ^ 52 = 671914833335277 := by rw [L_eq_numeral]; decide

theorem L_mod_two : L % 2 = 1 := by rw [L_eq_numeral]

theorem L_lt_two_pow_260 : L < 2 ^ 260 := by
  rw [show 260 = 253 + 7 from rfl, pow_add]
  exact L_lt_two_pow_253.trans_le (Nat.le_mul_of_pos_right _ (by decide))

/-- The Montgomery radix `2^260` modulo `L`. -/
theorem two_pow_260_mod_L :
    2 ^ 260 % L =
      7237005577332262213973186563042994233755083008372585100823854863819240236781 := by
  rw [L_eq_numeral]
  decide +kernel

theorem two_pow_520_mod_L :
    2 ^ 520 % L =
      4185850391763183796333492317919282507600454137915443218209456916606550724923 := by
  rw [L_eq_numeral]
  decide +kernel

/-! ## Characterisation of `twistL` -/

theorem twistL_def : twistL = 2 ^ 253 - 55484635554744707071703875581767296995 := by
  unfold twistL
  rfl

/-- `L'` as a numeral. -/
theorem twistL_eq_numeral :
    twistL = 14474011154664524427946373126085988481603263447650325797860494125407373907997 := by
  decide

theorem twistL_pos : 0 < twistL := by rw [twistL_eq_numeral]; decide

/-- `2 p + 2 = 8 L + 4 L'`: the curve and its twist have `2 p + 2` points in total. -/
theorem two_mul_p_add_two : 2 * p + 2 = 8 * L + 4 * twistL := by
  rw [p_eq_numeral, L_eq_numeral, twistL_eq_numeral]

/-! ## Characterisation of `sqrtM1` -/

theorem sqrtM1_lt_p : sqrtM1 < p := by rw [p_eq_numeral]; decide

theorem sqrtM1_sq_add_one_mod_p : (sqrtM1 ^ 2 + 1) % p = 0 := by rw [p_eq_numeral]; decide

/-- `sqrtM1` is a square root of `-1` in `ZMod p`. -/
theorem sqrtM1_sq : (sqrtM1 : ZMod p) ^ 2 = -1 := by
  have h : ((sqrtM1 ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero sqrtM1_sq_add_one_mod_p)
  push_cast at h
  linear_combination h

theorem sqrtM1_ne_zero : (sqrtM1 : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, sqrtM1_def, p_eq_numeral]
  decide

/-- `-sqrtM1` as a numeral below `p` (`p - sqrtM1`): the `x`-coordinate of dalek's
`EIGHT_TORSION[2]`. -/
theorem neg_sqrtM1_eq :
    -(sqrtM1 : ZMod p) =
      38214883241950591754978413199355411911188925816896391856984770930832735035197 := by
  rw [sqrtM1_def, p_eq_numeral]
  push_cast
  reduce_mod_char

/-- `sqrtM1` in radix `2^51`, the representation of dalek's `FieldElement51`. -/
theorem sqrtM1_eq_limbs :
    sqrtM1 = 1718705420411056 + 2 ^ 51 * 234908883556509 + 2 ^ 102 * 2233514472574048
      + 2 ^ 153 * 2117202627021982 + 2 ^ 204 * 765476049583133 := by
  decide

/-- `sqrtM1` is the RFC 8032 value `2^((p-1)/4)`: of the two square roots of `-1` modulo `p`, the
one RFC 8032 specifies (a check of the constant; proofs use `sqrtM1_sq_add_one_mod_p`). -/
theorem sqrtM1_eq_two_pow : (sqrtM1 : ZMod p) = 2 ^ ((p - 1) / 4) := by
  rw [p_eq_numeral, sqrtM1]
  reduce_mod_char


theorem sqrtM1_mod_two : sqrtM1 % 2 = 0 := by
  rw [sqrtM1_def]

/-- Euler's criterion for `sqrtM1`: `sqrtM1^((p-1)/2) = (-1)^((p-1)/4) = -1` since `p ≡ 5 (mod 8)`,
so `sqrtM1` is not a square (`not_isSquare_sqrtM1` in `Curve25519.Ristretto.Encoding.Defs`). -/
theorem sqrtM1_pow_p_div_two : (sqrtM1 : ZMod p) ^ (p / 2) = -1 := by
  rw [sqrtM1_def, p_eq_numeral]
  norm_num
  reduce_mod_char

/-! ## Characterisation of the ristretto255 constants (RFC 9496 §4.1) -/

theorem sqrtAdMinusOne_def :
    sqrtAdMinusOne =
      25063068953384623474111414158702152701244531502492656460079210482610430750235 := by
  unfold sqrtAdMinusOne
  rfl

theorem sqrtAdMinusOne_lt_p : sqrtAdMinusOne < p := by
  rw [sqrtAdMinusOne_def, p_eq_numeral]
  decide

/-- The RFC's `SQRT_AD_MINUS_ONE` is odd (negative). -/
theorem sqrtAdMinusOne_mod_two : sqrtAdMinusOne % 2 = 1 := by
  rw [sqrtAdMinusOne_def]

/-- `sqrtAdMinusOne² = a d - 1` in `ZMod p`. -/
theorem sqrtAdMinusOne_sq : (sqrtAdMinusOne : ZMod p) ^ 2 = a * d - 1 := by
  rw [sqrtAdMinusOne_def, a_def, d_eq_natCast, p_eq_numeral]
  push_cast
  reduce_mod_char

theorem sqrtAdMinusOne_ne_zero : (sqrtAdMinusOne : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, sqrtAdMinusOne_def, p_eq_numeral]
  decide

theorem invsqrtAMinusD_def :
    invsqrtAMinusD =
      54469307008909316920995813868745141605393597292927456921205312896311721017578 := by
  unfold invsqrtAMinusD
  rfl

theorem invsqrtAMinusD_lt_p : invsqrtAMinusD < p := by
  rw [invsqrtAMinusD_def, p_eq_numeral]
  decide

/-- The RFC's `INVSQRT_A_MINUS_D` is even (non-negative). -/
theorem invsqrtAMinusD_mod_two : invsqrtAMinusD % 2 = 0 := by
  rw [invsqrtAMinusD_def]

/-- `invsqrtAMinusD² (a - d) = 1` in `ZMod p`. -/
theorem invsqrtAMinusD_sq_mul : (invsqrtAMinusD : ZMod p) ^ 2 * (a - d) = 1 := by
  rw [invsqrtAMinusD_def, a_def, d_eq_natCast, p_eq_numeral]
  push_cast
  reduce_mod_char

theorem invsqrtAMinusD_ne_zero : (invsqrtAMinusD : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, invsqrtAMinusD_def, p_eq_numeral]
  decide

theorem oneMinusDSq_def :
    oneMinusDSq =
      1159843021668779879193775521855586647937357759715417654439879720876111806838 := by
  unfold oneMinusDSq
  rfl

theorem oneMinusDSq_lt_p : oneMinusDSq < p := by
  rw [oneMinusDSq_def, p_eq_numeral]
  decide

/-- `oneMinusDSq = 1 - d²` in `ZMod p`. -/
theorem oneMinusDSq_eq : (oneMinusDSq : ZMod p) = 1 - d ^ 2 := by
  rw [oneMinusDSq_def, d_eq_natCast, p_eq_numeral]
  push_cast
  reduce_mod_char

theorem dMinusOneSq_def :
    dMinusOneSq =
      40440834346308536858101042469323190826248399146238708352240133220865137265952 := by
  unfold dMinusOneSq
  rfl

theorem dMinusOneSq_lt_p : dMinusOneSq < p := by
  rw [dMinusOneSq_def, p_eq_numeral]
  decide

/-- `dMinusOneSq = (d - 1)²` in `ZMod p`. -/
theorem dMinusOneSq_eq : (dMinusOneSq : ZMod p) = (d - 1) ^ 2 := by
  rw [dMinusOneSq_def, d_eq_natCast, p_eq_numeral]
  push_cast
  reduce_mod_char

/-! ## The 2-descent certificate of the 8-torsion

Euler's criterion for `1 - y²` at dalek's `EIGHT_TORSION[1]`, `y = 55188…417927`:
`(1 - y²)^((p-1)/2) = -1`, so `1 - y²` is not a square (`not_isSquare_one_sub_torsion8_y_sq` in
`Curve25519.Ristretto.Basic`): the point of order `8` is not even. -/

theorem one_sub_torsion8_y_sq_pow_p_div_two :
    (1 - ((55188659117513257062467267217118295137698188065244968500265048394206261417927 : ℕ) :
      ZMod p) ^ 2) ^ (p / 2) = -1 := by
  rw [p_eq_numeral]
  norm_num
  reduce_mod_char

/-! ## Characterisation of `sqrtNegAAddTwo` -/

theorem sqrtNegAAddTwo_def :
    sqrtNegAAddTwo =
      6853475219497561581579357271197624642482790079785650197046958215289687604742 := by
  unfold sqrtNegAAddTwo
  rfl

theorem sqrtNegAAddTwo_lt_p : sqrtNegAAddTwo < p := by
  rw [sqrtNegAAddTwo_def, p_eq_numeral]
  decide

theorem sqrtNegAAddTwo_mod_two : sqrtNegAAddTwo % 2 = 0 := by
  rw [sqrtNegAAddTwo_def]

/-- `sqrtNegAAddTwo² = -(A + 2)` in `ZMod p`. -/
theorem sqrtNegAAddTwo_sq : (sqrtNegAAddTwo : ZMod p) ^ 2 = -(A + 2) := by
  rw [sqrtNegAAddTwo_def, A_def, p_eq_numeral]
  push_cast
  reduce_mod_char

theorem sqrtNegAAddTwo_ne_zero : (sqrtNegAAddTwo : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, sqrtNegAAddTwo_def, p_eq_numeral]
  decide

/-- `4 / (a - d) = sqrtNegAAddTwo²`: the Montgomery model of the Edwards model is the rescaling
of `(A, 1)` by `sqrtNegAAddTwo`. -/
theorem four_eq_sqrtNegAAddTwo_sq_mul : 4 = (sqrtNegAAddTwo : ZMod p) ^ 2 * (a - d) := by
  rw [sqrtNegAAddTwo_def, a_def, d_eq_natCast, p_eq_numeral]
  push_cast
  reduce_mod_char

end curve25519
