/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519.Edwards.Torsion
public section

/-! # The RFC 8032 point encoding of edwards25519

The generic encoding of `EllipticCurve.TwistedEdwards.Encoding.*` at `edwards` with
`bits = 255`: `encode P = P.y.val + 2 ^ 255 * sign(P.x)` (RFC 8032 §5.1.2, the little-endian
value of the 32 bytes of `CompressedEdwardsY`), and the strict decoder `decode` (§5.1.3). The
lemmas are the generic ones instantiated (`encode_lt_two_pow_256`, `decode_encode`,
`encode_decode`, `decode_eq_some_iff`, `decode_eq_none_iff`, `encode_injective`), the sign of
the basepoint (`not_isNeg_basepoint_x`), and the encodings of the basepoint
(`encode_basepoint`, dalek's `ED25519_BASEPOINT_COMPRESSED`), of `0` and of the eight torsion
points as numerals.

`encode` and `decode` are abbreviations of the generic functions, so every generic lemma
applies to them directly. -/

namespace curve25519

open TwistedEdwardsModel

/-- `p < 2 ^ 255`: the `y`-coordinate fits in `255` bits. -/
instance instFactPLtTwoPow255 : Fact (p < 2 ^ 255) := ⟨p_lt_two_pow_255⟩

/-- RFC 8032 §5.1.2: the encoding of a point of edwards25519, `y.val + 2 ^ 255 * sign(x)`. -/
noncomputable abbrev encode : edwards.Point → ℕ :=
  TwistedEdwardsModel.encode edwards 255

/-- RFC 8032 §5.1.3, strict: the decoding of a `256`-bit value, `none` unless it is the encoding
of a point (`decode_eq_some_iff_encode_eq`). -/
noncomputable abbrev decode : ℕ → Option edwards.Point :=
  TwistedEdwardsModel.decode edwards 255

theorem encode_eq (P : edwards.Point) :
    encode P = P.y.val + 2 ^ 255 * (if P.x.isNeg then 1 else 0) :=
  rfl

/-! ### The generic lemmas at `edwards`, `bits = 255` -/

theorem encode_lt_two_pow_256 (P : edwards.Point) : encode P < 2 ^ 256 :=
  TwistedEdwardsModel.encode_lt edwards 255 P

/-- The low `255` bits of an encoding are `y.val`. -/
theorem encode_mod_two_pow_255 (P : edwards.Point) : encode P % 2 ^ 255 = P.y.val :=
  TwistedEdwardsModel.encode_mod_two_pow edwards 255 P

/-- Bit `255` of an encoding is the sign of `x`. -/
theorem encode_div_two_pow_255 (P : edwards.Point) :
    encode P / 2 ^ 255 = if P.x.isNeg then 1 else 0 :=
  TwistedEdwardsModel.encode_div_two_pow edwards 255 P

theorem encode_injective : Function.Injective encode :=
  TwistedEdwardsModel.encode_injective edwards 255

theorem decode_encode (P : edwards.Point) : decode (encode P) = some P :=
  TwistedEdwardsModel.decode_encode edwards 255 P

theorem encode_decode {n : ℕ} {P : edwards.Point} (h : decode n = some P) : encode P = n :=
  TwistedEdwardsModel.encode_decode edwards 255 h

/-- `decode n = some P` iff `n < 2 ^ 256`, the low `255` bits of `n` are below `p`, `P.y` is
that value, and the sign of `P.x` is bit `255` of `n`. -/
theorem decode_eq_some_iff {n : ℕ} {P : edwards.Point} :
    decode n = some P ↔
      n < 2 ^ 256 ∧ n % 2 ^ 255 < p ∧ P.y = ((n % 2 ^ 255 : ℕ) : ZMod p) ∧
        (P.x.isNeg ↔ n / 2 ^ 255 = 1) :=
  TwistedEdwardsModel.decode_eq_some_iff edwards 255

theorem decode_eq_some_iff_encode_eq {n : ℕ} {P : edwards.Point} :
    decode n = some P ↔ encode P = n :=
  TwistedEdwardsModel.decode_eq_some_iff_encode_eq edwards 255

/-- The rejection reasons of strict decoding: `n ≥ 2 ^ 256`, `y ≥ p`, no square root of
`(y² - 1) / (d y² + 1)`, or `y² = 1` with the sign bit set. -/
theorem decode_eq_none_iff {n : ℕ} :
    decode n = none ↔
      2 ^ 256 ≤ n ∨ p ≤ n % 2 ^ 255 ∨
        ¬ IsSquare (edwards.xSq ((n % 2 ^ 255 : ℕ) : ZMod p)) ∨
        (((n % 2 ^ 255 : ℕ) : ZMod p) ^ 2 = 1 ∧ n / 2 ^ 255 = 1) :=
  TwistedEdwardsModel.decode_eq_none_iff edwards 255

theorem decode_isSome_iff {n : ℕ} : (decode n).isSome ↔ ∃ P, encode P = n :=
  TwistedEdwardsModel.decode_isSome_iff edwards 255

/-- `x² = (y² - 1) / (d y² + 1)` on edwards25519 (`a = -1`). -/
theorem edwards_xSq (y : ZMod p) : edwards.xSq y = (y ^ 2 - 1) / (d * y ^ 2 + 1) := by
  unfold xSq
  rw [edwards_a_eq_neg_one, edwards_d, sub_neg_eq_add]

/-! ### The basepoint -/

/-- The basepoint has even `x`: RFC 8032's "positive" square root. -/
theorem not_isNeg_basepoint_x : ¬ basepoint.x.isNeg :=
  ZMod.not_isNeg_iff.mpr basepoint_x_val_even

/-- **The encoding of the basepoint**: dalek's `ED25519_BASEPOINT_COMPRESSED`, the bytes
`58 66 66 … 66`, i.e. `y = 4/5` with the sign bit `0`. -/
theorem encode_basepoint : encode basepoint =
    46316835694926478169428394003475163141307993866256225615783033603165251855960 := by
  rw [encode_eq, ite_eq_right not_isNeg_basepoint_x, mul_zero, add_zero, basepoint_y_eq,
    ZMod.val_ofNat_of_lt (by rw [p_eq_numeral]; decide)]

/-- The encoding of the basepoint is below `2 ^ 255`: the sign bit is clear. -/
theorem encode_basepoint_lt : encode basepoint < 2 ^ 255 := by
  rw [encode_basepoint]
  decide

/-! ### The zero and the torsion points -/

theorem encode_zero : encode 0 = 1 :=
  TwistedEdwardsModel.encode_zero edwards 255

theorem encode_eightTorsion_zero : encode (eightTorsion 0) = 1 := by
  rw [eightTorsion_zero, encode_zero]

/-- `torsion8 = (x, y)` with `x` even: the encoding is `y`. -/
theorem encode_torsion8 : encode torsion8 =
    55188659117513257062467267217118295137698188065244968500265048394206261417927 := by
  rw [encode_eq, torsion8_x_eq, torsion8_y_eq,
    ite_eq_right ((not_iff_not.mpr (ZMod.isNeg_ofNat_iff (by rw [p_eq_numeral]; decide))).mpr
      (by decide)),
    mul_zero, add_zero, ZMod.val_ofNat_of_lt (by rw [p_eq_numeral]; decide)]

theorem encode_eightTorsion_one : encode (eightTorsion 1) =
    55188659117513257062467267217118295137698188065244968500265048394206261417927 := by
  rw [eightTorsion_one, encode_torsion8]

/-- `eightTorsion 2 = (-√-1, 0)` with `-√-1` odd: the encoding is `2 ^ 255`. -/
theorem encode_eightTorsion_two : encode (eightTorsion 2) =
    57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
  rw [encode_eq, eightTorsion_two_x_eq, eightTorsion_two_y_eq,
    ite_eq_left ((ZMod.isNeg_ofNat_iff (by rw [p_eq_numeral]; decide)).mpr (by decide)),
    ZMod.val_zero, zero_add, mul_one]
  decide

theorem encode_eightTorsion_two_eq_two_pow : encode (eightTorsion 2) = 2 ^ 255 := by
  rw [encode_eightTorsion_two]
  decide

/-- `eightTorsion 3 = (x, -y)` with `x` even: the encoding is `-y`. -/
theorem encode_eightTorsion_three : encode (eightTorsion 3) =
    2707385501144840649318225287225658788936804267575313519463743609750303402022 := by
  rw [encode_eq, eightTorsion_three_x_eq, eightTorsion_three_y_eq,
    ite_eq_right ((not_iff_not.mpr (ZMod.isNeg_ofNat_iff (by rw [p_eq_numeral]; decide))).mpr
      (by decide)),
    mul_zero, add_zero, ZMod.val_ofNat_of_lt (by rw [p_eq_numeral]; decide)]

/-- `eightTorsion 4 = (0, -1)`: the encoding is `p - 1`. -/
theorem encode_eightTorsion_four : encode (eightTorsion 4) =
    57896044618658097711785492504343953926634992332820282019728792003956564819948 := by
  rw [encode_eq, eightTorsion_four_x_eq, eightTorsion_four_y_eq, ite_eq_right ZMod.isNeg_zero,
    mul_zero, add_zero, ZMod.val_ofNat_of_lt (by rw [p_eq_numeral]; decide)]

/-- The encoding of `(0, -1)` is `p - 1`. -/
theorem encode_eightTorsion_four_add_one : encode (eightTorsion 4) + 1 = p := by
  rw [encode_eightTorsion_four, p_eq_numeral]

/-- `eightTorsion 5 = (-x, -y)` with `-x` odd: the encoding is `-y + 2 ^ 255`. -/
theorem encode_eightTorsion_five : encode (eightTorsion 5) =
    60603430119802938361103717791569612715571796600395595539192535613706868221990 := by
  rw [encode_eq, eightTorsion_five_x_eq, eightTorsion_five_y_eq,
    ite_eq_left ((ZMod.isNeg_ofNat_iff (by rw [p_eq_numeral]; decide)).mpr (by decide)),
    mul_one, ZMod.val_ofNat_of_lt (by rw [p_eq_numeral]; decide)]
  decide

/-- `eightTorsion 6 = (√-1, 0)` with `√-1` even: the encoding is `0`. -/
theorem encode_eightTorsion_six : encode (eightTorsion 6) = 0 := by
  rw [encode_eq, eightTorsion_six_x_eq, eightTorsion_six_y_eq,
    ite_eq_right ((not_iff_not.mpr (ZMod.isNeg_ofNat_iff (by rw [p_eq_numeral]; decide))).mpr
      (by decide)),
    mul_zero, add_zero, ZMod.val_zero]

/-- `eightTorsion 7 = (-x, y)` with `-x` odd: the encoding is `y + 2 ^ 255`. -/
theorem encode_eightTorsion_seven : encode (eightTorsion 7) =
    113084703736171354774252759721462249064333180398065250519993840398162826237895 := by
  rw [encode_eq, eightTorsion_seven_x_eq, eightTorsion_seven_y_eq,
    ite_eq_left ((ZMod.isNeg_ofNat_iff (by rw [p_eq_numeral]; decide)).mpr (by decide)),
    mul_one, ZMod.val_ofNat_of_lt (by rw [p_eq_numeral]; decide)]
  decide

end curve25519
