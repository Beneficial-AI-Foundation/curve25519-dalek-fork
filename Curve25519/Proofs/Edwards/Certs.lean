/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
import all Curve25519.Basic
public section

/-! # Certificates for the basepoint and the 8-torsion (not audited)

Kernel computations (`decide +kernel`) in extended coordinates: the curve equation at the
basepoint and at the torsion point, `L • basepoint = 0` (the 253-step double-and-add chain),
`8 • torsion8 = 0`, `4 • torsion8 ≠ 0`, and the coordinates of `i • torsion8`. The model is
first rewritten to its numeral form (`edwards_eq`), so that the kernel never meets the field
inversion in `d`; `Curve25519.Basic` is imported with `import all` so that the kernel can
unfold `p` and `L`. The results are stated for any point with the given numeral coordinates and
instantiated by `Curve25519.Edwards.Basepoint` and `Curve25519.Edwards.Torsion`. -/

namespace curve25519.Proofs

open TwistedEdwardsModel

/-- `edwards` with its coefficients as numerals, for the kernel. -/
private theorem edwards_eq :
    edwards = ⟨-1, ((37095705934669439343138083508754565189542113879843219016388785533085940283555 :
      ℕ) : ZMod p)⟩ := by
  rw [edwards_def, a_def, d_eq_natCast]

/-! ### From kernel computations to group facts -/

/-- `n • P = Q` from projective equality of `n • P` and `Q` in extended coordinates. -/
private theorem nsmul_eq_of_projEq {P Q : edwards.Point} {n : ℕ}
    (h : (Extended.nsmul n P.toExtended).ProjEq Q.toExtended) : n • P = Q :=
  calc n • P = n • P.toExtended.toPoint := by rw [Point.toPoint_toExtended]
    _ = (Extended.nsmul n P.toExtended).toPoint :=
      (Extended.toPoint_nsmul (Point.onCurve_toExtended P) n).symm
    _ = Q.toExtended.toPoint :=
      (Extended.projEq_iff_toPoint_eq (Extended.nsmul_onCurve (Point.onCurve_toExtended P) n)
        (Point.onCurve_toExtended Q)).mp h
    _ = Q := Point.toPoint_toExtended Q

/-- `n • P = 0` from the zero test on `n • P` in extended coordinates. -/
private theorem nsmul_eq_zero_of_isZero {P : edwards.Point} {n : ℕ}
    (h : (Extended.nsmul n P.toExtended).IsZero) : n • P = 0 :=
  calc n • P = n • P.toExtended.toPoint := by rw [Point.toPoint_toExtended]
    _ = (Extended.nsmul n P.toExtended).toPoint :=
      (Extended.toPoint_nsmul (Point.onCurve_toExtended P) n).symm
    _ = 0 := (Extended.isZero_iff (Extended.nsmul_onCurve (Point.onCurve_toExtended P) n)).mp h

/-- `n • P ≠ 0` from the zero test on `n • P` in extended coordinates. -/
private theorem nsmul_ne_zero_of_not_isZero {P : edwards.Point} {n : ℕ}
    (h : ¬ (Extended.nsmul n P.toExtended).IsZero) : n • P ≠ 0 := by
  intro h0
  apply h
  rw [Extended.isZero_iff (Extended.nsmul_onCurve (Point.onCurve_toExtended P) n),
    Extended.toPoint_nsmul (Point.onCurve_toExtended P), Point.toPoint_toExtended]
  exact h0

/-- `n • P = 0` for a point with given coordinates, from the zero test on the numeral
extended point. -/
private theorem nsmul_eq_zero_of_coords {x y : ZMod p} {n : ℕ} (P : edwards.Point)
    (hx : P.x = x) (hy : P.y = y)
    (hc : (Extended.nsmul n (⟨x, y, 1, x * y⟩ : edwards.Extended)).IsZero) : n • P = 0 := by
  obtain ⟨x₀, y₀, h⟩ := P
  change x₀ = x at hx
  change y₀ = y at hy
  subst hx hy
  exact nsmul_eq_zero_of_isZero hc

/-- `n • P ≠ 0` for a point with given coordinates, from the zero test on the numeral
extended point. -/
private theorem nsmul_ne_zero_of_coords {x y : ZMod p} {n : ℕ} (P : edwards.Point)
    (hx : P.x = x) (hy : P.y = y)
    (hc : ¬ (Extended.nsmul n (⟨x, y, 1, x * y⟩ : edwards.Extended)).IsZero) : n • P ≠ 0 := by
  obtain ⟨x₀, y₀, h⟩ := P
  change x₀ = x at hx
  change y₀ = y at hy
  subst hx hy
  exact nsmul_ne_zero_of_not_isZero hc

/-- The coordinates of `n • P` for a point with given coordinates, from projective equality of
the numeral extended points. -/
private theorem nsmul_x_y_of_coords {x y x' y' : ZMod p} {n : ℕ} (P : edwards.Point)
    (hx : P.x = x) (hy : P.y = y) (h' : edwards.Equation x' y')
    (hc : (Extended.nsmul n (⟨x, y, 1, x * y⟩ : edwards.Extended)).ProjEq ⟨x', y', 1, x' * y'⟩) :
    (n • P).x = x' ∧ (n • P).y = y' := by
  obtain ⟨x₀, y₀, h⟩ := P
  change x₀ = x at hx
  change y₀ = y at hy
  subst hx hy
  rw [nsmul_eq_of_projEq (P := ⟨x₀, y₀, h⟩) (Q := ⟨x', y', h'⟩) hc]
  exact ⟨rfl, rfl⟩

/-! ### The basepoint -/

/-- The basepoint `(x, 4/5)` of RFC 8032 is on the model. -/
theorem basepoint_equation : edwards.Equation
    15112221349535400772501151409588531511454012693041857206046113283949847762202
    46316835694926478169428394003475163141307993866256225615783033603165251855960 := by
  rw [edwards_eq]
  decide +kernel

theorem basepoint_x_ne_zero :
    (15112221349535400772501151409588531511454012693041857206046113283949847762202 : ZMod p)
      ≠ 0 := by
  decide +kernel

theorem basepoint_x_val_mod_two :
    (15112221349535400772501151409588531511454012693041857206046113283949847762202 :
      ZMod p).val % 2 = 0 := by
  decide +kernel

theorem five_ne_zero : (5 : ZMod p) ≠ 0 := by
  decide +kernel

theorem basepoint_y_mul_five :
    (46316835694926478169428394003475163141307993866256225615783033603165251855960 : ZMod p)
      * 5 = 4 := by
  decide +kernel

/-- `L • basepoint = 0`: the 253-step double-and-add chain in extended coordinates. -/
theorem L_nsmul_eq_zero (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    L • P = 0 :=
  nsmul_eq_zero_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)

/-! ### The torsion point -/

/-- Dalek's `EIGHT_TORSION[1]` is on the model. -/
theorem torsion8_equation : edwards.Equation
    14399317868200118260347934320527232580618823971194345261214217575416788799818
    55188659117513257062467267217118295137698188065244968500265048394206261417927 := by
  rw [edwards_eq]
  decide +kernel

theorem torsion8_x_ne_zero :
    (14399317868200118260347934320527232580618823971194345261214217575416788799818 : ZMod p)
      ≠ 0 := by
  decide +kernel

theorem eight_nsmul_eq_zero (P : edwards.Point)
    (hx : P.x = 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (hy : P.y = 55188659117513257062467267217118295137698188065244968500265048394206261417927) :
    8 • P = 0 :=
  nsmul_eq_zero_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)

theorem four_nsmul_ne_zero (P : edwards.Point)
    (hx : P.x = 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (hy : P.y = 55188659117513257062467267217118295137698188065244968500265048394206261417927) :
    4 • P ≠ 0 :=
  nsmul_ne_zero_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)

/-! The multiples `2 • T`, …, `7 • T` of the torsion point `T`, with their coordinates as
numerals: `2 • T = (-sqrtM1, 0)`, `3 • T = (x, -y)`, `4 • T = (0, -1)`, `5 • T = (-x, -y)`,
`6 • T = (sqrtM1, 0)`, `7 • T = (-x, y)`. -/

theorem two_nsmul_x_y (P : edwards.Point)
    (hx : P.x = 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (hy : P.y = 55188659117513257062467267217118295137698188065244968500265048394206261417927) :
    (2 • P).x = 38214883241950591754978413199355411911188925816896391856984770930832735035197 ∧
      (2 • P).y = 0 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

theorem three_nsmul_x_y (P : edwards.Point)
    (hx : P.x = 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (hy : P.y = 55188659117513257062467267217118295137698188065244968500265048394206261417927) :
    (3 • P).x = 14399317868200118260347934320527232580618823971194345261214217575416788799818 ∧
      (3 • P).y = 2707385501144840649318225287225658788936804267575313519463743609750303402022 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

theorem four_nsmul_x_y (P : edwards.Point)
    (hx : P.x = 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (hy : P.y = 55188659117513257062467267217118295137698188065244968500265048394206261417927) :
    (4 • P).x = 0 ∧
      (4 • P).y = 57896044618658097711785492504343953926634992332820282019728792003956564819948 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

theorem five_nsmul_x_y (P : edwards.Point)
    (hx : P.x = 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (hy : P.y = 55188659117513257062467267217118295137698188065244968500265048394206261417927) :
    (5 • P).x = 43496726750457979451437558183816721346016168361625936758514574428539776020131 ∧
      (5 • P).y = 2707385501144840649318225287225658788936804267575313519463743609750303402022 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

theorem six_nsmul_x_y (P : edwards.Point)
    (hx : P.x = 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (hy : P.y = 55188659117513257062467267217118295137698188065244968500265048394206261417927) :
    (6 • P).x = 19681161376707505956807079304988542015446066515923890162744021073123829784752 ∧
      (6 • P).y = 0 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

theorem seven_nsmul_x_y (P : edwards.Point)
    (hx : P.x = 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (hy : P.y = 55188659117513257062467267217118295137698188065244968500265048394206261417927) :
    (7 • P).x = 43496726750457979451437558183816721346016168361625936758514574428539776020131 ∧
      (7 • P).y = 55188659117513257062467267217118295137698188065244968500265048394206261417927 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

/-- `p - 1` as a numeral is `-1`. -/
theorem neg_one_eq_numeral :
    (-1 : ZMod p) =
      57896044618658097711785492504343953926634992332820282019728792003956564819948 := by
  decide +kernel

/-- `sqrtM1` as a numeral is `-1`'s square root. -/
theorem sqrtM1_eq_numeral :
    (sqrtM1 : ZMod p) =
      19681161376707505956807079304988542015446066515923890162744021073123829784752 := by
  rw [sqrtM1_def]
  rfl

end curve25519.Proofs
