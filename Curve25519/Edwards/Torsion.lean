/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
import Curve25519.Proofs.Edwards.Certs
import Mathlib.Tactic.NormNum
public section

/-! # The 8-torsion

The point `torsion8` of order `8` (dalek's `EIGHT_TORSION[1]`) and the eight torsion points
`eightTorsion i = i • torsion8`, in the order of dalek's `EIGHT_TORSION` array: `2 • T` and
`6 • T` are `(∓sqrtM1, 0)`, `4 • T = (0, -1)`, `3 • T`, `5 • T`, `7 • T` are `(x, -y)`,
`(-x, -y)`, `(-x, y)` for `T = (x, y)`. The definitions are hidden; the coordinates are
`torsion8_x_eq`, `torsion8_y_eq` and `eightTorsion_two_x_eq`, …. The certificates are in
`Curve25519.Proofs.Edwards.Certs` (not audited). -/

namespace curve25519

/-- Dalek's `EIGHT_TORSION[1]` is on the model. -/
theorem torsion8_equation : edwards.Equation
    14399317868200118260347934320527232580618823971194345261214217575416788799818
    55188659117513257062467267217118295137698188065244968500265048394206261417927 :=
  Proofs.torsion8_equation

/-- A point of order `8`: dalek's `EIGHT_TORSION[1]`. -/
noncomputable def torsion8 : edwards.Point :=
  ⟨14399317868200118260347934320527232580618823971194345261214217575416788799818,
    55188659117513257062467267217118295137698188065244968500265048394206261417927,
    torsion8_equation⟩

theorem torsion8_def : torsion8 =
    ⟨14399317868200118260347934320527232580618823971194345261214217575416788799818,
      55188659117513257062467267217118295137698188065244968500265048394206261417927,
      torsion8_equation⟩ := by
  unfold torsion8
  rfl

theorem torsion8_x_eq : torsion8.x =
    14399317868200118260347934320527232580618823971194345261214217575416788799818 := by
  rw [torsion8_def]

theorem torsion8_y_eq : torsion8.y =
    55188659117513257062467267217118295137698188065244968500265048394206261417927 := by
  rw [torsion8_def]

theorem torsion8_ne_zero : torsion8 ≠ 0 := by
  intro h
  have hx := congrArg TwistedEdwardsModel.Point.x h
  rw [torsion8_x_eq, TwistedEdwardsModel.zero_x] at hx
  exact Proofs.torsion8_x_ne_zero hx

theorem eight_nsmul_torsion8 : 8 • torsion8 = 0 :=
  Proofs.eight_nsmul_eq_zero torsion8 torsion8_x_eq torsion8_y_eq

theorem four_nsmul_torsion8_ne_zero : 4 • torsion8 ≠ 0 :=
  Proofs.four_nsmul_ne_zero torsion8 torsion8_x_eq torsion8_y_eq

/-- `torsion8` has order `8`. -/
theorem addOrderOf_torsion8 : addOrderOf torsion8 = 8 := by
  have h := addOrderOf_eq_prime_pow (p := 2) (n := 2) (x := torsion8)
    (by norm_num; exact four_nsmul_torsion8_ne_zero) (by norm_num; exact eight_nsmul_torsion8)
  norm_num at h
  exact h

/-! ### The eight torsion points -/

/-- The eight torsion points, `eightTorsion i = i • torsion8`: dalek's `EIGHT_TORSION` array. -/
noncomputable def eightTorsion (i : Fin 8) : edwards.Point :=
  (i : ℕ) • torsion8

theorem eightTorsion_def : eightTorsion = fun i : Fin 8 => (i : ℕ) • torsion8 := by
  unfold eightTorsion
  rfl

theorem eightTorsion_apply (i : Fin 8) : eightTorsion i = (i : ℕ) • torsion8 := by
  rw [eightTorsion_def]

theorem eightTorsion_zero : eightTorsion 0 = 0 := by
  rw [eightTorsion_apply]
  exact zero_nsmul _

theorem eightTorsion_one : eightTorsion 1 = torsion8 := by
  rw [eightTorsion_apply]
  exact one_nsmul _

/-- `8 • eightTorsion i = 0`. -/
theorem eight_nsmul_eightTorsion (i : Fin 8) : 8 • eightTorsion i = 0 := by
  rw [eightTorsion_apply, smul_comm, eight_nsmul_torsion8, smul_zero]

/-- The eight torsion points are distinct. -/
theorem eightTorsion_injective : Function.Injective eightTorsion := by
  intro i j h
  rw [eightTorsion_apply, eightTorsion_apply, nsmul_eq_nsmul_iff_modEq, addOrderOf_torsion8] at h
  exact Fin.ext (h.eq_of_lt_of_lt i.isLt j.isLt)

/-! The coordinates of `eightTorsion i` for `i = 2, …, 7`. -/

theorem eightTorsion_two_x_eq : (eightTorsion 2).x =
    38214883241950591754978413199355411911188925816896391856984770930832735035197 := by
  rw [eightTorsion_apply]
  exact (Proofs.two_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).1

theorem eightTorsion_two_y_eq : (eightTorsion 2).y = 0 := by
  rw [eightTorsion_apply]
  exact (Proofs.two_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).2

theorem eightTorsion_three_x_eq : (eightTorsion 3).x =
    14399317868200118260347934320527232580618823971194345261214217575416788799818 := by
  rw [eightTorsion_apply]
  exact (Proofs.three_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).1

theorem eightTorsion_three_y_eq : (eightTorsion 3).y =
    2707385501144840649318225287225658788936804267575313519463743609750303402022 := by
  rw [eightTorsion_apply]
  exact (Proofs.three_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).2

theorem eightTorsion_four_x_eq : (eightTorsion 4).x = 0 := by
  rw [eightTorsion_apply]
  exact (Proofs.four_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).1

theorem eightTorsion_four_y_eq : (eightTorsion 4).y =
    57896044618658097711785492504343953926634992332820282019728792003956564819948 := by
  rw [eightTorsion_apply]
  exact (Proofs.four_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).2

/-- `eightTorsion 4 = (0, -1)`, the point of order `2`. -/
theorem eightTorsion_four_y : (eightTorsion 4).y = -1 := by
  rw [eightTorsion_four_y_eq, Proofs.neg_one_eq_numeral]

theorem eightTorsion_five_x_eq : (eightTorsion 5).x =
    43496726750457979451437558183816721346016168361625936758514574428539776020131 := by
  rw [eightTorsion_apply]
  exact (Proofs.five_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).1

theorem eightTorsion_five_y_eq : (eightTorsion 5).y =
    2707385501144840649318225287225658788936804267575313519463743609750303402022 := by
  rw [eightTorsion_apply]
  exact (Proofs.five_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).2

theorem eightTorsion_six_x_eq : (eightTorsion 6).x =
    19681161376707505956807079304988542015446066515923890162744021073123829784752 := by
  rw [eightTorsion_apply]
  exact (Proofs.six_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).1

/-- `eightTorsion 6 = (sqrtM1, 0)`. -/
theorem eightTorsion_six_x : (eightTorsion 6).x = sqrtM1 := by
  rw [eightTorsion_six_x_eq, Proofs.sqrtM1_eq_numeral]

theorem eightTorsion_six_y_eq : (eightTorsion 6).y = 0 := by
  rw [eightTorsion_apply]
  exact (Proofs.six_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).2

theorem eightTorsion_seven_x_eq : (eightTorsion 7).x =
    43496726750457979451437558183816721346016168361625936758514574428539776020131 := by
  rw [eightTorsion_apply]
  exact (Proofs.seven_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).1

theorem eightTorsion_seven_y_eq : (eightTorsion 7).y =
    55188659117513257062467267217118295137698188065244968500265048394206261417927 := by
  rw [eightTorsion_apply]
  exact (Proofs.seven_nsmul_x_y torsion8 torsion8_x_eq torsion8_y_eq).2

end curve25519
