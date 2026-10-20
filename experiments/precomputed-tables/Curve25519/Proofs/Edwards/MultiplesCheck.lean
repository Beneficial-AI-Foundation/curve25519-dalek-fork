/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
import all Curve25519.Basic
public section

/-! # Kernel checks of multiples of the basepoint (not audited)

The tools for the certificates of `Curve25519.Proofs.Edwards.OddMultiples` and
`Curve25519.Proofs.Edwards.BasepointTable`: `n • B = (x, y)` follows from the curve equation at
`(x, y)` and projective equality of `n • B` (the double-and-add chain `Extended.nsmul`) with
`(x : y : 1 : x y)` in extended coordinates, both decided by kernel computation
(`decide +kernel`) once the model is in numeral form (`edwards_eq'`), as in
`Curve25519.Proofs.Edwards.Certs`. -/

namespace curve25519.Proofs

open TwistedEdwardsModel

/-- `edwards` with its coefficients as numerals, for the kernel. -/
theorem edwards_eq' :
    edwards = ⟨-1, ((37095705934669439343138083508754565189542113879843219016388785533085940283555 :
      ℕ) : ZMod p)⟩ := by
  rw [edwards_def, a_def, d_eq_natCast]

/-- The basepoint in extended coordinates of a model, as numerals. -/
@[expose] noncomputable def basepointExt (E : TwistedEdwardsModel (ZMod p)) : E.Extended :=
  ⟨15112221349535400772501151409588531511454012693041857206046113283949847762202,
    46316835694926478169428394003475163141307993866256225615783033603165251855960, 1,
    15112221349535400772501151409588531511454012693041857206046113283949847762202 *
      46316835694926478169428394003475163141307993866256225615783033603165251855960⟩

/-- `n • B = (x, y)` from the curve equation at `(x, y)` and projective equality of `n • B` with
`(x : y : 1 : x y)` in extended coordinates. -/
theorem nsmul_basepoint_of_check {x y : ZMod p} {n : ℕ} (h : edwards.Equation x y ∧
    (Extended.nsmul n (basepointExt edwards)).ProjEq ⟨x, y, 1, x * y⟩) :
    (n • basepoint).x = x ∧ (n • basepoint).y = y := by
  have hB : basepoint.toExtended = basepointExt edwards := by
    rw [Point.toExtended, basepoint_x_eq, basepoint_y_eq]
    rfl
  have hn : n • basepoint = (⟨x, y, h.1⟩ : edwards.Point) :=
    calc n • basepoint = n • basepoint.toExtended.toPoint := by rw [Point.toPoint_toExtended]
      _ = (Extended.nsmul n basepoint.toExtended).toPoint :=
        (Extended.toPoint_nsmul (Point.onCurve_toExtended basepoint) n).symm
      _ = (⟨x, y, h.1⟩ : edwards.Point).toExtended.toPoint :=
        (Extended.projEq_iff_toPoint_eq
          (Extended.nsmul_onCurve (Point.onCurve_toExtended basepoint) n)
          (Point.onCurve_toExtended _)).mp (by rw [hB]; exact h.2)
      _ = _ := Point.toPoint_toExtended _
  rw [hn]
  exact ⟨rfl, rfl⟩

end curve25519.Proofs
