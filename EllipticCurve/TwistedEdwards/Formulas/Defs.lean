/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Coords.Lemmas
public section

/-! # Twisted Edwards models: formulas in coordinates

The group operations in the coordinate systems of `EllipticCurve.TwistedEdwards.Coords.Defs`,
as exposed formulas, exactly as curve25519-dalek's `curve_models.rs` computes them:

* `Projective.double` ("dbl-2008-bbjlp", `ProjectivePoint::double`), the four mixed
  additions `Extended.addProjectiveNiels`, `Extended.subProjectiveNiels`, `Extended.addAffineNiels`,
  `Extended.subAffineNiels` (`Add`/`Sub` of `EdwardsPoint` with a Niels point), all into
  completed coordinates. These are the `a = -1` formulas of Hisil–Wong–Carter–Dawson 2008; they
  are defined for every model and correct when `a = -1`
  (`EllipticCurve.TwistedEdwards.Formulas.Lemmas`).
* `Extended.add` ("add-2008-hwcd", the complete extended addition for any `a`),
  `Extended.double`, the structurally recursive `Extended.nsmul` by double-and-add, and the
  zero test `Extended.IsZero`: field inversion appears nowhere, so that kernel `decide` can
  evaluate them on constants (the certificate engine).

Correctness with respect to `toPoint` is in `EllipticCurve.TwistedEdwards.Formulas.Lemmas`. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F}

namespace Projective

/-- Doubling `(X : Y : Z) ↦ ((X : Z), (Y : T))` by "dbl-2008-bbjlp" for `a = -1`
(`ProjectivePoint::double`): `XX = X²`, `YY = Y²`, `ZZ2 = 2 Z²`, `X_plus_Y_sq = (X + Y)²`,
`YY_plus_XX = YY + XX`, `YY_minus_XX = YY - XX`; the result is
`(X_plus_Y_sq - YY_plus_XX, YY_plus_XX, YY_minus_XX, ZZ2 - YY_minus_XX)`. -/
@[expose] def double (P : E.Projective) : E.Completed :=
  let XX := P.X ^ 2
  let YY := P.Y ^ 2
  let ZZ2 := 2 * P.Z ^ 2
  let X_plus_Y_sq := (P.X + P.Y) ^ 2
  let YY_plus_XX := YY + XX
  let YY_minus_XX := YY - XX
  ⟨X_plus_Y_sq - YY_plus_XX, YY_plus_XX, YY_minus_XX, ZZ2 - YY_minus_XX⟩

end Projective

namespace Extended

/-- Mixed addition of an extended point and a projective Niels point for `a = -1`
(`&EdwardsPoint + &ProjectiveNielsPoint`): `PP = (Y₁ + X₁) (Y₂ + X₂)`,
`MM = (Y₁ - X₁) (Y₂ - X₂)`, `TT2d = T₁ T2d₂`, `ZZ2 = 2 Z₁ Z₂`; the result is
`(PP - MM, PP + MM, ZZ2 + TT2d, ZZ2 - TT2d)`. -/
@[expose] def addProjectiveNiels (P : E.Extended) (Q : E.ProjectiveNiels) : E.Completed :=
  let Y_plus_X := P.Y + P.X
  let Y_minus_X := P.Y - P.X
  let PP := Y_plus_X * Q.YplusX
  let MM := Y_minus_X * Q.YminusX
  let TT2d := P.T * Q.T2d
  let ZZ := P.Z * Q.Z
  let ZZ2 := ZZ + ZZ
  ⟨PP - MM, PP + MM, ZZ2 + TT2d, ZZ2 - TT2d⟩

/-- Mixed subtraction of a projective Niels point from an extended point for `a = -1`
(`&EdwardsPoint - &ProjectiveNielsPoint`): `PM = (Y₁ + X₁) (Y₂ - X₂)`,
`MP = (Y₁ - X₁) (Y₂ + X₂)`, `TT2d = T₁ T2d₂`, `ZZ2 = 2 Z₁ Z₂`; the result is
`(PM - MP, PM + MP, ZZ2 - TT2d, ZZ2 + TT2d)`. -/
@[expose] def subProjectiveNiels (P : E.Extended) (Q : E.ProjectiveNiels) : E.Completed :=
  let Y_plus_X := P.Y + P.X
  let Y_minus_X := P.Y - P.X
  let PM := Y_plus_X * Q.YminusX
  let MP := Y_minus_X * Q.YplusX
  let TT2d := P.T * Q.T2d
  let ZZ := P.Z * Q.Z
  let ZZ2 := ZZ + ZZ
  ⟨PM - MP, PM + MP, ZZ2 - TT2d, ZZ2 + TT2d⟩

/-- Mixed addition of an extended point and an affine Niels point for `a = -1`
(`&EdwardsPoint + &AffineNielsPoint`): `PP = (Y₁ + X₁) (y₂ + x₂)`,
`MM = (Y₁ - X₁) (y₂ - x₂)`, `Txy2d = T₁ xy2d₂`, `Z2 = 2 Z₁`; the result is
`(PP - MM, PP + MM, Z2 + Txy2d, Z2 - Txy2d)`. -/
@[expose] def addAffineNiels (P : E.Extended) (Q : E.AffineNiels) : E.Completed :=
  let Y_plus_X := P.Y + P.X
  let Y_minus_X := P.Y - P.X
  let PP := Y_plus_X * Q.yPlusX
  let MM := Y_minus_X * Q.yMinusX
  let Txy2d := P.T * Q.xy2d
  let Z2 := P.Z + P.Z
  ⟨PP - MM, PP + MM, Z2 + Txy2d, Z2 - Txy2d⟩

/-- Mixed subtraction of an affine Niels point from an extended point for `a = -1`
(`&EdwardsPoint - &AffineNielsPoint`): `PM = (Y₁ + X₁) (y₂ - x₂)`,
`MP = (Y₁ - X₁) (y₂ + x₂)`, `Txy2d = T₁ xy2d₂`, `Z2 = 2 Z₁`; the result is
`(PM - MP, PM + MP, Z2 - Txy2d, Z2 + Txy2d)`. -/
@[expose] def subAffineNiels (P : E.Extended) (Q : E.AffineNiels) : E.Completed :=
  let Y_plus_X := P.Y + P.X
  let Y_minus_X := P.Y - P.X
  let PM := Y_plus_X * Q.yMinusX
  let MP := Y_minus_X * Q.yPlusX
  let Txy2d := P.T * Q.xy2d
  let Z2 := P.Z + P.Z
  ⟨PM - MP, PM + MP, Z2 - Txy2d, Z2 + Txy2d⟩

/-- The complete addition in extended coordinates for any `a`, "add-2008-hwcd"
(Hisil–Wong–Carter–Dawson 2008, §3.1): `A = X₁ X₂`, `B = Y₁ Y₂`, `C = d T₁ T₂`,
`D = Z₁ Z₂`, `E = (X₁ + Y₁) (X₂ + Y₂) - A - B`, `F = D - C`, `G = D + C`, `H = B - a A`; the
result is `(E F : G H : F G : E H)`. No inversion: kernel `decide` can evaluate it. -/
@[expose] def add (P Q : E.Extended) : E.Extended :=
  let A := P.X * Q.X
  let B := P.Y * Q.Y
  let C := E.d * P.T * Q.T
  let D := P.Z * Q.Z
  let e := (P.X + P.Y) * (Q.X + Q.Y) - A - B
  let f := D - C
  let G := D + C
  let H := B - E.a * A
  ⟨e * f, G * H, f * G, e * H⟩

/-- Doubling in extended coordinates: `P.add P`. -/
@[expose] def double (P : E.Extended) : E.Extended :=
  P.add P

/-- Double-and-add with fuel `k`: `nsmulAux P k n` represents `n • P` for `n < 2 ^ k`
(`nsmulAux_spec` in `EllipticCurve.TwistedEdwards.Formulas.Lemmas`). Structural recursion on
the fuel, so that kernel `decide` can evaluate it. -/
@[expose] def nsmulAux (P : E.Extended) : ℕ → ℕ → E.Extended
  | 0, _ => identity
  | k + 1, n =>
    if n = 0 then identity
    else
      let Q := nsmulAux P k (n / 2)
      if n % 2 = 0 then Q.double else Q.double.add P

/-- Scalar multiplication `n • P` in extended coordinates by double-and-add on `add`, without
inversion: the certificate engine for constants (`toPoint_nsmul`). -/
@[expose] def nsmul (n : ℕ) (P : E.Extended) : E.Extended :=
  nsmulAux P n n

/-- The zero test without inversion: `(X : Y : Z : T)` represents `0 = (0, 1)` exactly when
`X = 0` and `Y = Z` (`isZero_iff`). -/
@[expose] def IsZero (P : E.Extended) : Prop :=
  P.X = 0 ∧ P.Y = P.Z

instance instDecidableIsZero [DecidableEq F] (P : E.Extended) : Decidable P.IsZero :=
  inferInstanceAs (Decidable (_ ∧ _))

end Extended

end TwistedEdwardsModel
