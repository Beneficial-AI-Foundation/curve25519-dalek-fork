/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Models.Field.Sign
public import Curve25519.Models.Montgomery.Ladder.Defs
public import Curve25519.Models.Montgomery.Ladder.Lemmas
public import Curve25519.Models.TwistedEdwards.Coords.Defs
public import Curve25519.Models.TwistedEdwards.Coords.Lemmas
public import Curve25519.Models.TwistedEdwards.Formulas.Defs
public import Curve25519.Models.TwistedEdwards.Formulas.Lemmas
public import Curve25519.Models.TwistedEdwards.Encoding.Defs
public import Curve25519.Models.TwistedEdwards.Encoding.Lemmas
public import Curve25519.Models.TwistedEdwards.Even.Defs
public import Curve25519.Models.TwistedEdwards.Even.Lemmas

/-! # Coordinates, encodings and the ladder on elliptic-curve models

What the implementation needs on top of the models of the `EllipticCurve` library, stated for any
field (or any `ZMod p`) rather than for curve25519, under the library's namespaces
(`TwistedEdwardsModel`, `MontgomeryModel`, `ZMod`):

* `Field.Sign`: the sign `ZMod.isNeg` (odd canonical representative) and `ZMod.abs`;
* `TwistedEdwards.Coords`: projective, extended, completed and Niels coordinates (`toPoint`,
  `OnCurve`, `ProjEq`);
* `TwistedEdwards.Formulas`: the addition and doubling formulas on those coordinates;
* `TwistedEdwards.Encoding`: the RFC 8032 encoding of points (`encode`, `decode`);
* `TwistedEdwards.Even`: the 4-torsion `torsion4` and the relation `Rel` of Decaf/Ristretto;
* `Montgomery.Ladder`: projective x-only points `XZ`, the RFC 7748 formulas and the Montgomery
  ladder, with `ladder_eq_xMul`. -/
