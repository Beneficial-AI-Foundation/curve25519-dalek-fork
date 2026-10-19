module
public import EllipticCurve.Curve.Basic
public import EllipticCurve.Montgomery.Defs
public import EllipticCurve.Montgomery.Lemmas
public import EllipticCurve.TwistedEdwards.Defs
public import EllipticCurve.TwistedEdwards.Lemmas
import EllipticCurve.Weierstrass.PointEquiv

/-! # EllipticCurve

Elliptic-curve models over a field, independent of any particular curve: the abstract curve
`Curve F` (`EllipticCurve.Curve.Basic`), the Montgomery model `MontgomeryModel F`
(`EllipticCurve.Montgomery.*`), the twisted Edwards model `TwistedEdwardsModel F`
(`EllipticCurve.TwistedEdwards.*`). The audited generic module
`EllipticCurve.Weierstrass.PointEquiv` (the point map of a variable change of Mathlib's
Weierstrass models, used by the hidden construction of `Curve F`) is imported privately here, so
that it is built with the library but no Weierstrass name reaches importers of this root; import
it directly to use it. `EllipticCurve.Curve.Impl` (the construction interface, internal to model
definition modules) and `EllipticCurve.Proofs.*` (heavy proofs, imported privately by the
properties modules) are deliberately not part of this root. See `curve-api.md`. -/
