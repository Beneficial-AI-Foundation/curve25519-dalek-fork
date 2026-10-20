module
public import EllipticCurve.Field.Sign
public import EllipticCurve.Curve.Basic
public import EllipticCurve.Montgomery.Defs
public import EllipticCurve.Montgomery.Lemmas
public import EllipticCurve.Montgomery.Rescale
public import EllipticCurve.Montgomery.Count
public import EllipticCurve.Montgomery.XOnly.Defs
public import EllipticCurve.Montgomery.XOnly.Lemmas
public import EllipticCurve.TwistedEdwards.Defs
public import EllipticCurve.TwistedEdwards.Lemmas
public import EllipticCurve.TwistedEdwards.Coords.Defs
public import EllipticCurve.TwistedEdwards.Coords.Lemmas
public import EllipticCurve.TwistedEdwards.Formulas.Defs
public import EllipticCurve.TwistedEdwards.Formulas.Lemmas
public import EllipticCurve.TwistedEdwards.Encoding.Defs
public import EllipticCurve.TwistedEdwards.Encoding.Lemmas
public import EllipticCurve.TwistedEdwards.Even.Defs
public import EllipticCurve.TwistedEdwards.Even.Lemmas
import EllipticCurve.Weierstrass.PointEquiv

/-! # EllipticCurve

Elliptic-curve models over a field, independent of any particular curve: the sign convention
`ZMod.isNeg` and the absolute value on `ZMod p` (`EllipticCurve.Field.Sign`), the abstract curve
`Curve F` (`EllipticCurve.Curve.Basic`), the Montgomery model `MontgomeryModel F`
(`EllipticCurve.Montgomery.*`, with the rescaling isomorphism in
`EllipticCurve.Montgomery.Rescale`, the point count of a model and its twist in
`EllipticCurve.Montgomery.Count`, and the x-only arithmetic and the Montgomery ladder in
`EllipticCurve.Montgomery.XOnly.*`), the twisted Edwards model `TwistedEdwardsModel F`
(`EllipticCurve.TwistedEdwards.*`) with its coordinate systems
(`EllipticCurve.TwistedEdwards.Coords.*`), the formulas in coordinates
(`EllipticCurve.TwistedEdwards.Formulas.*`), the RFC 8032 point encoding
(`EllipticCurve.TwistedEdwards.Encoding.*`) and the even quotient, the Decaf/Ristretto
construction (`EllipticCurve.TwistedEdwards.Even.*`). The audited generic module
`EllipticCurve.Weierstrass.PointEquiv` (the point map of a variable change of Mathlib's
Weierstrass models, used by the hidden construction of `Curve F`) is imported privately here, so
that it is built with the library but no Weierstrass name reaches importers of this root; import
it directly to use it. `EllipticCurve.Curve.Impl` (the construction interface, internal to model
definition modules) and `EllipticCurve.Proofs.*` (heavy proofs, imported privately by the
properties modules) are deliberately not part of this root. See `curve-api.md`. -/
