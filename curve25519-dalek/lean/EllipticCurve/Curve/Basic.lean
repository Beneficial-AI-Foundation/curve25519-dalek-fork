/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Quot
import Mathlib.GroupTheory.GroupAction.Defs
public section

/-! # The abstract curve

`Curve F` is an elliptic curve over the field `F`, up to `F`-isomorphism. Its construction is
hidden: importers see a type, the group `C.Point` of its `F`-rational points with its instances,
and nothing else. Everything else about a curve is said through its models (`MontgomeryModel`,
…), each of which provides `toCurve` and a group isomorphism `pointEquiv : M.Point ≃+
M.toCurve.Point`; see `curve-api.md` §3.

The construction today is the quotient of the nonsingular Weierstrass models (Mathlib's
`WeierstrassCurve.Affine F` with `IsElliptic`, imported privately: no Weierstrass name appears in
this module's interface) by the orbit relation of Mathlib's action of `VariableChange F`, so that
isomorphic models are equal curves; `C.Point` is Mathlib's group of nonsingular affine points of a
chosen representative. Modules that define models reach the construction through
`EllipticCurve.Curve.Impl`, never through this file. -/

universe u

namespace Curve

variable {F : Type u} [Field F]

/-- The nonsingular Weierstrass models over `F`. Hidden, internal. -/
private abbrev Model (F : Type u) [Field F] : Type u :=
  {W : WeierstrassCurve.Affine F // W.IsElliptic}

/-- Mathlib's action of the variable changes on Weierstrass curves preserves `IsElliptic`, so it
restricts to the nonsingular models. Hidden, internal. -/
private instance instMulActionModel :
    MulAction (WeierstrassCurve.VariableChange F) (Model F) where
  smul C W := ⟨C • W.1, have := W.2; inferInstance⟩
  one_smul W := Subtype.ext (one_smul _ W.1)
  mul_smul C C' W := Subtype.ext (mul_smul C C' W.1)

private theorem smul_val (C : WeierstrassCurve.VariableChange F) (W : Model F) :
    (C • W).1 = C • W.1 :=
  rfl

end Curve

/-- An elliptic curve over `F`, up to `F`-isomorphism. Hidden construction: importers see only
`Curve.Point`, its instances, and the lemmas proved about the models of a curve. -/
def Curve (F : Type u) [Field F] : Type u :=
  Quotient (MulAction.orbitRel (WeierstrassCurve.VariableChange F) (Curve.Model F))

namespace Curve

variable {F : Type u} [Field F]

/-- A Weierstrass model representing `C` (hidden, internal). Everything built on the hidden
construction is `noncomputable`: the compiler cannot see through the hidden `Curve`. -/
private noncomputable def toAffine (C : Curve F) : WeierstrassCurve.Affine F :=
  (Quotient.out C).1

private instance (C : Curve F) : C.toAffine.IsElliptic :=
  (Quotient.out C).2

/-- The group of `F`-rational points of `C`. Hidden construction: only the instances below and
the lemmas about the models of `C` are visible. -/
def Point (C : Curve F) : Type u :=
  C.toAffine.Point

/-- The group law on the points of `C`. Hidden construction; it is characterised through the
models, e.g. by `MontgomeryModel.some_add_some_of_u_ne`. -/
@[no_expose] noncomputable instance instAddCommGroupPoint (C : Curve F) :
    AddCommGroup C.Point := by
  classical exact inferInstanceAs (AddCommGroup C.toAffine.Point)

@[no_expose] noncomputable instance instDecidableEqPoint (C : Curve F) [DecidableEq F] :
    DecidableEq C.Point :=
  inferInstanceAs (DecidableEq C.toAffine.Point)

instance instFinitePoint (C : Curve F) [Finite F] : Finite C.Point :=
  Finite.of_equiv (Option {xy : F × F // C.toAffine.Equation xy.1 xy.2})
    C.toAffine.pointEquiv.symm

@[no_expose] noncomputable instance instFintypePoint (C : Curve F) [Fintype F] :
    Fintype C.Point :=
  Fintype.ofFinite C.Point

end Curve
