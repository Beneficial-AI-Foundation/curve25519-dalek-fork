/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import EllipticCurve.Curve.Basic
import all EllipticCurve.Curve.Basic
import EllipticCurve.Weierstrass.PointEquiv
import Mathlib.Data.Quot
import Mathlib.GroupTheory.GroupAction.Defs
public section

/-! # Construction interface for `Curve` (internal)

The only place where the hidden construction of `Curve F` (`EllipticCurve.Curve.Basic`) is
reached: a model module (`EllipticCurve.Montgomery.Defs`, …) builds `M.toCurve` with
`Curve.ofWeierstrass` and its `pointEquiv` with `Curve.pointEquivOfWeierstrass`, and proves
equalities of curves with `Curve.ofWeierstrass_eq` by exhibiting a variable change.

**Internal.** This module must only ever be imported privately (`import EllipticCurve.Curve.Impl`)
by model definition modules, never `public import`ed: its statements mention Mathlib's
`WeierstrassCurve`, which no API module may expose. When the
construction of `Curve F` changes, this module changes with it and nothing else does. -/

universe u

namespace Curve

variable {F : Type u} [Field F]

/-- The curve of a nonsingular Weierstrass model: its class in the quotient. -/
noncomputable def ofWeierstrass (W : WeierstrassCurve.Affine F) [W.IsElliptic] : Curve F :=
  Quotient.mk _ ⟨W, ‹W.IsElliptic›⟩

/-- Isomorphic models give the same curve: `ofWeierstrass` is invariant under variable changes. -/
theorem ofWeierstrass_eq (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) : ofWeierstrass (C • W) = ofWeierstrass W :=
  Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨C, rfl⟩)

/-- Equal models give the same curve (the `IsElliptic` instances are irrelevant). -/
theorem ofWeierstrass_congr {W W' : WeierstrassCurve.Affine F} [W.IsElliptic] [W'.IsElliptic]
    (h : W = W') : ofWeierstrass W = ofWeierstrass W' := by
  subst h
  rfl

/-- The representative chosen for `ofWeierstrass W` is a variable change of `W`. -/
private theorem exists_smul_eq_toAffine (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    ∃ C : WeierstrassCurve.VariableChange F, C • W = (ofWeierstrass W).toAffine := by
  have h := Quotient.mk_out (s := MulAction.orbitRel (WeierstrassCurve.VariableChange F) (Model F))
    ⟨W, ‹W.IsElliptic›⟩
  obtain ⟨C, hC⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  exact ⟨C, congrArg Subtype.val hC⟩

/-- Transport of point groups along an equality of models. Internal. -/
private def pointEquivOfEq {W W' : WeierstrassCurve.Affine F} [DecidableEq F] (h : W = W') :
    W.Point ≃+ W'.Point := by
  subst h
  exact AddEquiv.refl _

open scoped Classical in
/-- `pointEquivOfWeierstrass` with the classical `DecidableEq F` (the one of the hidden group law
on `Curve.Point`). Internal. -/
private noncomputable def pointEquivOfWeierstrassAux (W : WeierstrassCurve.Affine F)
    [W.IsElliptic] : (ofWeierstrass W).Point ≃+ W.Point :=
  (pointEquivOfEq (Classical.choose_spec (exists_smul_eq_toAffine W)).symm).trans
    (WeierstrassCurve.Affine.Point.variableChange W
      (Classical.choose (exists_smul_eq_toAffine W))).symm

/-- The points of `ofWeierstrass W` are the points of `W`, as groups: the point map of the
variable change between `W` and the chosen representative of its class
(`EllipticCurve.Weierstrass.PointEquiv`). The group law on `Curve.Point` is Mathlib's with the
classical `DecidableEq F`; this works for whichever `DecidableEq F` is in scope, by
`Subsingleton`. -/
noncomputable def pointEquivOfWeierstrass (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [DecidableEq F] : (ofWeierstrass W).Point ≃+ W.Point := by
  obtain rfl : ‹DecidableEq F› = fun a b => Classical.propDecidable (a = b) :=
    Subsingleton.elim _ _
  exact pointEquivOfWeierstrassAux W

end Curve
