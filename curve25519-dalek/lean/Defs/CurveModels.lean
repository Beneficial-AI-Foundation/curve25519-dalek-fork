/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
public import Defs.FieldElement51
public section

/-! # The point structures of `curve_models.rs` (audited)

`ProjectivePoint`, `CompletedPoint`, `AffineNielsPoint` and `ProjectiveNielsPoint` of
`backend/serial/curve_models.rs` implement the coordinate systems `Projective`, `Completed`,
`AffineNiels` and `ProjectiveNiels` of the Edwards model `curve25519.edwards` on
radix-`2^51` limbs. Each structure `S` gets:

- `S.toX : S → curve25519.edwards.X`, its coordinates as field elements (hidden, `toX_def`);
- `S.OnCurve := (toX self).OnCurve`, the algebraic validity (exposed);
- `S.toPoint := (toX self).toPoint`, the point represented, `0` off the curve (hidden,
  `toPoint_def`);
- `S.Bounded`, the limb bounds the code relies on (exposed):
  `< 2^52` for `ProjectivePoint`, `< 2^54` for the three others.

The two x86_64 configurations (`«x86_64-tables»`, `«x86_64-no-tables»`) have distinct
structures with identical bodies, so every definition appears twice. -/

open Aeneas Aeneas.Std
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.curve_models

/-! ### `ProjectivePoint` (`x86_64-tables`) -/

namespace ProjectivePoint.«x86_64-tables»

/-- The projective coordinates `(X : Y : Z)` as field elements. -/
noncomputable def toProjective (self : ProjectivePoint.«x86_64-tables») :
    curve25519.edwards.Projective :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField⟩

theorem toProjective_def (self : ProjectivePoint.«x86_64-tables») :
    self.toProjective = ⟨self.X.toField, self.Y.toField, self.Z.toField⟩ := by
  unfold toProjective
  rfl

/-- `self` represents a point: `Z ≠ 0` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : ProjectivePoint.«x86_64-tables») : Prop :=
  self.toProjective.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectivePoint.«x86_64-tables») :
    curve25519.edwards.Point :=
  self.toProjective.toPoint

theorem toPoint_def (self : ProjectivePoint.«x86_64-tables») :
    self.toPoint = self.toProjective.toPoint := by
  unfold toPoint
  rfl

/-- The limb bounds of a `ProjectivePoint`: all limbs `< 2^52`. -/
@[expose] def Bounded (self : ProjectivePoint.«x86_64-tables») : Prop :=
  (∀ i < 5, self.X[i]!.val < 2 ^ 52) ∧ (∀ i < 5, self.Y[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, self.Z[i]!.val < 2 ^ 52)

end ProjectivePoint.«x86_64-tables»

/-! ### `CompletedPoint` (`x86_64-tables`) -/

namespace CompletedPoint.«x86_64-tables»

/-- The completed coordinates `((X : Z), (Y : T))` as field elements. -/
noncomputable def toCompleted (self : CompletedPoint.«x86_64-tables») :
    curve25519.edwards.Completed :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

theorem toCompleted_def (self : CompletedPoint.«x86_64-tables») :
    self.toCompleted = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toCompleted
  rfl

/-- `self` represents a point: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` is on the curve. -/
@[expose] def OnCurve (self : CompletedPoint.«x86_64-tables») : Prop :=
  self.toCompleted.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : CompletedPoint.«x86_64-tables») :
    curve25519.edwards.Point :=
  self.toCompleted.toPoint

theorem toPoint_def (self : CompletedPoint.«x86_64-tables») :
    self.toPoint = self.toCompleted.toPoint := by
  unfold toPoint
  rfl

/-- The limb bounds of a `CompletedPoint`: all limbs `< 2^54`. -/
@[expose] def Bounded (self : CompletedPoint.«x86_64-tables») : Prop :=
  (∀ i < 5, self.X[i]!.val < 2 ^ 54) ∧ (∀ i < 5, self.Y[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, self.Z[i]!.val < 2 ^ 54) ∧ (∀ i < 5, self.T[i]!.val < 2 ^ 54)

end CompletedPoint.«x86_64-tables»

/-! ### `AffineNielsPoint` (`x86_64-tables`) -/

namespace AffineNielsPoint.«x86_64-tables»

/-- The affine Niels coordinates `(y + x, y - x, 2 d x y)` as field elements. -/
noncomputable def toAffineNiels (self : AffineNielsPoint.«x86_64-tables») :
    curve25519.edwards.AffineNiels :=
  ⟨self.y_plus_x.toField, self.y_minus_x.toField, self.xy2d.toField⟩

theorem toAffineNiels_def (self : AffineNielsPoint.«x86_64-tables») :
    self.toAffineNiels =
      ⟨self.y_plus_x.toField, self.y_minus_x.toField, self.xy2d.toField⟩ := by
  unfold toAffineNiels
  rfl

/-- `self` represents a point: with `x := ((y + x) - (y - x)) / 2` and
`y := ((y + x) + (y - x)) / 2`, `(x, y)` is on the curve and `xy2d = 2 d x y`. -/
@[expose] def OnCurve (self : AffineNielsPoint.«x86_64-tables») : Prop :=
  self.toAffineNiels.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffineNielsPoint.«x86_64-tables») :
    curve25519.edwards.Point :=
  self.toAffineNiels.toPoint

theorem toPoint_def (self : AffineNielsPoint.«x86_64-tables») :
    self.toPoint = self.toAffineNiels.toPoint := by
  unfold toPoint
  rfl

/-- The limb bounds of an `AffineNielsPoint`: all limbs `< 2^54`. -/
@[expose] def Bounded (self : AffineNielsPoint.«x86_64-tables») : Prop :=
  (∀ i < 5, self.y_plus_x[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, self.y_minus_x[i]!.val < 2 ^ 54) ∧ (∀ i < 5, self.xy2d[i]!.val < 2 ^ 54)

/-- Needed for `t[j]!` on tables of `AffineNielsPoint`s; the default is never observed for
in-range indices. -/
instance instInhabited : Inhabited (AffineNielsPoint.«x86_64-tables») :=
  ⟨⟨default, default, default⟩⟩

end AffineNielsPoint.«x86_64-tables»

/-! ### `ProjectiveNielsPoint` (`x86_64-tables`) -/

namespace ProjectiveNielsPoint.«x86_64-tables»

/-- The projective Niels coordinates `(Y + X : Y - X : Z : 2 d T)` as field elements. -/
noncomputable def toProjectiveNiels (self : ProjectiveNielsPoint.«x86_64-tables») :
    curve25519.edwards.ProjectiveNiels :=
  ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩

theorem toProjectiveNiels_def (self : ProjectiveNielsPoint.«x86_64-tables») :
    self.toProjectiveNiels =
      ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩ := by
  unfold toProjectiveNiels
  rfl

/-- `self` represents a point: `Z ≠ 0`, and with `X := ((Y + X) - (Y - X)) / 2` and
`Y := ((Y + X) + (Y - X)) / 2`, `(X / Z, Y / Z)` is on the curve and `T2d Z = 2 d X Y`. -/
@[expose] def OnCurve (self : ProjectiveNielsPoint.«x86_64-tables») : Prop :=
  self.toProjectiveNiels.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectiveNielsPoint.«x86_64-tables») :
    curve25519.edwards.Point :=
  self.toProjectiveNiels.toPoint

theorem toPoint_def (self : ProjectiveNielsPoint.«x86_64-tables») :
    self.toPoint = self.toProjectiveNiels.toPoint := by
  unfold toPoint
  rfl

/-- The limb bounds of a `ProjectiveNielsPoint`: all limbs `< 2^54`. -/
@[expose] def Bounded (self : ProjectiveNielsPoint.«x86_64-tables») : Prop :=
  (∀ i < 5, self.Y_plus_X[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, self.Y_minus_X[i]!.val < 2 ^ 54) ∧ (∀ i < 5, self.Z[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, self.T2d[i]!.val < 2 ^ 54)

/-- Needed for `t[j]!` on tables of `ProjectiveNielsPoint`s; the default is never observed for
in-range indices. -/
instance instInhabited : Inhabited (ProjectiveNielsPoint.«x86_64-tables») :=
  ⟨⟨default, default, default, default⟩⟩

end ProjectiveNielsPoint.«x86_64-tables»

/-! ### `ProjectivePoint` (`x86_64-no-tables`) -/

namespace ProjectivePoint.«x86_64-no-tables»

/-- The projective coordinates `(X : Y : Z)` as field elements. -/
noncomputable def toProjective (self : ProjectivePoint.«x86_64-no-tables») :
    curve25519.edwards.Projective :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField⟩

theorem toProjective_def (self : ProjectivePoint.«x86_64-no-tables») :
    self.toProjective = ⟨self.X.toField, self.Y.toField, self.Z.toField⟩ := by
  unfold toProjective
  rfl

/-- `self` represents a point: `Z ≠ 0` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : ProjectivePoint.«x86_64-no-tables») : Prop :=
  self.toProjective.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectivePoint.«x86_64-no-tables») :
    curve25519.edwards.Point :=
  self.toProjective.toPoint

theorem toPoint_def (self : ProjectivePoint.«x86_64-no-tables») :
    self.toPoint = self.toProjective.toPoint := by
  unfold toPoint
  rfl

/-- The limb bounds of a `ProjectivePoint`: all limbs `< 2^52`. -/
@[expose] def Bounded (self : ProjectivePoint.«x86_64-no-tables») : Prop :=
  (∀ i < 5, self.X[i]!.val < 2 ^ 52) ∧ (∀ i < 5, self.Y[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, self.Z[i]!.val < 2 ^ 52)

end ProjectivePoint.«x86_64-no-tables»

/-! ### `CompletedPoint` (`x86_64-no-tables`) -/

namespace CompletedPoint.«x86_64-no-tables»

/-- The completed coordinates `((X : Z), (Y : T))` as field elements. -/
noncomputable def toCompleted (self : CompletedPoint.«x86_64-no-tables») :
    curve25519.edwards.Completed :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

theorem toCompleted_def (self : CompletedPoint.«x86_64-no-tables») :
    self.toCompleted = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toCompleted
  rfl

/-- `self` represents a point: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` is on the curve. -/
@[expose] def OnCurve (self : CompletedPoint.«x86_64-no-tables») : Prop :=
  self.toCompleted.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : CompletedPoint.«x86_64-no-tables») :
    curve25519.edwards.Point :=
  self.toCompleted.toPoint

theorem toPoint_def (self : CompletedPoint.«x86_64-no-tables») :
    self.toPoint = self.toCompleted.toPoint := by
  unfold toPoint
  rfl

/-- The limb bounds of a `CompletedPoint`: all limbs `< 2^54`. -/
@[expose] def Bounded (self : CompletedPoint.«x86_64-no-tables») : Prop :=
  (∀ i < 5, self.X[i]!.val < 2 ^ 54) ∧ (∀ i < 5, self.Y[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, self.Z[i]!.val < 2 ^ 54) ∧ (∀ i < 5, self.T[i]!.val < 2 ^ 54)

end CompletedPoint.«x86_64-no-tables»

/-! ### `AffineNielsPoint` (`x86_64-no-tables`) -/

namespace AffineNielsPoint.«x86_64-no-tables»

/-- The affine Niels coordinates `(y + x, y - x, 2 d x y)` as field elements. -/
noncomputable def toAffineNiels (self : AffineNielsPoint.«x86_64-no-tables») :
    curve25519.edwards.AffineNiels :=
  ⟨self.y_plus_x.toField, self.y_minus_x.toField, self.xy2d.toField⟩

theorem toAffineNiels_def (self : AffineNielsPoint.«x86_64-no-tables») :
    self.toAffineNiels =
      ⟨self.y_plus_x.toField, self.y_minus_x.toField, self.xy2d.toField⟩ := by
  unfold toAffineNiels
  rfl

/-- `self` represents a point: with `x := ((y + x) - (y - x)) / 2` and
`y := ((y + x) + (y - x)) / 2`, `(x, y)` is on the curve and `xy2d = 2 d x y`. -/
@[expose] def OnCurve (self : AffineNielsPoint.«x86_64-no-tables») : Prop :=
  self.toAffineNiels.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffineNielsPoint.«x86_64-no-tables») :
    curve25519.edwards.Point :=
  self.toAffineNiels.toPoint

theorem toPoint_def (self : AffineNielsPoint.«x86_64-no-tables») :
    self.toPoint = self.toAffineNiels.toPoint := by
  unfold toPoint
  rfl

/-- The limb bounds of an `AffineNielsPoint`: all limbs `< 2^54`. -/
@[expose] def Bounded (self : AffineNielsPoint.«x86_64-no-tables») : Prop :=
  (∀ i < 5, self.y_plus_x[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, self.y_minus_x[i]!.val < 2 ^ 54) ∧ (∀ i < 5, self.xy2d[i]!.val < 2 ^ 54)

/-- Needed for `t[j]!` on tables of `AffineNielsPoint`s; the default is never observed for
in-range indices. -/
instance instInhabited : Inhabited (AffineNielsPoint.«x86_64-no-tables») :=
  ⟨⟨default, default, default⟩⟩

end AffineNielsPoint.«x86_64-no-tables»

/-! ### `ProjectiveNielsPoint` (`x86_64-no-tables`) -/

namespace ProjectiveNielsPoint.«x86_64-no-tables»

/-- The projective Niels coordinates `(Y + X : Y - X : Z : 2 d T)` as field elements. -/
noncomputable def toProjectiveNiels (self : ProjectiveNielsPoint.«x86_64-no-tables») :
    curve25519.edwards.ProjectiveNiels :=
  ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩

theorem toProjectiveNiels_def (self : ProjectiveNielsPoint.«x86_64-no-tables») :
    self.toProjectiveNiels =
      ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩ := by
  unfold toProjectiveNiels
  rfl

/-- `self` represents a point: `Z ≠ 0`, and with `X := ((Y + X) - (Y - X)) / 2` and
`Y := ((Y + X) + (Y - X)) / 2`, `(X / Z, Y / Z)` is on the curve and `T2d Z = 2 d X Y`. -/
@[expose] def OnCurve (self : ProjectiveNielsPoint.«x86_64-no-tables») : Prop :=
  self.toProjectiveNiels.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectiveNielsPoint.«x86_64-no-tables») :
    curve25519.edwards.Point :=
  self.toProjectiveNiels.toPoint

theorem toPoint_def (self : ProjectiveNielsPoint.«x86_64-no-tables») :
    self.toPoint = self.toProjectiveNiels.toPoint := by
  unfold toPoint
  rfl

/-- The limb bounds of a `ProjectiveNielsPoint`: all limbs `< 2^54`. -/
@[expose] def Bounded (self : ProjectiveNielsPoint.«x86_64-no-tables») : Prop :=
  (∀ i < 5, self.Y_plus_X[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, self.Y_minus_X[i]!.val < 2 ^ 54) ∧ (∀ i < 5, self.Z[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, self.T2d[i]!.val < 2 ^ 54)

/-- Needed for `t[j]!` on tables of `ProjectiveNielsPoint`s; the default is never observed for
in-range indices. -/
instance instInhabited : Inhabited (ProjectiveNielsPoint.«x86_64-no-tables») :=
  ⟨⟨default, default, default, default⟩⟩

end ProjectiveNielsPoint.«x86_64-no-tables»

end Curve25519Dalek.backend.serial.curve_models
