/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.CurveModels
public section

/-! # The lookup tables of `window.rs` (audited)

A table is an array of Niels points (`LookupTable T = Array T 8`, `LookupTableRadix32/64/128/256
T = Array T 16/32/64/128`, `NafLookupTable5 T = Array T 8`, `NafLookupTable8 T = Array T 64`),
generic in the entry type `T`. The entry types are the four Niels structures of `Defs.CurveModels`
(`ProjectiveNielsPoint`, `AffineNielsPoint`, in both x86_64 configurations); the class
`PointRepr` collects their `OnCurve`, `toPoint` and `Bounded`, so that each table predicate is
stated once:

- `LookupTable.Represents t P`: entry `j` of `t` is on the curve and represents `(j + 1) • P`;
  likewise for the radix-32…256 tables;
- `NafLookupTable5.Represents t P`, `NafLookupTable8.Represents t P`: entry `k` represents
  `(2 k + 1) • P` (R8);
- `….Bounded t`: every entry satisfies the limb bounds of its type.

The basepoint tables of `edwards.rs` are in `Defs.Edwards`, the precomputations of
`scalar_mul` in `Defs.ScalarMul`. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

/-- A dalek point structure usable as a table entry: its curve predicate, the point it
represents and its limb bounds (the definitions of `Defs.CurveModels`, as instance fields). -/
class PointRepr (T : Type) where
  /-- The entry represents a point (`OnCurve` of its structure). -/
  OnCurve : T → Prop
  /-- The point represented (`toPoint` of its structure). -/
  toPoint : T → curve25519.edwards.Point
  /-- The limb bounds (`Bounded` of its structure). -/
  Bounded : T → Prop

/-! ### The entry types -/

namespace backend.serial.curve_models

noncomputable instance ProjectiveNielsPoint.«x86_64-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«x86_64-tables» where
  OnCurve := ProjectiveNielsPoint.«x86_64-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«x86_64-tables».toPoint
  Bounded := ProjectiveNielsPoint.«x86_64-tables».Bounded

noncomputable instance ProjectiveNielsPoint.«x86_64-no-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«x86_64-no-tables» where
  OnCurve := ProjectiveNielsPoint.«x86_64-no-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«x86_64-no-tables».toPoint
  Bounded := ProjectiveNielsPoint.«x86_64-no-tables».Bounded

noncomputable instance AffineNielsPoint.«x86_64-tables».instPointRepr :
    PointRepr AffineNielsPoint.«x86_64-tables» where
  OnCurve := AffineNielsPoint.«x86_64-tables».OnCurve
  toPoint := AffineNielsPoint.«x86_64-tables».toPoint
  Bounded := AffineNielsPoint.«x86_64-tables».Bounded

noncomputable instance AffineNielsPoint.«x86_64-no-tables».instPointRepr :
    PointRepr AffineNielsPoint.«x86_64-no-tables» where
  OnCurve := AffineNielsPoint.«x86_64-no-tables».OnCurve
  toPoint := AffineNielsPoint.«x86_64-no-tables».toPoint
  Bounded := AffineNielsPoint.«x86_64-no-tables».Bounded

end backend.serial.curve_models

/-! ### The tables -/

namespace window

variable {T : Type} [Inhabited T] [PointRepr T]

/-- Entry `j` of `t` (`j < 8`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTable.Represents (t : LookupTable T) (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 8, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Every entry of `t` satisfies the limb bounds of its type. -/
@[expose] def LookupTable.Bounded (t : LookupTable T) : Prop :=
  ∀ j < 8, PointRepr.Bounded t[j]!

/-- Entry `j` of `t` (`j < 16`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix32.Represents (t : LookupTableRadix32 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 16, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Every entry of `t` satisfies the limb bounds of its type. -/
@[expose] def LookupTableRadix32.Bounded (t : LookupTableRadix32 T) : Prop :=
  ∀ j < 16, PointRepr.Bounded t[j]!

/-- Entry `j` of `t` (`j < 32`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix64.Represents (t : LookupTableRadix64 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 32, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Every entry of `t` satisfies the limb bounds of its type. -/
@[expose] def LookupTableRadix64.Bounded (t : LookupTableRadix64 T) : Prop :=
  ∀ j < 32, PointRepr.Bounded t[j]!

/-- Entry `j` of `t` (`j < 64`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix128.Represents (t : LookupTableRadix128 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 64, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Every entry of `t` satisfies the limb bounds of its type. -/
@[expose] def LookupTableRadix128.Bounded (t : LookupTableRadix128 T) : Prop :=
  ∀ j < 64, PointRepr.Bounded t[j]!

/-- Entry `j` of `t` (`j < 128`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix256.Represents (t : LookupTableRadix256 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 128, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Every entry of `t` satisfies the limb bounds of its type. -/
@[expose] def LookupTableRadix256.Bounded (t : LookupTableRadix256 T) : Prop :=
  ∀ j < 128, PointRepr.Bounded t[j]!

/-- Entry `k` of `t` (`k < 8`) is on the curve and represents the odd multiple `(2 k + 1) • P`. -/
@[expose] def NafLookupTable5.Represents (t : NafLookupTable5 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ k < 8, PointRepr.OnCurve t[k]! ∧ PointRepr.toPoint t[k]! = (2 * k + 1) • P

/-- Every entry of `t` satisfies the limb bounds of its type. -/
@[expose] def NafLookupTable5.Bounded (t : NafLookupTable5 T) : Prop :=
  ∀ k < 8, PointRepr.Bounded t[k]!

/-- Entry `k` of `t` (`k < 64`) is on the curve and represents the odd multiple
`(2 k + 1) • P`. -/
@[expose] def NafLookupTable8.Represents (t : NafLookupTable8 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ k < 64, PointRepr.OnCurve t[k]! ∧ PointRepr.toPoint t[k]! = (2 * k + 1) • P

/-- Every entry of `t` satisfies the limb bounds of its type. -/
@[expose] def NafLookupTable8.Bounded (t : NafLookupTable8 T) : Prop :=
  ∀ k < 64, PointRepr.Bounded t[k]!

end window

end Curve25519Dalek
