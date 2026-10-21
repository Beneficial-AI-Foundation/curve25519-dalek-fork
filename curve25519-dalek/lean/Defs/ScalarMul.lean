/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Window
public section

/-! # The precomputations of `backend/serial/scalar_mul/precomputed_straus.rs` (audited)

`VartimePrecomputedStraus` holds one `NafLookupTable8` of affine Niels points per static point;
`Represents self ps` says that these tables are, in order, the NAF tables of the points `ps`,
and `Bounded self` that every entry meets the limb bounds. The
backend enum `backend.VartimePrecomputedStraus` (whose only variant is `Scalar`) and its alias
`edwards.VartimeEdwardsPrecomputation` forward to it. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

namespace backend.serial.scalar_mul.precomputed_straus

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».Represents
    (self : VartimePrecomputedStraus.«x86_64-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- Every entry of every table of `self` satisfies the limb bounds. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».Bounded
    (self : VartimePrecomputedStraus.«x86_64-tables») : Prop :=
  ∀ t ∈ self.static_lookup_tables.val, window.NafLookupTable8.Bounded t

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».Represents
    (self : VartimePrecomputedStraus.«x86_64-no-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- Every entry of every table of `self` satisfies the limb bounds. -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».Bounded
    (self : VartimePrecomputedStraus.«x86_64-no-tables») : Prop :=
  ∀ t ∈ self.static_lookup_tables.val, window.NafLookupTable8.Bounded t

end backend.serial.scalar_mul.precomputed_straus

namespace backend

/-- The serial precomputation inside the backend enum represents `ps`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».Represents :
    VartimePrecomputedStraus.«x86_64-tables» → List curve25519.edwards.Point → Prop
  | .Scalar pre, ps => pre.Represents ps

/-- The serial precomputation inside the backend enum is bounded. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».Bounded :
    VartimePrecomputedStraus.«x86_64-tables» → Prop
  | .Scalar pre => pre.Bounded

/-- The serial precomputation inside the backend enum represents `ps`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».Represents :
    VartimePrecomputedStraus.«x86_64-no-tables» → List curve25519.edwards.Point → Prop
  | .Scalar pre, ps => pre.Represents ps

/-- The serial precomputation inside the backend enum is bounded. -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».Bounded :
    VartimePrecomputedStraus.«x86_64-no-tables» → Prop
  | .Scalar pre => pre.Bounded

end backend

end Curve25519Dalek
