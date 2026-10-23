/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Aeneas
public section

/-! # Field backends, for proofs shared by all configurations

The point functions (`curve_models`, `edwards`, `ristretto`, …) are translated once per
configuration, but their bodies agree up to the field backend: `FieldElement51` with `u64` limbs
for `«x86_64-tables»` and `«x86_64-no-tables»`, `FieldElement2625` with `u32` limbs for
`«i686-tables»` and `«i686-no-tables»`. A `Backend` bundles what the point proofs use of a field
backend: the element type `F`, its value `toField`, the operations as `Result` functions, and
four abstract limb bounds; the operations' specs, stated with `toField` and the bounds, are
propositions (`AddSpec`, `MulSpec`, …) that the instance files prove.

| bound   | meaning                               | `U64`         | `U32`          |
|---------|---------------------------------------|---------------|----------------|
| `Red`   | output of `mul`, `sub`, `square`, …   | `LimbsLt 52`  | `LimbsLt 26`   |
| `Sum2`  | sum of two `Red`; `square` input      | `LimbsLt 53`  | `LimbsLt 27`   |
| `MulIn` | `mul`, `sub`, `neg` input             | `LimbsLt 54`  | `MulBounded`   |
| `Niels` | coordinates of the Niels points       | `LimbsLt 54`  | `LimbsLt 27`   |

A point function then has a generic counterpart (same body, field calls through the backend,
the result built by a constructor argument `mk`) with a generic spec, proved once. The
translated function of each configuration is `rfl`-equal to the generic one at the instance
(`Proofs/Helpers/Backend/U64.lean`, `…/U32.lean`), whose bounds are by definition the concrete
predicates, so each configuration's statement follows in a few lines. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

/-- A field backend: element type, value in `ZMod p`, operations, and limb bounds. -/
structure Backend where
  /-- the field-element type -/
  F : Type
  /-- the represented element of `ZMod p` -/
  toField : F → ZMod p
  /-- output bound of `mul`, `sub`, `square`, `neg` -/
  Red : F → Prop
  /-- bound of the sum of two `Red` elements -/
  Sum2 : F → Prop
  /-- input bound of `mul`, `sub`, `neg` -/
  MulIn : F → Prop
  /-- bound of the coordinates of `ProjectiveNielsPoint` and `AffineNielsPoint` -/
  Niels : F → Prop
  /-- `Add<&FieldElement> for &FieldElement` -/
  add : F → F → Result F
  /-- `Sub<&FieldElement> for &FieldElement` -/
  sub : F → F → Result F
  /-- `Mul<&FieldElement> for &FieldElement` -/
  mul : F → F → Result F
  /-- `FieldElement::square` -/
  square : F → Result F
  /-- `FieldElement::square2`: twice the square -/
  square2 : F → Result F
  /-- `Neg for &FieldElement` -/
  neg : F → Result F
  /-- `PartialEq for FieldElement` -/
  eq : F → F → Result Bool
  /-- `EDWARDS_D` -/
  edwardsD : Result F
  red_sum2 : ∀ {a}, Red a → Sum2 a
  sum2_mulIn : ∀ {a}, Sum2 a → MulIn a
  red_niels : ∀ {a}, Red a → Niels a
  niels_mulIn : ∀ {a}, Niels a → MulIn a

namespace Backend

variable (B : Backend)

theorem red_mulIn {a : B.F} (h : B.Red a) : B.MulIn a := B.sum2_mulIn (B.red_sum2 h)

/-! The operations' specs, as propositions: a generic theorem takes exactly the specs it uses, so
that each configuration's theorem depends on the same axioms as the field specs it uses. -/

/-- `add` of two `Red` elements. -/
abbrev AddSpec : Prop := ∀ a b, B.Red a → B.Red b →
  B.add a b ⦃ r => B.toField r = B.toField a + B.toField b ∧ B.Sum2 r ⦄

/-- `add` of a `Sum2` and a `Red` element. -/
abbrev AddSum2Spec : Prop := ∀ a b, B.Sum2 a → B.Red b →
  B.add a b ⦃ r => B.toField r = B.toField a + B.toField b ∧ B.MulIn r ⦄

/-- `sub` of two `MulIn` elements. -/
abbrev SubSpec : Prop := ∀ a b, B.MulIn a → B.MulIn b →
  B.sub a b ⦃ r => B.toField r = B.toField a - B.toField b ∧ B.Red r ⦄

/-- `mul` of two `MulIn` elements. -/
abbrev MulSpec : Prop := ∀ a b, B.MulIn a → B.MulIn b →
  B.mul a b ⦃ r => B.toField r = B.toField a * B.toField b ∧ B.Red r ⦄

/-- `square` of a `Sum2` element. -/
abbrev SquareSpec : Prop := ∀ a, B.Sum2 a →
  B.square a ⦃ r => B.toField r = B.toField a ^ 2 ∧ B.Red r ⦄

/-- `square2` of a `Sum2` element. -/
abbrev Square2Spec : Prop := ∀ a, B.Sum2 a →
  B.square2 a ⦃ r => B.toField r = 2 * B.toField a ^ 2 ∧ B.Sum2 r ⦄

/-- `neg` of a `MulIn` element. -/
abbrev NegSpec : Prop := ∀ a, B.MulIn a →
  B.neg a ⦃ r => B.toField r = -B.toField a ∧ B.Red r ⦄

/-- `eq` decides equality in `ZMod p`. -/
abbrev EqSpec : Prop := ∀ a b, B.eq a b ⦃ c => (c = true ↔ B.toField a = B.toField b) ⦄

/-- `EDWARDS_D` is `d`. -/
abbrev EdwardsDSpec : Prop := B.edwardsD ⦃ r => B.toField r = d ∧ B.Red r ⦄

end Backend

end Curve25519Dalek
