/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Window
import Curve25519.Proofs.Edwards.OddMultiples
import Proofs.Helpers.TableConstants
public section

/-! # `AFFINE_ODD_MULTIPLES_OF_BASEPOINT`

Entry `k` is the affine Niels form of `(2 k + 1) • B`: its limbs' values are `y + x`, `y - x`,
`2 d x y` modulo `p` for the coordinates `(x, y)` certified in
`Curve25519.Proofs.Edwards.OddMultiples`, checked by kernel computation on the numerals. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.u64.constants

/-- The limbs of the table: entry `k` has the Niels coordinates of `oddMultiplesCoords[k]`
modulo `p`, and limbs `< 2^54`. -/
private theorem AFFINE_ODD_MULTIPLES_OF_BASEPOINT_eq :
    ∃ t, AFFINE_ODD_MULTIPLES_OF_BASEPOINT = ok t ∧ ∀ k < 64,
      t[k]!.y_plus_x.asNat % p = (Proofs.oddMultiplesCoords[k]!.2 +
        Proofs.oddMultiplesCoords[k]!.1) % p ∧
      (t[k]!.y_minus_x.asNat + Proofs.oddMultiplesCoords[k]!.1) % p =
        Proofs.oddMultiplesCoords[k]!.2 % p ∧
      t[k]!.xy2d.asNat % p = 2 * dNat * Proofs.oddMultiplesCoords[k]!.1 *
        Proofs.oddMultiplesCoords[k]!.2 % p ∧
      t[k]!.Bounded := by
  unfold AFFINE_ODD_MULTIPLES_OF_BASEPOINT
  simp only [FieldElement51.from_limbs, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [p_eq_numeral]
  simp only [asNat_def, Array.asNat_def, AffineNielsPoint.«x86_64-tables».Bounded]
  decide +kernel

/-- `AFFINE_ODD_MULTIPLES_OF_BASEPOINT`: the table of odd multiples `(2 k + 1) • B`
(`k < 64`) of the basepoint; limbs `< 2^54`. -/
@[step]
theorem AFFINE_ODD_MULTIPLES_OF_BASEPOINT_spec :
    AFFINE_ODD_MULTIPLES_OF_BASEPOINT
      ⦃ (r : window.NafLookupTable8 AffineNielsPoint.«x86_64-tables») =>
        r.Represents basepoint ∧ r.Bounded ⦄ := by
  obtain ⟨t, ht, hd⟩ := AFFINE_ODD_MULTIPLES_OF_BASEPOINT_eq
  rw [ht, WP.spec_ok]
  refine ⟨fun k hk => ?_, fun k hk => (hd k hk).2.2.2⟩
  obtain ⟨hx, hy⟩ := Proofs.oddMultiplesCoords_spec k hk
  obtain ⟨ha, hb, hc, -⟩ := hd k hk
  exact AffineNielsPoint.«x86_64-tables».onCurve_toPoint_of_coords hx hy ha hb hc

end Curve25519Dalek.backend.serial.u64.constants
