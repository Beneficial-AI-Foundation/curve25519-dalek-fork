/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Curve25519.Proofs.Edwards.BasepointTable
import Proofs.Helpers.TableConstants
public section

/-! # `ED25519_BASEPOINT_TABLE`

Entry `j` of row `i` is the affine Niels form of `(j + 1) • 2^(8 i) • B`: its limbs' values are
`y + x`, `y - x`, `2 d x y` modulo `p` for the coordinates `(x, y)` certified in
`Curve25519.Proofs.Edwards.BasepointTable`, checked by kernel computation on the numerals. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.u64.constants

/-- The data of entry `j` of row `i` of a table, as numbers: the Niels coordinates of
`basepointTableCoords[8 i + j]` modulo `p`, and limbs `< 2^54`. -/
private def EntryOK (t : edwards.EdwardsBasepointTable.«x86_64-tables») (i j : ℕ) : Prop :=
  (t[i]!)[j]!.y_plus_x.asNat % p = (Proofs.basepointTableCoords[8 * i + j]!.2 +
      Proofs.basepointTableCoords[8 * i + j]!.1) % p ∧
    ((t[i]!)[j]!.y_minus_x.asNat + Proofs.basepointTableCoords[8 * i + j]!.1) % p =
      Proofs.basepointTableCoords[8 * i + j]!.2 % p ∧
    (t[i]!)[j]!.xy2d.asNat % p = 2 * dNat * Proofs.basepointTableCoords[8 * i + j]!.1 *
      Proofs.basepointTableCoords[8 * i + j]!.2 % p ∧
    ((t[i]!)[j]!).Bounded

private theorem ED25519_BASEPOINT_TABLE_eq :
    ∃ t, ED25519_BASEPOINT_TABLE = ok t ∧ ∀ i < 32, ∀ j < 8, EntryOK t i j := by
  unfold ED25519_BASEPOINT_TABLE ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN
  refine ⟨_, rfl, ?_⟩
  unfold EntryOK
  rw [p_eq_numeral]
  simp only [asNat_def, Array.asNat_def, AffineNielsPoint.«x86_64-tables».Bounded]
  decide +kernel

/-- `ED25519_BASEPOINT_TABLE`: the radix-`16` basepoint table of `B` (row `i` is the lookup table
of `2^(8 i) • B`); limbs `< 2^54`. -/
@[step]
theorem ED25519_BASEPOINT_TABLE_spec :
    ED25519_BASEPOINT_TABLE ⦃ (r : edwards.EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents basepoint ∧ r.Bounded ⦄ := by
  obtain ⟨t, ht, hd⟩ := ED25519_BASEPOINT_TABLE_eq
  rw [ht, WP.spec_ok]
  refine ⟨fun i hi j hj => ?_, fun i hi j hj => (hd i hi j hj).2.2.2⟩
  obtain ⟨hx, hy⟩ := Proofs.basepointTableCoords_spec i j hi hj
  obtain ⟨ha, hb, hc, -⟩ := hd i hi j hj
  exact AffineNielsPoint.«x86_64-tables».onCurve_toPoint_of_coords hx hy ha hb hc

end Curve25519Dalek.backend.serial.u64.constants
