/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
import all Curve25519.Basic
import Proofs.Helpers.TableCertificate
public section

/-! # `ED25519_BASEPOINT_TABLE`

Row `i` is the lookup table of `2^(8 i) • B`: entry `j` is the affine Niels form of
`(j + 1) • 2^(8 i) • B`. The constant is reduced to its 768 limb arrays
(`Proofs.Helpers.TableCertificate`), and the content is certified by kernel computation. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.curve_models
open Curve25519Dalek.TableCertificate

namespace Curve25519Dalek.backend.serial.u64.constants

set_option maxRecDepth 100000 in
collect_limbs tableLimbs from ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN

/-- The table built from its 768 field elements in source order. -/
@[expose] def mkTable (fes : List FieldElement51) : edwards.EdwardsBasepointTable.«x86_64-tables» :=
  Array.make 32#usize (List.ofFn fun i : Fin 32 => Array.make 8#usize (List.ofFn fun j : Fin 8 =>
    ({ y_plus_x := fes[24 * i.val + 3 * j.val]!, y_minus_x := fes[24 * i.val + 3 * j.val + 1]!,
       xy2d := fes[24 * i.val + 3 * j.val + 2]! } : AffineNielsPoint.«x86_64-tables»))
    (by rw [List.length_ofFn]; rfl)) (by rw [List.length_ofFn]; rfl)

theorem mkTable_get (fes : List FieldElement51) {i j : ℕ} (hi : i < 32) (hj : j < 8) :
    ((mkTable fes)[i]!)[j]! =
      (⟨fes[24 * i + 3 * j]!, fes[24 * i + 3 * j + 1]!, fes[24 * i + 3 * j + 2]!⟩ :
        AffineNielsPoint.«x86_64-tables») := by
  simp only [mkTable, Array.getElem!_Nat_eq, Array.make_val, getElem!_pos, List.length_ofFn, hi, hj,
    List.getElem_ofFn]

set_option maxRecDepth 100000 in
private theorem inner_eq_bindList : ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN =
    bindList tableLimbs (fun fes => ok (mkTable fes)) := by
  kernel_rfl

private theorem inner_eq : ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN = ok (mkTable tableLimbs) := by
  rw [inner_eq_bindList, bindList_eq]

private theorem tableLimbs_length : tableLimbs.length = 24 * 32 := by
  decide +kernel

private theorem table_check : checkTable edwards (basepointExt edwards) tableLimbs 32 = true := by
  rw [edwards_eq_numerals]
  decide +kernel

private theorem table_bounded :
    tableLimbs.all (fun a => a.val.all fun l => decide (l.val < 2 ^ 54)) = true := by
  decide +kernel

/-- `ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN`: the radix-`16` basepoint table of `B` (row `i`
is the lookup table of `2^(8 i) • B`); limbs `< 2^54`. -/
@[step]
theorem ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN_spec :
    ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN
      ⦃ (r : edwards.EdwardsBasepointTable.«x86_64-tables») =>
        r.Represents basepoint ∧ r.Bounded ⦄ := by
  rw [inner_eq, spec_ok]
  constructor
  · intro i hi j hj
    rw [mkTable_get _ hi hj]
    have h := checkTable_sound onCurve_basepointExt table_check tableLimbs_length i hi j hj
    rwa [toPoint_basepointExt] at h
  · intro i hi j hj
    rw [mkTable_get _ hi hj]
    refine ⟨limbs_lt_of_all table_bounded (by rw [tableLimbs_length]; omega),
      limbs_lt_of_all table_bounded (by rw [tableLimbs_length]; omega),
      limbs_lt_of_all table_bounded (by rw [tableLimbs_length]; omega)⟩

/-- `ED25519_BASEPOINT_TABLE`: the radix-`16` basepoint table of `B` (row `i` is the lookup
table of `2^(8 i) • B`); limbs `< 2^54`. -/
@[step]
theorem ED25519_BASEPOINT_TABLE_spec :
    ED25519_BASEPOINT_TABLE ⦃ (r : edwards.EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents basepoint ∧ r.Bounded ⦄ := by
  unfold ED25519_BASEPOINT_TABLE
  exact ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN_spec

end Curve25519Dalek.backend.serial.u64.constants
