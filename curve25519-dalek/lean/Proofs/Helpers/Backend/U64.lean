/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
public import Proofs.Helpers.Backend
import Proofs.Backend.Serial.U64.Constants.EdwardsD
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Neg
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Square2
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Field.Eq
import Proofs.Helpers.ToField
public section

/-! # The `u64` field backend

`FieldElement51`, the backend of `«x86_64-tables»` and `«x86_64-no-tables»`, as a `Backend`:
`Red`, `Sum2`, `MulIn`, `Niels` are `LimbsLt 52`, `53`, `54`, `54`. The specs are stated first
on `FieldElement51` (their proofs use the field specs, imported privately), then bundled.
`Backend.U64.mul_spec : Backend.U64.MulSpec`, … by definition. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.Shared0FieldElement51.Insts

namespace Curve25519Dalek.Backend.U64

theorem add_spec (a b : FieldElement51) (ha : a.LimbsLt 52) (hb : b.LimbsLt 52) :
    CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b ⦃ r =>
      r.toField = a.toField + b.toField ∧ r.LimbsLt 53 ⦄ :=
  spec_mono (CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec a b
    (limbs_lt_of_le (by decide) ha) (limbs_lt_of_le (by decide) hb))
    fun _ h => ⟨toField_add_of_limbs h, limbs_add_lt h ha hb⟩

theorem add_sum2_spec (a b : FieldElement51) (ha : a.LimbsLt 53) (hb : b.LimbsLt 52) :
    CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b ⦃ r =>
      r.toField = a.toField + b.toField ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec a b
    (limbs_lt_of_le (by decide) ha) (limbs_lt_of_le (by decide) hb))
    fun _ h => ⟨toField_add_of_limbs h, limbs_add_lt h ha (limbs_lt_of_le (by decide) hb)⟩

theorem sub_spec (a b : FieldElement51) (ha : a.LimbsLt 54) (hb : b.LimbsLt 54) :
    CoreOpsArithSubSharedAFieldElement51FieldElement51.sub a b ⦃ r =>
      r.toField = a.toField - b.toField ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (CoreOpsArithSubSharedAFieldElement51FieldElement51.sub_spec a b ha hb)
    fun _ ⟨h, hr⟩ => ⟨toField_sub_of_mod h, hr⟩

theorem mul_spec (a b : FieldElement51) (ha : a.LimbsLt 54) (hb : b.LimbsLt 54) :
    CoreOpsArithMulSharedAFieldElement51FieldElement51.mul a b ⦃ r =>
      r.toField = a.toField * b.toField ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec a b ha hb)
    fun _ ⟨h, hr⟩ => ⟨toField_mul_of_mod h, hr⟩

theorem square_spec (a : FieldElement51) (ha : a.LimbsLt 53) :
    FieldElement51.square a ⦃ r => r.toField = a.toField ^ 2 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (FieldElement51.square_spec a (limbs_lt_of_le (by decide) ha))
    fun _ ⟨h, hr⟩ => ⟨toField_sq_of_mod h, hr⟩

theorem square2_spec (a : FieldElement51) (ha : a.LimbsLt 53) :
    FieldElement51.square2 a ⦃ r => r.toField = 2 * a.toField ^ 2 ∧ r.LimbsLt 53 ⦄ :=
  spec_mono (FieldElement51.square2_spec a (limbs_lt_of_le (by decide) ha))
    fun _ ⟨h, hr⟩ => ⟨toField_two_mul_sq_of_mod h, hr⟩

theorem neg_spec (a : FieldElement51) (ha : a.LimbsLt 54) :
    CoreOpsArithNegFieldElement51.neg a ⦃ r => r.toField = -a.toField ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (CoreOpsArithNegFieldElement51.neg_spec a ha)
    fun _ ⟨h, hr⟩ => ⟨toField_neg_of_mod h, hr⟩

theorem eq_spec (a b : FieldElement51) :
    FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq a b ⦃ c =>
      (c = true ↔ a.toField = b.toField) ⦄ :=
  spec_mono (FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq_spec a b)
    fun _ h => h.trans toField_eq_toField_iff.symm

theorem edwardsD_spec :
    backend.serial.u64.constants.EDWARDS_D ⦃ (r : FieldElement51) =>
      r.toField = d ∧ r.LimbsLt 52 ⦄ :=
  spec_mono backend.serial.u64.constants.EDWARDS_D_spec
    fun _ ⟨h, hr⟩ => ⟨toField_eq_d_of_asNat h, limbs_lt_of_le (by decide) hr⟩

theorem limbs_lt_mono {a : FieldElement51} {k l : ℕ} (hkl : k ≤ l) (h : a.LimbsLt k) :
    a.LimbsLt l :=
  limbs_lt_of_le hkl h

end Curve25519Dalek.Backend.U64

namespace Curve25519Dalek.Backend

/-- The `u64` backend (`FieldElement51`). -/
@[expose] noncomputable def U64 : Backend where
  F := FieldElement51
  toField := FieldElement51.toField
  Red a := a.LimbsLt 52
  Sum2 a := a.LimbsLt 53
  MulIn a := a.LimbsLt 54
  Niels a := a.LimbsLt 54
  add := CoreOpsArithAddSharedAFieldElement51FieldElement51.add
  sub := CoreOpsArithSubSharedAFieldElement51FieldElement51.sub
  mul := CoreOpsArithMulSharedAFieldElement51FieldElement51.mul
  square := FieldElement51.square
  square2 := FieldElement51.square2
  neg := CoreOpsArithNegFieldElement51.neg
  eq := FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq
  edwardsD := backend.serial.u64.constants.EDWARDS_D
  red_sum2 := U64.limbs_lt_mono (by decide)
  sum2_mulIn := U64.limbs_lt_mono (by decide)
  red_niels := U64.limbs_lt_mono (by decide)
  niels_mulIn h := h

end Curve25519Dalek.Backend
