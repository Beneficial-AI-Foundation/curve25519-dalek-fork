/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Proofs.Helpers.Backend
public import Proofs.Helpers.ToField2625
import Proofs.Backend.Serial.U32.Constants.EdwardsD
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Neg
import Proofs.Backend.Serial.U32.Field.Square
import Proofs.Backend.Serial.U32.Field.Square2
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Field.Eq
public section

/-! # The `u32` field backend

`FieldElement2625`, the backend of `«i686-tables»` and `«i686-no-tables»`, as a `Backend`:
`Red`, `Sum2`, `MulIn`, `Niels` are `LimbsLt 26`, `27`, `MulBounded`, `LimbsLt 27`. The specs
are stated first on `FieldElement2625` (their proofs use the field specs, imported privately),
then bundled.
`Backend.U32.mul_spec : Backend.U32.MulSpec`, … by definition. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open Curve25519Dalek.SharedAFieldElement2625.Insts

namespace Curve25519Dalek.Backend.U32

theorem add_spec (a b : FieldElement2625) (ha : a.LimbsLt 26) (hb : b.LimbsLt 26) :
    CoreOpsArithAddSharedBFieldElement2625FieldElement2625.add a b ⦃ r =>
      r.toField = a.toField + b.toField ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (CoreOpsArithAddSharedBFieldElement2625FieldElement2625.add_spec a b
    (limbs_lt_of_le (by decide) ha) (limbs_lt_of_le (by decide) hb))
    fun _ ⟨h, _⟩ => ⟨toField_add_of_limbs h, limbs_add_lt h ha hb⟩

theorem add_sum2_spec (a b : FieldElement2625) (ha : a.LimbsLt 27) (hb : b.LimbsLt 26) :
    CoreOpsArithAddSharedBFieldElement2625FieldElement2625.add a b ⦃ r =>
      r.toField = a.toField + b.toField ∧ r.MulBounded ⦄ :=
  spec_mono (CoreOpsArithAddSharedBFieldElement2625FieldElement2625.add_spec a b
    (limbs_lt_of_le (by decide) ha) (limbs_lt_of_le (by decide) hb))
    fun _ ⟨h, _⟩ => ⟨toField_add_of_limbs h, mulBounded_add h ha hb⟩

theorem sub_spec (a b : FieldElement2625) (ha : a.MulBounded) (hb : b.MulBounded) :
    CoreOpsArithSubSharedBFieldElement2625FieldElement2625.sub a b ⦃ r =>
      r.toField = a.toField - b.toField ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (CoreOpsArithSubSharedBFieldElement2625FieldElement2625.sub_spec a b
    (limbsLt_of_mulBounded ha) (limbsLt_of_mulBounded hb))
    fun _ ⟨h, hr⟩ => ⟨toField_sub_of_mod h, hr⟩

theorem mul_spec (a b : FieldElement2625) (ha : a.MulBounded) (hb : b.MulBounded) :
    CoreOpsArithMulSharedBFieldElement2625FieldElement2625.mul a b ⦃ r =>
      r.toField = a.toField * b.toField ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (CoreOpsArithMulSharedBFieldElement2625FieldElement2625.mul_spec a b ha hb)
    fun _ ⟨h, hr⟩ => ⟨toField_mul_of_mod h, hr⟩

theorem square_spec (a : FieldElement2625) (ha : a.LimbsLt 27) :
    FieldElement2625.square a ⦃ r => r.toField = a.toField ^ 2 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (FieldElement2625.square_spec a ha)
    fun _ ⟨h, hr⟩ => ⟨toField_sq_of_mod h, hr⟩

theorem square2_spec (a : FieldElement2625) (ha : a.LimbsLt 27) :
    FieldElement2625.square2 a ⦃ r => r.toField = 2 * a.toField ^ 2 ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (FieldElement2625.square2_spec a ha)
    fun _ ⟨h, hr⟩ => ⟨toField_two_mul_sq_of_mod h, limbs_lt_of_le (by decide) hr⟩

theorem neg_spec (a : FieldElement2625) (ha : a.MulBounded) :
    CoreOpsArithNegFieldElement2625.neg a ⦃ r => r.toField = -a.toField ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (CoreOpsArithNegFieldElement2625.neg_spec a (limbsLt_of_mulBounded ha))
    fun _ ⟨h, hr⟩ => ⟨toField_neg_of_mod h, hr⟩

theorem eq_spec (a b : FieldElement2625) :
    FieldElement2625.Insts.CoreCmpPartialEqFieldElement2625.eq a b ⦃ c =>
      (c = true ↔ a.toField = b.toField) ⦄ :=
  spec_mono (FieldElement2625.Insts.CoreCmpPartialEqFieldElement2625.eq_spec a b)
    fun _ h => h.trans toField_eq_toField_iff.symm

theorem edwardsD_spec :
    backend.serial.u32.constants.EDWARDS_D ⦃ (r : FieldElement2625) =>
      r.toField = d ∧ r.LimbsLt 26 ⦄ :=
  spec_mono backend.serial.u32.constants.EDWARDS_D_spec
    fun _ ⟨h, hr⟩ => ⟨toField_eq_d_of_asNat h, hr⟩

theorem red_sum2 {a : FieldElement2625} (h : a.LimbsLt 26) : a.LimbsLt 27 :=
  limbs_lt_of_le (by decide) h

theorem sum2_mulIn {a : FieldElement2625} (h : a.LimbsLt 27) : a.MulBounded :=
  mulBounded_of_limbsLt h

end Curve25519Dalek.Backend.U32

namespace Curve25519Dalek.Backend

/-- The `u32` backend (`FieldElement2625`). -/
@[expose] noncomputable def U32 : Backend where
  F := FieldElement2625
  toField := FieldElement2625.toField
  Red a := a.LimbsLt 26
  Sum2 a := a.LimbsLt 27
  MulIn a := a.MulBounded
  Niels a := a.LimbsLt 27
  add := CoreOpsArithAddSharedBFieldElement2625FieldElement2625.add
  sub := CoreOpsArithSubSharedBFieldElement2625FieldElement2625.sub
  mul := CoreOpsArithMulSharedBFieldElement2625FieldElement2625.mul
  square := FieldElement2625.square
  square2 := FieldElement2625.square2
  neg := CoreOpsArithNegFieldElement2625.neg
  eq := FieldElement2625.Insts.CoreCmpPartialEqFieldElement2625.eq
  edwardsD := backend.serial.u32.constants.EDWARDS_D
  red_sum2 := U32.red_sum2
  sum2_mulIn := U32.sum2_mulIn
  red_niels := U32.red_sum2
  niels_mulIn := U32.sum2_mulIn

end Curve25519Dalek.Backend
