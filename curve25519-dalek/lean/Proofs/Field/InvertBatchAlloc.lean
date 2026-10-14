/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Field.InternalInvertBatch
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.field.FieldElement51

@[step]
theorem invert_batch_alloc_spec (inputs : Slice FieldElement51)
    (hinputs : ∀ i < inputs.length, ∀ j < 5, (inputs[i]!)[j]!.val < 2 ^ 54) :
    invert_batch_alloc inputs ⦃ (r : Slice FieldElement51) =>
      r.length = inputs.length ∧
      ∀ i < inputs.length,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          ∀ j < 5, (r[i]!)[j]!.val < 2 ^ 52) ⦄ := by
  unfold invert_batch_alloc
  step as ⟨one, hone, honeb⟩
  step with alloc.vec.from_elem_spec
    backend.serial.u64.field.FieldElement51.Insts.CoreCloneClone one inputs.len rfl
    as ⟨scratch, hsc, hsclen⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  have hslen : scratch.slice.length = inputs.length := by
    rw [show scratch.slice.length = scratch.length from rfl, hsclen, Slice.len_val]
  step as ⟨r, scratch', hrlen, hr⟩
  exact ⟨hrlen, hr⟩

end Curve25519Dalek.field.FieldElement51
