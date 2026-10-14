/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Field.CtEq
import Proofs.Field.Default
import Proofs.Field.Eq
import Proofs.Field.InternalInvertBatch
import Proofs.Field.Invert
import Proofs.Field.InvertBatch
import Proofs.Field.InvertBatchAlloc
import Proofs.Field.Invsqrt
import Proofs.Field.IsNegative
import Proofs.Field.IsZero
import Proofs.Field.Pow22501
import Proofs.Field.PowP58
import Proofs.Field.SqrtRatioI
public section

/-! # Specs of `src/field.rs`

Audit file: every Rust item of `field.rs` (for the u64 backend, `FieldElement = FieldElement51`)
with its spec statement, proved by the theorem of the same name (without the prime) in `Field/`,
and the axioms that proof depends on. Items appear in the order of `field.rs`.
Definitions used: `FieldElement51.asNat` (`Specs/Backend/Serial/U64/Defs.lean`), `p`, `sqrtM1`
(`Curve25519/Basic.lean`).
Not translated (`digest` feature off): `from_bytes_wide`, `hash_to_field`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreCmpPartialEqFieldElement51

/-- `PartialEq::eq`: equality modulo `p`. -/
theorem eq_spec' (self other : FieldElement51) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔ self.asNat % p = other.asNat % p) ⦄ :=
  eq_spec self other

/-- [propext, Classical.choice, Quot.sound, Bool.Insts.CoreConvertFromChoice.from_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec, U8.Insts.SubtleConstantTimeEq.ct_eq_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec'

end CoreCmpPartialEqFieldElement51
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq::ct_eq`: `1` iff equal modulo `p`. -/
theorem ct_eq_spec' (self other : FieldElement51) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (self.asNat % p = other.asNat % p → c = 1#u8) ∧
      (self.asNat % p ≠ other.asNat % p → c = 0#u8) ⦄ :=
  ct_eq_spec self other

/-- [propext, Classical.choice, Quot.sound, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.CoreDefaultDefault

/-- `Default::default`: the field element `0`. -/
theorem default_spec' :
    default ⦃ (r : FieldElement51) =>
      r.asNat = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  default_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.CoreDefaultDefault

namespace Curve25519Dalek.field.FieldElement51

/-- `is_negative`: the low bit of the canonical value. -/
theorem is_negative_spec' (self : FieldElement51) :
    is_negative self ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ c.val = self.asNat % p % 2 ⦄ :=
  is_negative_spec self

/-- [propext, Classical.choice, Quot.sound, subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_negative_spec'

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement51

/-- `is_zero`: `1` iff `0` modulo `p`. -/
theorem is_zero_spec' (self : FieldElement51) :
    is_zero self ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (self.asNat % p = 0 → c = 1#u8) ∧ (self.asNat % p ≠ 0 → c = 0#u8) ⦄ :=
  is_zero_spec self

/-- [propext, Classical.choice, Quot.sound, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_zero_spec'

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement51

/-- `pow22501`: `(self^(2^250 - 1), self^11)`; limbs `< 2^54` in, `< 2^52` out. -/
theorem pow22501_spec' (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow22501 self ⦃ (t19 t3 : FieldElement51) =>
      t19.asNat % p = self.asNat ^ (2 ^ 250 - 1) % p ∧ t3.asNat % p = self.asNat ^ 11 % p ∧
      (∀ i < 5, t19[i]!.val < 2 ^ 52) ∧ ∀ i < 5, t3[i]!.val < 2 ^ 52 ⦄ :=
  pow22501_spec self hself

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms pow22501_spec'

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement51

/-- `invert_batch`: inverts every nonzero element; zero elements are left unchanged. -/
theorem invert_batch_spec' {N : Usize} (inputs : Array FieldElement51 N)
    (hinputs : ∀ i < N.val, ∀ j < 5, (inputs[i]!)[j]!.val < 2 ^ 54) :
    invert_batch inputs ⦃ (r : Array FieldElement51 N) =>
      ∀ i < N.val,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          ∀ j < 5, (r[i]!)[j]!.val < 2 ^ 52) ⦄ :=
  invert_batch_spec inputs hinputs

/-- [propext, Classical.choice, Quot.sound, Bool.Insts.CoreConvertFromChoice.from_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms invert_batch_spec'

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement51

/-- `invert_batch_alloc`: as `invert_batch`, on a slice. -/
theorem invert_batch_alloc_spec' (inputs : Slice FieldElement51)
    (hinputs : ∀ i < inputs.length, ∀ j < 5, (inputs[i]!)[j]!.val < 2 ^ 54) :
    invert_batch_alloc inputs ⦃ (r : Slice FieldElement51) =>
      r.length = inputs.length ∧
      ∀ i < inputs.length,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          ∀ j < 5, (r[i]!)[j]!.val < 2 ^ 52) ⦄ :=
  invert_batch_alloc_spec inputs hinputs

/-- [propext, Classical.choice, Quot.sound, Bool.Insts.CoreConvertFromChoice.from_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms invert_batch_alloc_spec'

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement51

/-- `internal_invert_batch`: Montgomery's batch inversion; the returned scratch space is not
specified. -/
theorem internal_invert_batch_spec' (inputs scratch : Slice FieldElement51)
    (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, ∀ j < 5, (inputs[i]!)[j]!.val < 2 ^ 54) :
    internal_invert_batch inputs scratch ⦃ (r _scratch : Slice FieldElement51) =>
      r.length = inputs.length ∧
      ∀ i < inputs.length,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          ∀ j < 5, (r[i]!)[j]!.val < 2 ^ 52) ⦄ :=
  internal_invert_batch_spec inputs scratch hlen hinputs

/-- [propext, Classical.choice, Quot.sound, Bool.Insts.CoreConvertFromChoice.from_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms internal_invert_batch_spec'

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement51

/-- `invert`: the inverse modulo `p`, and `0` for `0`. -/
theorem invert_spec' (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    invert self ⦃ (r : FieldElement51) =>
      (self.asNat % p ≠ 0 → r.asNat * self.asNat % p = 1) ∧
      (self.asNat % p = 0 → r.asNat % p = 0) ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  invert_spec self hself

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms invert_spec'

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement51

/-- `pow_p58`: `self^((p - 5) / 8) = self^(2^252 - 3)`. -/
theorem pow_p58_spec' (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow_p58 self ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ (2 ^ 252 - 3) % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  pow_p58_spec self hself

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms pow_p58_spec'

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement51

/-- `sqrt_ratio_i`: the nonnegative (even) `sqrt(u/v)` with `c = 1` if `u/v` is a square,
otherwise `sqrt(sqrtM1 * u/v)` with `c = 0`; `(1, 0)` if `u = 0`, `(0, 0)` if only `v = 0`. -/
theorem sqrt_ratio_i_spec' (u v : FieldElement51) (hu : ∀ i < 5, u[i]!.val < 2 ^ 54)
    (hv : ∀ i < 5, v[i]!.val < 2 ^ 54) :
    sqrt_ratio_i u v ⦃ (c : subtle.Choice) (r : FieldElement51) =>
      c.IsValid ∧ (u.asNat % p = 0 → c = 1#u8 ∧ r.asNat % p = 0) ∧
      (u.asNat % p ≠ 0 → v.asNat % p = 0 → c = 0#u8 ∧ r.asNat % p = 0) ∧
      (v.asNat % p ≠ 0 → (∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) →
        c = 1#u8 ∧ r.asNat ^ 2 * v.asNat % p = u.asNat % p) ∧
      (v.asNat % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) →
        c = 0#u8 ∧ r.asNat ^ 2 * v.asNat % p = sqrtM1 * u.asNat % p) ∧
      r.asNat % p % 2 = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  sqrt_ratio_i_spec u v hu hv

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sqrt_ratio_i_spec'

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement51

/-- `invsqrt`: `sqrt_ratio_i 1 self`, i.e. the nonnegative `1/sqrt(self)` (`c = 1`) or
`sqrt(sqrtM1/self)` (`c = 0`); `(0, 0)` for `0`. -/
theorem invsqrt_spec' (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    invsqrt self ⦃ (c : subtle.Choice) (r : FieldElement51) =>
      c.IsValid ∧ (self.asNat % p = 0 → c = 0#u8 ∧ r.asNat % p = 0) ∧
      (self.asNat % p ≠ 0 → (∃ x : ℕ, x ^ 2 * self.asNat % p = 1) →
        c = 1#u8 ∧ r.asNat ^ 2 * self.asNat % p = 1) ∧
      (self.asNat % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * self.asNat % p = 1) →
        c = 0#u8 ∧ r.asNat ^ 2 * self.asNat % p = sqrtM1) ∧
      r.asNat % p % 2 = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  invsqrt_spec self hself

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms invsqrt_spec'

end Curve25519Dalek.field.FieldElement51
