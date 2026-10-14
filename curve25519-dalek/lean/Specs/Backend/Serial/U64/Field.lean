/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.AddAssign
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U64.Field.ConditionalSelect
import Proofs.Backend.Serial.U64.Field.ConditionalSwap
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Backend.Serial.U64.Field.FromLimbs
import Proofs.Backend.Serial.U64.Field.MinusOne
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.MulAssign
import Proofs.Backend.Serial.U64.Field.Neg
import Proofs.Backend.Serial.U64.Field.Negate
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Backend.Serial.U64.Field.Pow2k
import Proofs.Backend.Serial.U64.Field.Reduce
import Proofs.Backend.Serial.U64.Field.SixteenP
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Square2
import Proofs.Backend.Serial.U64.Field.SquareLimbs
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Backend.Serial.U64.Field.SubAssign
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Backend.Serial.U64.Field.Zero
import Zeroize.Instances
public section

/-! # Specs of `src/backend/serial/u64/field.rs`

Spec summary: every Rust item of `field.rs` with its spec statement, proved by the theorem of the
same name (without the prime) in `Proofs/Backend/Serial/U64/Field/`, and the axioms that proof
depends on. Items appear in the order of `field.rs`.
Definitions used: `FieldElement51.asNat` (`Defs/FieldElement51.lean`), `Array.asNat`
(`Defs/Array.lean`; radix `2^8` for bytes), `p` (`Curve25519/Basic.lean`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field

/-- `SIXTEEN_P`: the limbs of `16 p`, each in `[2^55 - 304, 2^55)`. -/
theorem SIXTEEN_P_spec' :
    FieldElement51.asNat SIXTEEN_P = 16 * p ∧
      (∀ i < 5, 2 ^ 55 ≤ SIXTEEN_P[i]!.val + 304) ∧ ∀ i < 5, SIXTEEN_P[i]!.val < 2 ^ 55 :=
  SIXTEEN_P_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms SIXTEEN_P_spec'

end Curve25519Dalek.backend.serial.u64.field

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.ZeroizeZeroize

/-- `Zeroize::zeroize`: all limbs `0` (proved in `Zeroize/Instances.lean`). -/
theorem zeroize_spec' (self : FieldElement51) :
    zeroize self ⦃ (r : FieldElement51) =>
      r = Array.repeat 5#usize 0#u64 ⦄ :=
  zeroize_spec self

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  zeroize.Zeroize.Blanket.zeroize_eq] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.ZeroizeZeroize

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreOpsArithAddAssignSharedAFieldElement51

/-- `AddAssign::add_assign`: limb-wise sum, for limbs `< 2^54`. -/
theorem add_assign_spec' (self _rhs : FieldElement51)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    add_assign self _rhs ⦃ (r : FieldElement51) =>
      ∀ i < 5, r[i]!.val = self[i]!.val + _rhs[i]!.val ⦄ :=
  add_assign_spec self _rhs hself hrhs

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec'

end CoreOpsArithAddAssignSharedAFieldElement51
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts

namespace Curve25519Dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithAddSharedAFieldElement51FieldElement51

/-- `Add::add`: limb-wise sum, for limbs `< 2^54`. -/
theorem add_spec' (self _rhs : FieldElement51)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    add self _rhs ⦃ (r : FieldElement51) =>
      ∀ i < 5, r[i]!.val = self[i]!.val + _rhs[i]!.val ⦄ :=
  add_spec self _rhs hself hrhs

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec'

end Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreOpsArithSubAssignSharedAFieldElement51

/-- `SubAssign::sub_assign`: `r = self - _rhs` mod `p`; limbs `< 2^54` in, `< 2^52` out. -/
theorem sub_assign_spec' (self _rhs : FieldElement51)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    sub_assign self _rhs ⦃ (r : FieldElement51) =>
      (r.asNat + _rhs.asNat) % p = self.asNat % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  sub_assign_spec self _rhs hself hrhs

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec'

end CoreOpsArithSubAssignSharedAFieldElement51
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts

namespace Curve25519Dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithSubSharedAFieldElement51FieldElement51

/-- `Sub::sub`: `r = self - _rhs` mod `p`; limbs `< 2^54` in, `< 2^52` out. -/
theorem sub_spec' (self _rhs : FieldElement51)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    sub self _rhs ⦃ (r : FieldElement51) =>
      (r.asNat + _rhs.asNat) % p = self.asNat % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  sub_spec self _rhs hself hrhs

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec'

end Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreOpsArithMulAssignSharedAFieldElement51

/-- `MulAssign::mul_assign`: `r = self * _rhs` mod `p`; limbs `< 2^54` in, `< 2^52` out. -/
theorem mul_assign_spec' (self _rhs : FieldElement51)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    mul_assign self _rhs ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat * _rhs.asNat % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  mul_assign_spec self _rhs hself hrhs

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec'

end CoreOpsArithMulAssignSharedAFieldElement51
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts

namespace Curve25519Dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithMulSharedAFieldElement51FieldElement51

/-- `Mul::mul`: `r = self * _rhs` mod `p`; limbs `< 2^54` in, `< 2^52` out. -/
theorem mul_spec' (self _rhs : FieldElement51)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    mul self _rhs ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat * _rhs.asNat % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  mul_spec self _rhs hself hrhs

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec'

end Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field
namespace MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul

/-- `Mul::mul::m`: the full 128-bit product. -/
theorem m_spec' (x y : U64) :
    m x y ⦃ (r : U128) =>
      r.val = x.val * y.val ⦄ :=
  m_spec x y

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms m_spec'

end MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
end Curve25519Dalek.backend.serial.u64.field

namespace Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51

/-- `Neg::neg`: `r = -self` mod `p`; limbs `< 2^54` in, `< 2^52` out. -/
theorem neg_spec' (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    neg self ⦃ (r : FieldElement51) =>
      (r.asNat + self.asNat) % p = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  neg_spec self hself

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec'

end Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable

/-- `conditional_select`: `a` if `choice = 0`, `b` if `choice = 1`. -/
theorem conditional_select_spec' (a b : FieldElement51) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : FieldElement51) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  conditional_select_spec a b choice hchoice

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable

/-- `conditional_swap`: unchanged if `choice = 0`, swapped if `choice = 1`. -/
theorem conditional_swap_spec' (a b : FieldElement51) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_swap a b choice ⦃ (a' : FieldElement51) (b' : FieldElement51) =>
      (choice = 0#u8 → a' = a ∧ b' = b) ∧ (choice = 1#u8 → a' = b ∧ b' = a) ⦄ :=
  conditional_swap_spec a b choice hchoice

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_swap_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_swap_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable

/-- `conditional_assign`: `self` if `choice = 0`, `other` if `choice = 1`. -/
theorem conditional_assign_spec' (self other : FieldElement51) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_assign self other choice ⦃ (r : FieldElement51) =>
      (choice = 0#u8 → r = self) ∧ (choice = 1#u8 → r = other) ⦄ :=
  conditional_assign_spec self other choice hchoice

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_assign_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `from_limbs`: wraps the limbs unchanged. -/
theorem from_limbs_spec' (limbs : Array U64 5#usize) :
    from_limbs limbs ⦃ (r : FieldElement51) =>
      r = limbs ⦄ :=
  from_limbs_spec limbs

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_limbs_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ZERO`: the field element `0`. -/
theorem ZERO_spec' :
    ZERO ⦃ (r : FieldElement51) =>
      r.asNat = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  ZERO_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ZERO_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ONE`: the field element `1`. -/
theorem ONE_spec' :
    ONE ⦃ (r : FieldElement51) =>
      r.asNat = 1 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  ONE_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ONE_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `MINUS_ONE`: the field element `-1`, i.e. `p - 1`. -/
theorem MINUS_ONE_spec' :
    MINUS_ONE ⦃ (r : FieldElement51) =>
      r.asNat + 1 = p ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  MINUS_ONE_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms MINUS_ONE_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `negate`: `r = -self` mod `p`; limbs `< 2^54` in, `< 2^52` out. -/
theorem negate_spec' (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    negate self ⦃ (r : FieldElement51) =>
      (r.asNat + self.asNat) % p = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  negate_spec self hself

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms negate_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `reduce`: same value mod `p`, limbs `< 2^52`, value `< 2 p`. -/
theorem reduce_spec' (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (r : FieldElement51) =>
      r.asNat % p = FieldElement51.asNat limbs % p ∧ (∀ i < 5, r[i]!.val < 2 ^ 52) ∧
      r.asNat < 2 * p ⦄ :=
  reduce_spec limbs

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms reduce_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `from_bytes`: the low 255 bits of the little-endian bytes; limbs `< 2^51`. -/
theorem from_bytes_spec' (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (r : FieldElement51) =>
      r.asNat = bytes.asNat 8 % 2 ^ 255 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  from_bytes_spec bytes

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_bytes_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.from_bytes

/-- `from_bytes::load8_at`: the 8 bytes from `i`, little-endian. -/
theorem load8_at_spec' (input : Slice U8) (i : Usize) (hi : i.val + 8 ≤ input.length) :
    load8_at input i ⦃ (r : U64) =>
      r.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * input[i.val + j]!.val ⦄ :=
  load8_at_spec input i hi

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms load8_at_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51.from_bytes

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `to_bytes`: the canonical little-endian encoding of `self mod p`. -/
theorem to_bytes_spec' (self : FieldElement51) :
    to_bytes self ⦃ (r : Array U8 32#usize) =>
      r.asNat 8 = self.asNat % p ⦄ :=
  to_bytes_spec self

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_bytes_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `pow2k`: `r = self^(2^k)` mod `p` (`k > 0`); limbs `< 2^54` in, `< 2^52` out. -/
theorem pow2k_spec' (self : FieldElement51) (k : U32) (hk : 0 < k.val)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow2k self k ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ 2 ^ k.val % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  pow2k_spec self k hk hself

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms pow2k_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `square`: `r = self²` mod `p`; limbs `< 2^54` in, `< 2^52` out. -/
theorem square_spec' (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    square self ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ 2 % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  square_spec self hself

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms square_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `square2`: `r = 2 self²` mod `p`; limbs `< 2^54` in, `< 2^53` out. -/
theorem square2_spec' (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    square2 self ⦃ (r : FieldElement51) =>
      r.asNat % p = 2 * self.asNat ^ 2 % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 53 ⦄ :=
  square2_spec self hself

/-- [propext, Classical.choice, Quot.sound,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms square2_spec'

end Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.field

/-- `square_limbs`: `r = a²` mod `p`; limbs `< 2^54` in, `< 2^52` out. -/
theorem square_limbs_spec' (a : Array U64 5#usize) (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    square_limbs a ⦃ (r : Array U64 5#usize) =>
      FieldElement51.asNat r % p = FieldElement51.asNat a ^ 2 % p ∧
      ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  square_limbs_spec a ha

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms square_limbs_spec'

end Curve25519Dalek.backend.serial.u64.field

namespace Curve25519Dalek.backend.serial.u64.field.square_limbs

/-- `square_limbs::m`: the full 128-bit product. -/
theorem m_spec' (x y : U64) :
    m x y ⦃ (r : U128) =>
      r.val = x.val * y.val ⦄ :=
  m_spec x y

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms m_spec'

end Curve25519Dalek.backend.serial.u64.field.square_limbs
