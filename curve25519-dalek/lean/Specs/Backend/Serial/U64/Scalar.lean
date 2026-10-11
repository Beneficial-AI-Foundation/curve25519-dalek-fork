/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Specs.Backend.Serial.U64.Scalar.Index
public import Specs.Backend.Serial.U64.Scalar.IndexMut
public import Specs.Backend.Serial.U64.Scalar.M
public import Specs.Backend.Serial.U64.Scalar.Zero
public import Specs.Backend.Serial.U64.Scalar.FromBytes
public import Specs.Backend.Serial.U64.Scalar.FromBytesWide
public import Specs.Backend.Serial.U64.Scalar.ToBytes
public import Specs.Backend.Serial.U64.Scalar.Add
public import Specs.Backend.Serial.U64.Scalar.Sub
public import Specs.Backend.Serial.U64.Scalar.ConditionalAddL
public import Specs.Backend.Serial.U64.Scalar.Shr1Assign
public import Specs.Backend.Serial.U64.Scalar.MulInternal
public import Specs.Backend.Serial.U64.Scalar.SquareInternal
public import Specs.Backend.Serial.U64.Scalar.MontgomeryReduce
public import Specs.Backend.Serial.U64.Scalar.Mul
public import Specs.Backend.Serial.U64.Scalar.Square
public import Specs.Backend.Serial.U64.Scalar.MontgomeryMul
public import Specs.Backend.Serial.U64.Scalar.MontgomerySquare
public import Specs.Backend.Serial.U64.Scalar.AsMontgomery
public import Specs.Backend.Serial.U64.Scalar.FromMontgomery
public import Zeroize
public section

/-! # Specs of `src/backend/serial/u64/scalar.rs`

Audit file: every Rust item of `scalar.rs` with its spec statement, proved by the theorem of the
same name (without the prime) in `Scalar/`, and the axioms that proof depends on. Items appear in
the order of `scalar.rs`.
Definitions used: `Scalar52.asNat` (`Specs/Backend/Serial/U64/Defs.lean`), `Array.asNat`
(`Specs/Defs.lean`; radix `2^8` for bytes, `2^52` for the nine-limb products), `L`
(`Curve25519/Basic.lean`), and the constants `L`, `LFACTOR` of `constants.rs` (specified in
`Constants.lean`). The Montgomery radix is written `montgomeryRadix`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize

/-- `Zeroize::zeroize`: all limbs `0` (proved in `Zeroize/Instances.lean`). -/
theorem zeroize_spec' (self : Scalar52) :
    zeroize self ⦃ (r : Scalar52) =>
      r = Array.repeat 5#usize 0#u64 ⦄ :=
  zeroize_spec self

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  zeroize.Zeroize.Blanket.zeroize_eq] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64

/-- `Index::index`: limb `_index`. -/
theorem index_spec' (self : Scalar52) (_index : Usize) (hindex : _index.val < 5) :
    index self _index ⦃ (r : U64) =>
      r = self[_index.val]! ⦄ :=
  index_spec self _index hindex

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms index_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64

/-- `IndexMut::index_mut`: limb `_index`, and writing back sets that limb. -/
theorem index_mut_spec' (self : Scalar52) (_index : Usize) (hindex : _index.val < 5) :
    index_mut self _index ⦃ (r : U64) (back : U64 → Scalar52) =>
      r = self[_index.val]! ∧ ∀ x, back x = self.set _index x ⦄ :=
  index_mut_spec self _index hindex

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms index_mut_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64

namespace Curve25519Dalek.backend.serial.u64.scalar

/-- `m`: the full 128-bit product. -/
theorem m_spec' (x y : U64) :
    m x y ⦃ (r : U128) =>
      r.val = x.val * y.val ⦄ :=
  m_spec x y

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms m_spec'

end Curve25519Dalek.backend.serial.u64.scalar

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `ZERO`: the scalar `0`. -/
theorem ZERO_spec' :
    Scalar52.asNat ZERO = 0 ∧ ∀ i < 5, ZERO[i]!.val < 2 ^ 52 :=
  ZERO_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ZERO_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `from_bytes`: the 256-bit little-endian value, in 52-bit limbs (not reduced). -/
theorem from_bytes_spec' (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (r : Scalar52) =>
      r.asNat = bytes.asNat 8 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  from_bytes_spec bytes

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_bytes_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `from_bytes_wide`: the 512-bit little-endian value reduced modulo `L`. -/
theorem from_bytes_wide_spec' (bytes : Array U8 64#usize) :
    from_bytes_wide bytes ⦃ (r : Scalar52) =>
      r.asNat = bytes.asNat 8 % L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  from_bytes_wide_spec bytes

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_bytes_wide_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `to_bytes`: the value as 32 little-endian bytes; limbs `< 2^52`, value `< 2^256`. -/
theorem to_bytes_spec' (self : Scalar52) (hself : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (hself' : self.asNat < 2 ^ 256) :
    to_bytes self ⦃ (r : Array U8 32#usize) =>
      r.asNat 8 = self.asNat ⦄ :=
  to_bytes_spec self hself hself'

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_bytes_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `add`: `(a + b) mod L` for canonical `a`, `b`. -/
theorem add_spec' (a b : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) (ha' : a.asNat < L) (hb' : b.asNat < L) :
    add a b ⦃ (r : Scalar52) =>
      r.asNat = (a.asNat + b.asNat) % L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  add_spec a b ha hb ha' hb'

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `sub`: `(a - b) mod L`, canonical, for `a < b + L` and `b ≤ L`. -/
theorem sub_spec' (a b : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) (ha' : a.asNat < b.asNat + L) (hb' : b.asNat ≤ L) :
    sub a b ⦃ (r : Scalar52) =>
      (r.asNat + b.asNat) % L = a.asNat % L ∧ r.asNat < L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  sub_spec a b ha hb ha' hb'

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `conditional_add_l`: for a valid `condition` (`0` or `1`), adds `L` (modulo `2^260`) if
`condition = 1`; the returned carry is not specified. -/
theorem conditional_add_l_spec' (self : Scalar52) (condition : subtle.Choice)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 52) (hcondition : condition.IsValid) :
    conditional_add_l self condition ⦃ (c : U64) (r : Scalar52) =>
      (condition = 0#u8 → r.asNat = self.asNat) ∧
      (condition = 1#u8 → r.asNat = (self.asNat + L) % montgomeryRadix) ∧
      ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  conditional_add_l_spec self condition hself hcondition

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_add_l_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `shr1_assign`: halves the value; `c` is the bit shifted out. -/
theorem shr1_assign_spec' (self : Scalar52) (hself : ∀ i < 5, self[i]!.val < 2 ^ 52) :
    shr1_assign self ⦃ (c : U64) (r : Scalar52) =>
      2 * r.asNat + c.val = self.asNat ∧ c.val < 2 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  shr1_assign_spec self hself

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms shr1_assign_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `mul_internal`: the product `a b` in nine 128-bit radix-`2^52` limbs. -/
theorem mul_internal_spec' (a b : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    mul_internal a b ⦃ (r : Array U128 9#usize) =>
      r.asNat 52 = a.asNat * b.asNat ∧ ∀ i < 9, r[i]!.val < 2 ^ 107 ⦄ :=
  mul_internal_spec a b ha hb

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_internal_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `square_internal`: `a²` in nine 128-bit radix-`2^52` limbs. -/
theorem square_internal_spec' (a : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) :
    square_internal a ⦃ (r : Array U128 9#usize) =>
      r.asNat 52 = a.asNat ^ 2 ∧ ∀ i < 9, r[i]!.val < 2 ^ 107 ⦄ :=
  square_internal_spec a ha

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms square_internal_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `montgomery_reduce`: `limbs / 2^260 mod L`, canonical, for `limbs < 2^260 L`. -/
theorem montgomery_reduce_spec' (limbs : Array U128 9#usize)
    (hlimbs : ∀ i < 9, limbs[i]!.val < 2 ^ 127) (hlimbs' : limbs.asNat 52 < montgomeryRadix * L) :
    montgomery_reduce limbs ⦃ (r : Scalar52) =>
      r.asNat * montgomeryRadix % L = limbs.asNat 52 % L ∧ r.asNat < L ∧
      ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  montgomery_reduce_spec limbs hlimbs hlimbs'

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms montgomery_reduce_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52.montgomery_reduce

/-- `montgomery_reduce::part1`: the Montgomery factor `p` making `sum + p L[0]` divisible by
`2^52`, and the quotient `c`. -/
theorem part1_spec' (sum : U128) (hsum : sum.val + 2 ^ 104 ≤ 2 ^ 128) :
    part1 sum ⦃ (c : U128) (p : U64) =>
      p.val = sum.val * constants.LFACTOR.val % 2 ^ 52 ∧
      c.val * 2 ^ 52 = sum.val + p.val * constants.L[0]!.val ⦄ :=
  part1_spec sum hsum

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms part1_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52.montgomery_reduce

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52.montgomery_reduce

/-- `montgomery_reduce::part2`: splits off the low 52 bits. -/
theorem part2_spec' (sum : U128) :
    part2 sum ⦃ (c : U128) (w : U64) =>
      c.val * 2 ^ 52 + w.val = sum.val ∧ w.val < 2 ^ 52 ⦄ :=
  part2_spec sum

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms part2_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52.montgomery_reduce

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `mul`: `a b mod L`, for `a b < 2^260 L` (e.g. `a, b < 2^256`). -/
theorem mul_spec' (a b : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) (hab : a.asNat * b.asNat < montgomeryRadix * L) :
    mul a b ⦃ (r : Scalar52) =>
      r.asNat = a.asNat * b.asNat % L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  mul_spec a b ha hb hab

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `square`: `self² mod L`, for `self² < 2^260 L`. -/
theorem square_spec' (self : Scalar52) (hself : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (hself' : self.asNat ^ 2 < montgomeryRadix * L) :
    square self ⦃ (r : Scalar52) =>
      r.asNat = self.asNat ^ 2 % L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  square_spec self hself hself'

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms square_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `montgomery_mul`: `a b / 2^260 mod L`, canonical, for `a b < 2^260 L`. -/
theorem montgomery_mul_spec' (a b : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) (hab : a.asNat * b.asNat < montgomeryRadix * L) :
    montgomery_mul a b ⦃ (r : Scalar52) =>
      r.asNat * montgomeryRadix % L = a.asNat * b.asNat % L ∧ r.asNat < L ∧
      ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  montgomery_mul_spec a b ha hb hab

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms montgomery_mul_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `montgomery_square`: `self² / 2^260 mod L`, canonical, for `self² < 2^260 L`. -/
theorem montgomery_square_spec' (self : Scalar52) (hself : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (hself' : self.asNat ^ 2 < montgomeryRadix * L) :
    montgomery_square self ⦃ (r : Scalar52) =>
      r.asNat * montgomeryRadix % L = self.asNat ^ 2 % L ∧ r.asNat < L ∧
      ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  montgomery_square_spec self hself hself'

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms montgomery_square_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `as_montgomery`: `self 2^260 mod L`. -/
theorem as_montgomery_spec' (self : Scalar52) (hself : ∀ i < 5, self[i]!.val < 2 ^ 52) :
    as_montgomery self ⦃ (r : Scalar52) =>
      r.asNat = self.asNat * montgomeryRadix % L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  as_montgomery_spec self hself

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_montgomery_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- `from_montgomery`: `self / 2^260 mod L`, canonical. -/
theorem from_montgomery_spec' (self : Scalar52) (hself : ∀ i < 5, self[i]!.val < 2 ^ 52) :
    from_montgomery self ⦃ (r : Scalar52) =>
      r.asNat * montgomeryRadix % L = self.asNat % L ∧ r.asNat < L ∧
      ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  from_montgomery_spec self hself

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_montgomery_spec'

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
