/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Specs.Scalar.FromBytesModOrderWide
public import Specs.Scalar.Eq
public import Specs.Scalar.CtEq
public import Specs.Scalar.Index
public import Specs.Scalar.MulAssign
public import Specs.Scalar.Mul
public import Specs.Scalar.Add
public import Specs.Scalar.Sub
public import Specs.Scalar.Neg
public import Specs.Scalar.ConditionalSelect
public import Specs.Scalar.Default
public import Specs.Scalar.FromUnsigned
public import Specs.Scalar.Zero
public import Specs.Scalar.One
public import Specs.Scalar.ToBytes
public import Specs.Scalar.AsBytes
public import Specs.Scalar.Invert
public import Specs.Scalar.InvertBatch
public import Specs.Scalar.InvertBatchAlloc
public import Specs.Scalar.InvertBatchInternal
public import Specs.Scalar.DivBy2
public import Specs.Scalar.NonAdjacentForm
public import Specs.Scalar.AsRadix16
public import Specs.Scalar.ToRadix2wSizeHint
public import Specs.Scalar.AsRadix2w
public import Specs.Scalar.Unpack
public import Specs.Scalar.Reduce
public import Specs.Scalar.Scalar52Pack
public import Specs.Scalar.MontgomeryInvert
public import Specs.Scalar.Scalar52Invert
public import Specs.Scalar.ReadLeU64Into
public import Specs.Scalar.ClampInteger
public import Specs.Scalar.HalfWidthTryFrom
public import Specs.Scalar.HalfWidthZero
public import Specs.Scalar.HalfWidthOne
public import Specs.Scalar.HalfWidthFromBytes
public import Specs.Scalar.HalfWidthAsScalar
public import Specs.Scalar.HalfWidthToBytes
public import Specs.Scalar.HalfWidthNonAdjacentForm
public import Specs.Scalar.SplitAt128
public import Specs.Scalar.FromHalfWidth
public import Specs.Scalar.HalfWidthFromUnsigned
public import Specs.Scalar.HalfWidthZeroize
import Zeroize.Instances
public section

/-! # Specs of `src/scalar.rs`

Audit file: the Rust items of `scalar.rs` with their spec statements, proved by the theorem of the
same name (without the prime) in `Scalar/`, and the axioms that proof depends on. Items appear in
the order of `scalar.rs`. Functions with per-target variants are specified for the two x86_64
variants (u64 backend); the `get_target` dispatchers follow with the u32 backend.
Definitions used: `Scalar.asNat`, `HalfWidthScalar.asNat`, `Array.asNat`, `Array.asInt`
(`Specs/Defs.lean`), `Scalar52.asNat`, `montgomeryRadix` (`Specs/Backend/Serial/U64/Defs.lean`),
`L` (`Curve25519/Basic.lean`).

Not yet specified:
- they call a `get_target` dispatcher (wait for the u32 backend): `from_bytes_mod_order`,
  `from_canonical_bytes`, `is_canonical`, `AddAssign`, `SubAssign`, `Neg for Scalar`, and the
  dispatchers of the per-target functions;
- `Product`, `Sum` (folds over a generic iterator);
- `Scalar29::pack`, `Scalar29::invert`, `Scalar29::montgomery_invert` (u32 backend);
- derived impls of `HalfWidthScalar` (`Clone`, `Default`, `PartialEq`).
Not translated: `from_bits`, `random`, `hash_from_bytes`, `from_hash`, `bits_le`, the `group`
and `serde` impls. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

/-- `from_bytes_mod_order_wide`: the 512-bit little-endian value reduced modulo `L`.
Target `x86_64-tables`. -/
theorem from_bytes_mod_order_wide.«x86_64-tables_spec'» (input : Array U8 64#usize) :
    from_bytes_mod_order_wide.«x86_64-tables» input ⦃ (r : Scalar) =>
      r.asNat = input.asNat 8 % L ⦄ :=
  from_bytes_mod_order_wide.«x86_64-tables_spec» input

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms from_bytes_mod_order_wide.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `from_bytes_mod_order_wide`: the 512-bit little-endian value reduced modulo `L`.
Target `x86_64-no-tables`. -/
theorem from_bytes_mod_order_wide.«x86_64-no-tables_spec'» (input : Array U8 64#usize) :
    from_bytes_mod_order_wide.«x86_64-no-tables» input ⦃ (r : Scalar) =>
      r.asNat = input.asNat 8 % L ⦄ :=
  from_bytes_mod_order_wide.«x86_64-no-tables_spec» input

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms from_bytes_mod_order_wide.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar

/-- `PartialEq::eq`: equality of the byte encodings. -/
theorem eq_spec' (self other : Scalar) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔ self = other) ⦄ :=
  eq_spec self other

/-- [propext, Classical.choice, Quot.sound, Bool.Insts.CoreConvertFromChoice.from_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec, U8.Insts.SubtleConstantTimeEq.ct_eq_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec'

end Curve25519Dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq::ct_eq`: `1` iff the byte encodings are equal. -/
theorem ct_eq_spec' (self other : Scalar) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (self = other → c = 1#u8) ∧ (self ≠ other → c = 0#u8) ⦄ :=
  ct_eq_spec self other

/-- [propext, Classical.choice, Quot.sound, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec'

end Curve25519Dalek.scalar.Scalar.Insts.SubtleConstantTimeEq

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8

/-- `Index::index`: byte `_index`. -/
theorem index_spec' (self : Scalar) (_index : Usize) (hindex : _index.val < 32) :
    index self _index ⦃ (r : U8) =>
      r = self.bytes[_index.val]! ⦄ :=
  index_spec self _index hindex

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms index_spec'

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8

namespace Curve25519Dalek.scalar.MulAssignScalarSharedAScalar

/-- `MulAssign::mul_assign`: the product modulo `L`.
Target `x86_64-tables`. -/
theorem mul_assign.«x86_64-tables_spec'» (self _rhs : Scalar) :
    mul_assign.«x86_64-tables» self _rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * _rhs.asNat % L ⦄ :=
  mul_assign.«x86_64-tables_spec» self _rhs

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.MulAssignScalarSharedAScalar

namespace Curve25519Dalek.scalar.MulAssignScalarSharedAScalar

/-- `MulAssign::mul_assign`: the product modulo `L`.
Target `x86_64-no-tables`. -/
theorem mul_assign.«x86_64-no-tables_spec'» (self _rhs : Scalar) :
    mul_assign.«x86_64-no-tables» self _rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * _rhs.asNat % L ⦄ :=
  mul_assign.«x86_64-no-tables_spec» self _rhs

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms mul_assign.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.MulAssignScalarSharedAScalar

namespace Curve25519Dalek.scalar.MulShared0ScalarSharedAScalarScalar

/-- `Mul::mul`: the product modulo `L`.
Target `x86_64-tables`. -/
theorem mul.«x86_64-tables_spec'» (self _rhs : Scalar) :
    mul.«x86_64-tables» self _rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * _rhs.asNat % L ⦄ :=
  mul.«x86_64-tables_spec» self _rhs

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.MulShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.MulShared0ScalarSharedAScalarScalar

/-- `Mul::mul`: the product modulo `L`.
Target `x86_64-no-tables`. -/
theorem mul.«x86_64-no-tables_spec'» (self _rhs : Scalar) :
    mul.«x86_64-no-tables» self _rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * _rhs.asNat % L ⦄ :=
  mul.«x86_64-no-tables_spec» self _rhs

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.MulShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar

/-- `Add::add`: the sum modulo `L`, for reduced inputs.
Target `x86_64-tables`. -/
theorem add.«x86_64-tables_spec'» (self _rhs : Scalar) (hself : self.asNat < L)
    (hrhs : _rhs.asNat < L) :
    add.«x86_64-tables» self _rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + _rhs.asNat) % L ⦄ :=
  add.«x86_64-tables_spec» self _rhs hself hrhs

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar

/-- `Add::add`: the sum modulo `L`, for reduced inputs.
Target `x86_64-no-tables`. -/
theorem add.«x86_64-no-tables_spec'» (self _rhs : Scalar) (hself : self.asNat < L)
    (hrhs : _rhs.asNat < L) :
    add.«x86_64-no-tables» self _rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + _rhs.asNat) % L ⦄ :=
  add.«x86_64-no-tables_spec» self _rhs hself hrhs

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar

/-- `Sub::sub`: the difference modulo `L`, reduced, for reduced inputs.
Target `x86_64-tables`. -/
theorem sub.«x86_64-tables_spec'» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    sub.«x86_64-tables» self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat % L ∧ r.asNat < L ⦄ :=
  sub.«x86_64-tables_spec» self rhs hself hrhs

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar

/-- `Sub::sub`: the difference modulo `L`, reduced, for reduced inputs.
Target `x86_64-no-tables`. -/
theorem sub.«x86_64-no-tables_spec'» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    sub.«x86_64-no-tables» self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat % L ∧ r.asNat < L ⦄ :=
  sub.«x86_64-no-tables_spec» self rhs hself hrhs

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.NegShared0ScalarScalar

/-- `Neg::neg` (for `&Scalar`): the negation modulo `L`, reduced.
Target `x86_64-tables`. -/
theorem neg.«x86_64-tables_spec'» (self : Scalar) :
    neg.«x86_64-tables» self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄ :=
  neg.«x86_64-tables_spec» self

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.NegShared0ScalarScalar

namespace Curve25519Dalek.scalar.NegShared0ScalarScalar

/-- `Neg::neg` (for `&Scalar`): the negation modulo `L`, reduced.
Target `x86_64-no-tables`. -/
theorem neg.«x86_64-no-tables_spec'» (self : Scalar) :
    neg.«x86_64-no-tables» self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄ :=
  neg.«x86_64-no-tables_spec» self

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.NegShared0ScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.SubtleConditionallySelectable

/-- `conditional_select`: `a` if `choice = 0`, `b` if `choice = 1`, for a valid `choice`. -/
theorem conditional_select_spec' (a b : Scalar) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : Scalar) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  conditional_select_spec a b choice hchoice

/-- [propext, Classical.choice, Quot.sound,
  U8.Insts.SubtleConditionallySelectable.conditional_select_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec'

end Curve25519Dalek.scalar.Scalar.Insts.SubtleConditionallySelectable

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreDefaultDefault

/-- `Default::default`: the scalar `0`. -/
theorem default_spec' :
    default ⦃ (r : Scalar) =>
      r.asNat = 0 ⦄ :=
  default_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec'

end Curve25519Dalek.scalar.Scalar.Insts.CoreDefaultDefault

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU8

/-- `From<u8>`: the value of `x`. -/
theorem from_spec' (x : U8) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU8

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU16

/-- `From<u16>`: the value of `x`. -/
theorem from_spec' (x : U16) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU16

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU32

/-- `From<u32>`: the value of `x`. -/
theorem from_spec' (x : U32) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU32

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU64

/-- `From<u64>`: the value of `x`. -/
theorem from_spec' (x : U64) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU64

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU128

/-- `From<u128>`: the value of `x`. -/
theorem from_spec' (x : U128) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU128

namespace Curve25519Dalek.scalar.Scalar.Insts.ZeroizeZeroize

/-- `Zeroize::zeroize`: all bytes `0` (proved in `Zeroize/Instances.lean`). -/
theorem zeroize_spec' (self : Scalar) :
    zeroize self ⦃ (r : Scalar) =>
      r = { bytes := Array.repeat 32#usize 0#u8 } ⦄ :=
  zeroize_spec self

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  zeroize.Zeroize.Blanket.zeroize_eq] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec'

end Curve25519Dalek.scalar.Scalar.Insts.ZeroizeZeroize

namespace Curve25519Dalek.scalar.Scalar

/-- `ZERO`: the scalar `0`. -/
theorem ZERO_spec' :
    Scalar.asNat ZERO = 0 :=
  ZERO_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ZERO_spec'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `ONE`: the scalar `1`. -/
theorem ONE_spec' :
    Scalar.asNat ONE = 1 :=
  ONE_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ONE_spec'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `to_bytes`: the byte encoding. -/
theorem to_bytes_spec' (self : Scalar) :
    to_bytes self ⦃ (r : Array U8 32#usize) =>
      r = self.bytes ⦄ :=
  to_bytes_spec self

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_bytes_spec'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `as_bytes`: the byte encoding. -/
theorem as_bytes_spec' (self : Scalar) :
    as_bytes self ⦃ (r : Array U8 32#usize) =>
      r = self.bytes ⦄ :=
  as_bytes_spec self

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_bytes_spec'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert`: the inverse modulo `L` (reduced), and `0` for `0`.
Target `x86_64-tables`. -/
theorem invert.«x86_64-tables_spec'» (self : Scalar) :
    invert.«x86_64-tables» self ⦃ (r : Scalar) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄ :=
  invert.«x86_64-tables_spec» self

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms invert.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert`: the inverse modulo `L` (reduced), and `0` for `0`.
Target `x86_64-no-tables`. -/
theorem invert.«x86_64-no-tables_spec'» (self : Scalar) :
    invert.«x86_64-no-tables» self ⦃ (r : Scalar) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄ :=
  invert.«x86_64-no-tables_spec» self

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms invert.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert_batch`: inverts every (nonzero) input; returns the inverse of their product.
Target `x86_64-tables`. -/
theorem invert_batch.«x86_64-tables_spec'» {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    invert_batch.«x86_64-tables» inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch.«x86_64-tables_spec» inputs hinputs

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, zeroize.Zeroize.Blanket.zeroize_eq,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms invert_batch.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert_batch`: inverts every (nonzero) input; returns the inverse of their product.
Target `x86_64-no-tables`. -/
theorem invert_batch.«x86_64-no-tables_spec'» {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    invert_batch.«x86_64-no-tables» inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch.«x86_64-no-tables_spec» inputs hinputs

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, zeroize.Zeroize.Blanket.zeroize_eq,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms invert_batch.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert_batch_alloc`: as `invert_batch`, on a slice.
Target `x86_64-tables`. -/
theorem invert_batch_alloc.«x86_64-tables_spec'» (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_alloc.«x86_64-tables» inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch_alloc.«x86_64-tables_spec» inputs hinputs

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, zeroize.Zeroize.Blanket.zeroize_eq,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms invert_batch_alloc.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert_batch_alloc`: as `invert_batch`, on a slice.
Target `x86_64-no-tables`. -/
theorem invert_batch_alloc.«x86_64-no-tables_spec'» (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_alloc.«x86_64-no-tables» inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch_alloc.«x86_64-no-tables_spec» inputs hinputs

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, zeroize.Zeroize.Blanket.zeroize_eq,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms invert_batch_alloc.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert_batch_internal`: Montgomery's batch inversion; the scratch space is not specified.
Target `x86_64-tables`. -/
theorem invert_batch_internal.«x86_64-tables_spec'» (inputs : Slice Scalar)
    (scratch : Slice backend.serial.u64.scalar.Scalar52) (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_internal.«x86_64-tables» inputs scratch
      ⦃ (ret : Scalar) (r : Slice Scalar)
      (_scratch : Slice backend.serial.u64.scalar.Scalar52) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch_internal.«x86_64-tables_spec» inputs scratch hlen hinputs

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, zeroize.Zeroize.Blanket.zeroize_eq,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms invert_batch_internal.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert_batch_internal`: Montgomery's batch inversion; the scratch space is not specified.
Target `x86_64-no-tables`. -/
theorem invert_batch_internal.«x86_64-no-tables_spec'» (inputs : Slice Scalar)
    (scratch : Slice backend.serial.u64.scalar.Scalar52) (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_internal.«x86_64-no-tables» inputs scratch
      ⦃ (ret : Scalar) (r : Slice Scalar)
      (_scratch : Slice backend.serial.u64.scalar.Scalar52) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch_internal.«x86_64-no-tables_spec» inputs scratch hlen hinputs

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, zeroize.Zeroize.Blanket.zeroize_eq,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms invert_batch_internal.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `div_by_2`: `b` with `b + b = self` modulo `L`, reduced.
Target `x86_64-tables`. -/
theorem div_by_2.«x86_64-tables_spec'» (self : Scalar) (hself : self.asNat < L) :
    div_by_2.«x86_64-tables» self ⦃ (r : Scalar) =>
      2 * r.asNat % L = self.asNat ∧ r.asNat < L ⦄ :=
  div_by_2.«x86_64-tables_spec» self hself

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms div_by_2.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `div_by_2`: `b` with `b + b = self` modulo `L`, reduced.
Target `x86_64-no-tables`. -/
theorem div_by_2.«x86_64-no-tables_spec'» (self : Scalar) (hself : self.asNat < L) :
    div_by_2.«x86_64-no-tables» self ⦃ (r : Scalar) =>
      2 * r.asNat % L = self.asNat ∧ r.asNat < L ⦄ :=
  div_by_2.«x86_64-no-tables_spec» self hself

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms div_by_2.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `non_adjacent_form`: the width-`w` NAF: odd digits below `2^(w-1)` in absolute value, at most
one nonzero digit in any `w` consecutive ones, for `self < 2^255`. -/
theorem non_adjacent_form_spec' (self : Scalar) (w : Usize) (hw : 2 ≤ w.val ∧ w.val ≤ 8)
    (hself : self.asNat < 2 ^ 255) :
    non_adjacent_form self w ⦃ (r : Array I8 256#usize) =>
      r.asInt 1 = self.asNat ∧
      (∀ i < 256, r[i]!.val ≠ 0 → r[i]!.val % 2 = 1 ∧ 2 * |r[i]!.val| < 2 ^ w.val) ∧
      ∀ i < 256, ∀ j < 256, i < j → j < i + w.val → r[i]!.val ≠ 0 → r[j]!.val = 0 ⦄ :=
  non_adjacent_form_spec self w hw hself

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.fmt.Formatter,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms non_adjacent_form_spec'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar.as_radix_16

/-- `as_radix_16::bot_half`: the low nibble. -/
theorem bot_half_spec' (x : U8) :
    bot_half x ⦃ (r : U8) =>
      r.val = x.val % 16 ⦄ :=
  bot_half_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms bot_half_spec'

end Curve25519Dalek.scalar.Scalar.as_radix_16

namespace Curve25519Dalek.scalar.Scalar.as_radix_16

/-- `as_radix_16::top_half`: the high nibble. -/
theorem top_half_spec' (x : U8) :
    top_half x ⦃ (r : U8) =>
      16 * r.val + x.val % 16 = x.val ⦄ :=
  top_half_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms top_half_spec'

end Curve25519Dalek.scalar.Scalar.as_radix_16

namespace Curve25519Dalek.scalar.Scalar

/-- `as_radix_16`: signed radix-16 digits in `[-8, 8)` (the last in `[-8, 8]`), for
`self < 2^255`. -/
theorem as_radix_16_spec' (self : Scalar) (hself : self.bytes[31]!.val ≤ 127) :
    as_radix_16 self ⦃ (r : Array I8 64#usize) =>
      r.asInt 4 = self.asNat ∧
      (∀ i < 63, -8 ≤ r[i]!.val ∧ r[i]!.val < 8) ∧ -8 ≤ r[63]!.val ∧ r[63]!.val ≤ 8 ⦄ :=
  as_radix_16_spec self hself

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_radix_16_spec'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `to_radix_2w_size_hint`: `⌈256 / w⌉` digits, plus one for `w = 8`. -/
theorem to_radix_2w_size_hint_spec' (w : Usize) (hw : 4 ≤ w.val ∧ w.val ≤ 8) :
    to_radix_2w_size_hint w ⦃ (r : Usize) =>
      (w.val = 4 → r.val = 64) ∧ (w.val = 5 → r.val = 52) ∧ (w.val = 6 → r.val = 43) ∧
      (w.val = 7 → r.val = 37) ∧ (w.val = 8 → r.val = 33) ⦄ :=
  to_radix_2w_size_hint_spec w hw

/-- [propext, Classical.choice, Quot.sound, core.num.Usize.div_ceil_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_radix_2w_size_hint_spec'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `as_radix_2w`: signed radix-`2^w` digits in `[-2^(w-1), 2^(w-1))` (the last in
`[-2^(w-1), 2^(w-1)]`), the unused ones `0`, for `self < 2^255`. -/
theorem as_radix_2w_spec' (self : Scalar) (w : Usize) (hw : 4 ≤ w.val ∧ w.val ≤ 8)
    (hself : self.asNat < 2 ^ 255) :
    as_radix_2w self w ⦃ (r : Array I8 64#usize) =>
      r.asInt w.val = self.asNat ∧
      (∀ i < 64, (i + 1) * w.val < 256 → -2 ^ w.val ≤ 2 * r[i]!.val ∧ 2 * r[i]!.val < 2 ^ w.val) ∧
      (∀ i < 64, -2 ^ w.val ≤ 2 * r[i]!.val ∧ 2 * r[i]!.val ≤ 2 ^ w.val) ∧
      ∀ i < 64, 256 < i * w.val → r[i]!.val = 0 ⦄ :=
  as_radix_2w_spec self w hw hself

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.num.Usize.div_ceil_spec, core.fmt.Formatter,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_radix_2w_spec'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `unpack`: the same value in 52-bit limbs.
Target `x86_64-tables`. -/
theorem unpack.«x86_64-tables_spec'» (self : Scalar) :
    unpack.«x86_64-tables» self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat = self.asNat ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  unpack.«x86_64-tables_spec» self

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms unpack.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `unpack`: the same value in 52-bit limbs.
Target `x86_64-no-tables`. -/
theorem unpack.«x86_64-no-tables_spec'» (self : Scalar) :
    unpack.«x86_64-no-tables» self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat = self.asNat ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  unpack.«x86_64-no-tables_spec» self

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms unpack.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `reduce`: the value modulo `L`.
Target `x86_64-tables`. -/
theorem reduce.«x86_64-tables_spec'» (self : Scalar) :
    reduce.«x86_64-tables» self ⦃ (r : Scalar) =>
      r.asNat = self.asNat % L ⦄ :=
  reduce.«x86_64-tables_spec» self

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms reduce.«x86_64-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `reduce`: the value modulo `L`.
Target `x86_64-no-tables`. -/
theorem reduce.«x86_64-no-tables_spec'» (self : Scalar) :
    reduce.«x86_64-no-tables» self ⦃ (r : Scalar) =>
      r.asNat = self.asNat % L ⦄ :=
  reduce.«x86_64-no-tables_spec» self

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms reduce.«x86_64-no-tables_spec'»

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar52

/-- `UnpackedScalar::pack`: the same value as 32 bytes. -/
theorem pack_spec' (self : backend.serial.u64.scalar.Scalar52)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 52) (hself' : self.asNat < 2 ^ 256) :
    pack self ⦃ (r : Scalar) =>
      r.asNat = self.asNat ⦄ :=
  pack_spec self hself hself'

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms pack_spec'

end Curve25519Dalek.scalar.Scalar52

namespace Curve25519Dalek.scalar.Scalar52.montgomery_invert

/-- `montgomery_invert::square_multiply`: `y^(2^squarings) x` in Montgomery form. -/
theorem square_multiply_spec' (y : backend.serial.u64.scalar.Scalar52)
    (squarings : Usize) (x : backend.serial.u64.scalar.Scalar52) (hy : ∀ i < 5, y[i]!.val < 2 ^ 52)
    (hy' : y.asNat < L) (hx : ∀ i < 5, x[i]!.val < 2 ^ 52) (hx' : x.asNat < L) :
    square_multiply y squarings x ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat * montgomeryRadix ^ 2 ^ squarings.val % L =
        y.asNat ^ 2 ^ squarings.val * x.asNat % L ∧
      r.asNat < L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  square_multiply_spec y squarings x hy hy' hx hx'

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms square_multiply_spec'

end Curve25519Dalek.scalar.Scalar52.montgomery_invert

namespace Curve25519Dalek.scalar.Scalar52

/-- `UnpackedScalar::montgomery_invert`: the inverse in Montgomery form (`a R ↦ a⁻¹ R`). -/
theorem montgomery_invert_spec' (self : backend.serial.u64.scalar.Scalar52)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 52) (hself' : self.asNat < L) :
    montgomery_invert self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = montgomeryRadix ^ 2 % L) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  montgomery_invert_spec self hself hself'

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms montgomery_invert_spec'

end Curve25519Dalek.scalar.Scalar52

namespace Curve25519Dalek.scalar.Scalar52

/-- `UnpackedScalar::invert`: the inverse modulo `L` (reduced), and `0` for `0`. -/
theorem invert_spec' (self : backend.serial.u64.scalar.Scalar52)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 52) :
    invert self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  invert_spec self hself

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms invert_spec'

end Curve25519Dalek.scalar.Scalar52

namespace Curve25519Dalek.scalar

/-- `read_le_u64_into`: each word is read from 8 little-endian bytes. -/
theorem read_le_u64_into_spec' (src : Slice U8) (dst : Slice U64)
    (hsrc : src.length = 8 * dst.length) :
    read_le_u64_into src dst ⦃ (r : Slice U64) =>
      r.length = dst.length ∧
      ∀ i < dst.length, ∀ j < 8, r[i]!.val / 2 ^ (8 * j) % 2 ^ 8 = src[8 * i + j]!.val ⦄ :=
  read_le_u64_into_spec src dst hsrc

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.fmt.Formatter,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms read_le_u64_into_spec'

end Curve25519Dalek.scalar

namespace Curve25519Dalek.scalar

/-- `clamp_integer`: clears the low 3 bits and bit 255, sets bit 254. -/
theorem clamp_integer_spec' (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ (r : Array U8 32#usize) =>
      r.asNat 8 + bytes.asNat 8 % 8 = 2 ^ 254 + bytes.asNat 8 % 2 ^ 254 ⦄ :=
  clamp_integer_spec bytes

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms clamp_integer_spec'

end Curve25519Dalek.scalar

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple

/-- `TryFrom<Scalar> for HalfWidthScalar`: succeeds iff the value is below `2^128`. -/
theorem try_from_spec' (value : Scalar) :
    try_from value ⦃ (r : core.result.Result HalfWidthScalar Unit) =>
      (value.asNat < 2 ^ 128 → r = .Ok value) ∧ (2 ^ 128 ≤ value.asNat → r = .Err ()) ⦄ :=
  try_from_spec value

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms try_from_spec'

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::ZERO`: `0`. -/
theorem ZERO_spec' :
    HalfWidthScalar.asNat ZERO = 0 :=
  ZERO_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ZERO_spec'

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::ONE`: `1`. -/
theorem ONE_spec' :
    HalfWidthScalar.asNat ONE = 1 :=
  ONE_spec

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ONE_spec'

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::from_bytes`: the 128-bit little-endian value. -/
theorem from_bytes_spec' (bytes : Array U8 16#usize) :
    from_bytes bytes ⦃ (r : HalfWidthScalar) =>
      r.asNat = bytes.asNat 8 ⦄ :=
  from_bytes_spec bytes

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_bytes_spec'

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::as_scalar`: the same value. -/
theorem as_scalar_spec' (self : HalfWidthScalar) :
    as_scalar self ⦃ (r : Scalar) =>
      r.asNat = self.asNat ⦄ :=
  as_scalar_spec self

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_scalar_spec'

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::to_bytes`: the low 16 bytes. -/
theorem to_bytes_spec' (self : HalfWidthScalar) :
    to_bytes self ⦃ (r : Array U8 16#usize) =>
      r.asNat 8 = self.asNat % 2 ^ 128 ⦄ :=
  to_bytes_spec self

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_bytes_spec'

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::non_adjacent_form`: as `Scalar::non_adjacent_form`. -/
theorem non_adjacent_form_spec' (self : HalfWidthScalar) (w : Usize)
    (hw : 2 ≤ w.val ∧ w.val ≤ 8) (hself : self.asNat < 2 ^ 255) :
    non_adjacent_form self w ⦃ (r : Array I8 256#usize) =>
      r.asInt 1 = self.asNat ∧
      (∀ i < 256, r[i]!.val ≠ 0 → r[i]!.val % 2 = 1 ∧ 2 * |r[i]!.val| < 2 ^ w.val) ∧
      ∀ i < 256, ∀ j < 256, i < j → j < i + w.val → r[i]!.val ≠ 0 → r[j]!.val = 0 ⦄ :=
  non_adjacent_form_spec self w hw hself

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.fmt.Formatter,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms non_adjacent_form_spec'

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.Scalar

/-- `split_at_128`: `self = lo + 2^128 hi` with both halves below `2^128`. -/
theorem split_at_128_spec' (self : Scalar) :
    split_at_128 self ⦃ (lo hi : HalfWidthScalar) =>
      lo.asNat + 2 ^ 128 * hi.asNat = self.asNat ∧ lo.asNat < 2 ^ 128 ∧ hi.asNat < 2 ^ 128 ⦄ :=
  split_at_128_spec self

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms split_at_128_spec'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromHalfWidthScalar

/-- `From<HalfWidthScalar> for Scalar`: the same value. -/
theorem from_spec' (x : HalfWidthScalar) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.asNat ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromHalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU8

/-- `From<u8> for HalfWidthScalar`. -/
theorem from_spec' (x : U8) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU8

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU16

/-- `From<u16> for HalfWidthScalar`. -/
theorem from_spec' (x : U16) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU16

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU32

/-- `From<u32> for HalfWidthScalar`. -/
theorem from_spec' (x : U32) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU32

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU64

/-- `From<u64> for HalfWidthScalar`. -/
theorem from_spec' (x : U64) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU64

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU128

/-- `From<u128> for HalfWidthScalar`. -/
theorem from_spec' (x : U128) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ :=
  from_spec x

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec'

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU128

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.ZeroizeZeroize

/-- `Zeroize::zeroize` for `HalfWidthScalar`: `0`. -/
theorem zeroize_spec' (self : HalfWidthScalar) :
    zeroize self ⦃ (r : HalfWidthScalar) =>
      r.asNat = 0 ⦄ :=
  zeroize_spec self

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  zeroize.Zeroize.Blanket.zeroize_eq] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec'

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.ZeroizeZeroize
