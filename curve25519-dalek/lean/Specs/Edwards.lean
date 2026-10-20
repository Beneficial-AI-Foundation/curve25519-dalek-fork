/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519.Edwards.Encoding
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
public import Subtle
import Proofs.Edwards.Add
import Proofs.Edwards.AddAssign
import Proofs.Edwards.AsBytes
import Proofs.Edwards.BasepointTableBasepoint
import Proofs.Edwards.BasepointTableCreate
import Proofs.Edwards.BasepointTableFrom
import Proofs.Edwards.BasepointTableMul
import Proofs.Edwards.BasepointTableMulBase
import Proofs.Edwards.Compress
import Proofs.Edwards.CompressBatch
import Proofs.Edwards.CompressBatchAlloc
import Proofs.Edwards.CompressedCtEq
import Proofs.Edwards.CompressedDefault
import Proofs.Edwards.CompressedEq
import Proofs.Edwards.CompressedIdentity
import Proofs.Edwards.CompressedZeroize
import Proofs.Edwards.ConditionalSelect
import Proofs.Edwards.CtEq
import Proofs.Edwards.Decompress
import Proofs.Edwards.Default
import Proofs.Edwards.Eq
import Proofs.Edwards.FromSlice
import Proofs.Edwards.Identity
import Proofs.Edwards.IsSmallOrder
import Proofs.Edwards.IsTorsionFree
import Proofs.Edwards.Mul
import Proofs.Edwards.MulAssign
import Proofs.Edwards.MulBase
import Proofs.Edwards.MulBaseClamped
import Proofs.Edwards.MulByCofactor
import Proofs.Edwards.MulClamped
import Proofs.Edwards.MultiscalarMul
import Proofs.Edwards.Neg
import Proofs.Edwards.OptionalMultiscalarMul
import Proofs.Edwards.Sub
import Proofs.Edwards.SubAssign
import Proofs.Edwards.Sum
import Proofs.Edwards.ToBytes
import Proofs.Edwards.ToMontgomery
import Proofs.Edwards.ToMontgomeryBatch
import Proofs.Edwards.VartimeDoubleScalarMulBasepoint
import Proofs.Edwards.VartimeEdwardsPrecomputationLen
import Proofs.Edwards.VartimeEdwardsPrecomputationNew
import Proofs.Edwards.VartimeEdwardsPrecomputationOptionalMixedMultiscalarMul
import Proofs.Edwards.Zeroize
import Zeroize.Instances
public section

/-! # Specs of `src/edwards.rs`

Spec summary: the items of `edwards.rs` in the crate's public API, with their spec statements, each
restated with `recall` from the theorem proved in `Proofs/Edwards/`, and the axioms that proof
depends on. Items appear in the order of `edwards.rs`; the two 64-bit configurations
(`x86_64-tables`, `x86_64-no-tables`) are distinct types, so each `EdwardsPoint` item has two
statements. Items outside the public API (`is_valid`, `as_projective`, `as_projective_niels`,
`as_affine_niels`, `to_affine`, `double`, `mul_by_pow_2`, the `edwards/affine.rs` module) are proved
in `Proofs/` but not restated here.

**Complete except as follows.** Not restated here: `mul_base` and `mul_base_clamped` of
`x86_64-tables` and `vartime_double_scalar_mul_basepoint` of `x86_64-tables`. They read the
constants `ED25519_BASEPOINT_TABLE` and `AFFINE_ODD_MULTIPLES_OF_BASEPOINT`, and their proofs
(`…_spec_of_table` in `Proofs/Edwards/`) take as a hypothesis that the constant represents the
basepoint's table. `vartime_triple_scalar_mul_basepoint` is not proved. It needs the same
constants (`AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128`). `VartimePrecomputedMultiscalarMul::is_empty`
is not proved either: it calls `Vec::is_empty`, which the library leaves opaque without a spec.
The basepoint tables (`impl_basepoint_table!`) exist only in `x86_64-tables`. They are stated for a
table `Represents P` (row `i` holds the multiples of `2^(w i) • P`) and `Bounded`.

Statements are given at the point level (`toPoint`, the represented point of `curve25519.edwards`),
under the representation invariants `OnCurve` (`Z ≠ 0`, `X Y = Z T`, on the curve) and `Bounded`
(limbs `< 2^52`); the coordinate-level forms (`toExtended`, `ProjEq`) are the `@[step]` theorems of
the proof files. `is_identity`, the blanket implementation of `IsIdentity`, is stated generically
in `Specs/Traits.lean`.

Scalar multiplication is by the unreduced value `s.asNat` of the scalar's bytes, not by
`s.asNat % L`: `mul_clamped` and `is_torsion_free` build scalars `≥ L` (`clamp`, `BASEPOINT_ORDER =
L`). The precondition `s.asNat < 2^255` is the `debug_assert!(self[31] <= 127)` of `as_radix_16`.

The iterator-taking items (`Sum`, the multiscalar traits) are stated for an input that yields a
given list (`Iterator.Yields`, `IntoIterator.Yields`, `Defs/Iterator.lean`), each element borrowed
to a given scalar or point, with list lengths `≤ Usize.max`. The sums are over these lists:
`List.zipWith` pairs the scalars with the points. `multiscalar_mul` and `optional_multiscalar_mul`
require as many scalars as points (the patched `assert_eq!`). In `optional_mixed_multiscalar_mul`,
missing static scalars count as `0`. A precomputation `Represents` its static points
(`Defs/ScalarMul.lean`).

`CompressedEdwardsY::decompress` is dalek's lenient decoding `decodeLenient`
(`Defs/Edwards.lean`): a `y ≥ p` is reduced and `x = 0` is accepted with either sign bit, unlike
RFC 8032's strict decoder `curve25519.decode`.

Definitions used: `EdwardsPoint.toPoint`, `OnCurve`, `Bounded`, `CompressedEdwardsY.asNat`,
`decodeLenient` (`Defs/Edwards.lean`), `Scalar.asNat` (`Defs/Scalar.lean`), `curve25519.encode`
(`Curve25519/Edwards/Encoding.lean`), `curve25519.basepoint` (`Curve25519/Edwards/Basepoint.lean`),
`curve25519.clamp` (`Curve25519/X25519.lean`), `curve25519.L` (`Curve25519/Basic.lean`),
`curve25519.encodeU` (`Curve25519/X25519.lean`), `edwardsToMontgomery`
(`Curve25519/Montgomery.lean`), `MontgomeryPoint.asNat` (`Defs/Montgomery.lean`), the tables'
`Represents`, `Bounded` (`Defs/Edwards.lean`, `Defs/Window.lean`), `subtle.Choice.IsValid`
(`Subtle/`), `core.result.Result.map_spec` (`Curve25519Dalek/FunsExternal.lean`).

The axioms `…_native.decide.ax_*` and `core.fmt.Formatter` in the lists of the multiscalar and
basepoint-table items come from the translation of panics: Aeneas's `toStr` proves the length
bound of each message literal with `decide +native` (see `notes.md`), and Aeneas declares the
type `core.fmt.Formatter` as an axiom.

Not specified: derived `Clone`/`Copy` impls. Not translated: `Debug`, `Hash`, `map_to_curve`,
`encode_to_curve`, `hash_to_curve`, `random`, the `group` and `serde` impls. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for CompressedEdwardsY`: byte equality (two encodings of one point can
differ). -/
recall ct_eq_spec (self other : CompressedEdwardsY) :
    ct_eq self other ⦃ (c : subtle.Choice) => c.IsValid ∧ (c = 1#u8 ↔ self = other) ⦄

/-- [propext, Classical.choice, Quot.sound, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.SubtleConstantTimeEq

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts
namespace CoreCmpPartialEqCompressedEdwardsY

/-- `PartialEq for CompressedEdwardsY`: byte equality (two encodings of one point can differ). -/
recall eq_spec (self other : CompressedEdwardsY) :
    eq self other ⦃ (b : Bool) => b = true ↔ self = other ⦄

/-- [propext, Classical.choice, Quot.sound, Bool.Insts.CoreConvertFromChoice.from_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec, U8.Insts.SubtleConstantTimeEq.ct_eq_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end CoreCmpPartialEqCompressedEdwardsY
end Curve25519Dalek.edwards.CompressedEdwardsY.Insts

namespace Curve25519Dalek.edwards.CompressedEdwardsY

/-- `CompressedEdwardsY::as_bytes`: the bytes. -/
recall as_bytes_spec (self : CompressedEdwardsY) :
    as_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_bytes_spec

/-- `CompressedEdwardsY::to_bytes`: the bytes. -/
recall to_bytes_spec (self : CompressedEdwardsY) :
    to_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_bytes_spec

end Curve25519Dalek.edwards.CompressedEdwardsY

namespace Curve25519Dalek.edwards.CompressedEdwardsY.«x86_64-tables»

/-- `CompressedEdwardsY::decompress`: dalek's lenient decoding `decodeLenient` of the bytes'
value (`y` reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve with
limbs `< 2^52`. -/
recall decompress_spec (self : CompressedEdwardsY) :
    decompress.«x86_64-tables» self ⦃ (r : Option (EdwardsPoint.«x86_64-tables»)) =>
      r.map EdwardsPoint.«x86_64-tables».toPoint = decodeLenient self.asNat ∧
      ∀ q, r = some q → q.OnCurve ∧ q.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms decompress_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.«x86_64-tables»

namespace Curve25519Dalek.edwards.CompressedEdwardsY.«x86_64-no-tables»

/-- `CompressedEdwardsY::decompress`: dalek's lenient decoding `decodeLenient` of the bytes'
value (`y` reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve with
limbs `< 2^52`. -/
recall decompress_spec (self : CompressedEdwardsY) :
    decompress.«x86_64-no-tables» self ⦃ (r : Option (EdwardsPoint.«x86_64-no-tables»)) =>
      r.map EdwardsPoint.«x86_64-no-tables».toPoint = decodeLenient self.asNat ∧
      ∀ q, r = some q → q.OnCurve ∧ q.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms decompress_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.«x86_64-no-tables»

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts
namespace CoreConvertTryFromShared0SliceU8TryFromSliceError

/-- `TryFrom<&[u8]> for CompressedEdwardsY`: as `from_slice`. -/
recall try_from_spec (slice : Slice U8) :
    try_from slice ⦃ (r : core.result.Result CompressedEdwardsY core.array.TryFromSliceError) =>
      (slice.length = 32 → ∃ a : CompressedEdwardsY, r = .Ok a ∧ a.val = slice.val) ∧
      (slice.length ≠ 32 → r = .Err ()) ⦄

/-- [propext, Classical.choice, Quot.sound, core.result.Result.map_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms try_from_spec

end CoreConvertTryFromShared0SliceU8TryFromSliceError
end Curve25519Dalek.edwards.CompressedEdwardsY.Insts

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for CompressedEdwardsY` is the encoding of the neutral element. -/
recall identity_spec_point :
    identity ⦃ (r : CompressedEdwardsY) => r.asNat = encode 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec_point

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.CoreDefaultDefault

/-- `Default for CompressedEdwardsY` is the encoding of the neutral element. -/
recall default_spec_point :
    default ⦃ (r : CompressedEdwardsY) => r.asNat = encode 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec_point

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.CoreDefaultDefault

namespace Curve25519Dalek.edwards.CompressedEdwardsY

/-- `CompressedEdwardsY::from_slice`: the bytes of a slice of length `32`, an error otherwise. -/
recall from_slice_spec (bytes : Slice U8) :
    from_slice bytes ⦃ (r : core.result.Result CompressedEdwardsY core.array.TryFromSliceError) =>
      (bytes.length = 32 → ∃ a : CompressedEdwardsY, r = .Ok a ∧ a.val = bytes.val) ∧
      (bytes.length ≠ 32 → r = .Err ()) ⦄

/-- [propext, Classical.choice, Quot.sound, core.result.Result.map_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_slice_spec

end Curve25519Dalek.edwards.CompressedEdwardsY

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.ZeroizeZeroize

/-- `Zeroize for CompressedEdwardsY` leaves the encoding of the neutral element. -/
recall zeroize_spec_point (self : CompressedEdwardsY) :
    zeroize self ⦃ (r : CompressedEdwardsY) => r.asNat = encode 0 ⦄

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  zeroize.Zeroize.Blanket.zeroize_eq] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec_point

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.ZeroizeZeroize

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace Curve25519_dalekTraitsIdentity

/-- `Identity for EdwardsPoint` represents the neutral element. -/
recall identity_spec_point :
    identity ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec_point

end Curve25519_dalekTraitsIdentity
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace Curve25519_dalekTraitsIdentity

/-- `Identity for EdwardsPoint` represents the neutral element. -/
recall identity_spec_point :
    identity ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec_point

end Curve25519_dalekTraitsIdentity
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.CoreDefaultDefault

/-- `Default for EdwardsPoint` represents the neutral element. -/
recall default_spec_point :
    default ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec_point

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.CoreDefaultDefault

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

/-- `Default for EdwardsPoint` represents the neutral element. -/
recall default_spec_point :
    default ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec_point

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.ZeroizeZeroize

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
recall zeroize_spec_point (self : EdwardsPoint.«x86_64-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  zeroize.Zeroize.Blanket.zeroize_eq] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec_point

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.ZeroizeZeroize

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
recall zeroize_spec_point (self : EdwardsPoint.«x86_64-no-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, Array.Insts.ZeroizeZeroize.zeroize_spec,
  zeroize.Zeroize.Blanket.zeroize_eq] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec_point

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `EdwardsPoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : EdwardsPoint.«x86_64-tables») (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end SubtleConditionallySelectable
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `EdwardsPoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : EdwardsPoint.«x86_64-no-tables») (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound,
  U64.Insts.SubtleConditionallySelectable.conditional_select_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end SubtleConditionallySelectable
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for EdwardsPoint` on points: equality of the represented points. -/
recall ct_eq_spec_point (self other : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hother : other.Bounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.toPoint = other.toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec,
  subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec_point

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.SubtleConstantTimeEq

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace SubtleConstantTimeEq

/-- `ConstantTimeEq for EdwardsPoint` on points: equality of the represented points. -/
recall ct_eq_spec_point (self other : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hother : other.Bounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.toPoint = other.toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec,
  subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec_point

end SubtleConstantTimeEq
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreCmpPartialEqEdwardsPointx86_64-tables»

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
recall eq_spec_point (self other : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hother : other.Bounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, Bool.Insts.CoreConvertFromChoice.from_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec, U8.Insts.SubtleConstantTimeEq.ct_eq_spec,
  subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec_point

end «CoreCmpPartialEqEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreCmpPartialEqEdwardsPointx86_64-no-tables»

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
recall eq_spec_point (self other : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hother : other.Bounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, Bool.Insts.CoreConvertFromChoice.from_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec, U8.Insts.SubtleConstantTimeEq.ct_eq_spec,
  subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec_point

end «CoreCmpPartialEqEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of the represented point (`0` for the identity). -/
recall to_montgomery_spec_point (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (edwardsToMontgomery self.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_spec_point

end «EdwardsPointx86_64-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of the represented point (`0` for the identity). -/
recall to_montgomery_spec_point (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (edwardsToMontgomery self.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_spec_point

end «EdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
recall to_montgomery_batch_spec_point (eds : Slice EdwardsPoint.«x86_64-tables»)
    (heds : ∀ i < eds.length, eds[i]!.Bounded) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.asNat = encodeU (edwardsToMontgomery eds[i]!.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_batch_spec_point

end «EdwardsPointx86_64-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
recall to_montgomery_batch_spec_point (eds : Slice EdwardsPoint.«x86_64-no-tables»)
    (heds : ∀ i < eds.length, eds[i]!.Bounded) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.asNat = encodeU (edwardsToMontgomery eds[i]!.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_batch_spec_point

end «EdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
recall compress_spec_point (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.asNat = curve25519.encode self.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, subtle.Choice.unwrap_u8_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_spec_point

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
recall compress_spec_point (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.asNat = curve25519.encode self.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, subtle.Choice.unwrap_u8_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_spec_point

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_spec_point {N : Usize} (inputs : Array EdwardsPoint.«x86_64-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.Bounded) (hinputs_on : ∀ i < N.val, inputs[i]!.OnCurve) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec, subtle.Choice.unwrap_u8_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_spec_point

end «EdwardsPointx86_64-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_spec_point {N : Usize} (inputs : Array EdwardsPoint.«x86_64-no-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.Bounded) (hinputs_on : ∀ i < N.val, inputs[i]!.OnCurve) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec, subtle.Choice.unwrap_u8_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_spec_point

end «EdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_alloc_spec_point (inputs : Slice EdwardsPoint.«x86_64-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.Bounded)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, subtle.Choice.unwrap_u8_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_alloc_spec_point

end «EdwardsPointx86_64-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_alloc_spec_point (inputs : Slice EdwardsPoint.«x86_64-no-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.Bounded)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, subtle.Choice.unwrap_u8_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec, Slice.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_alloc_spec_point

end «EdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithAddSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Add<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec_point (self other : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.Bounded) (hother : other.Bounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec_point

end «CoreOpsArithAddSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Add<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec_point

end «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Add<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec_point

end «CoreOpsArithAddSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Add<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec_point (self rhs : edwards.EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec_point

end «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithAddSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Add<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec_point (self other : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.Bounded) (hother : other.Bounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec_point

end «CoreOpsArithAddSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Add<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec_point

end «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Add<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec_point

end «CoreOpsArithAddSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Add<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec_point (self rhs : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec_point

end «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec_point (self _rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : _rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : _rhs.OnCurve) :
    add_assign self _rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + _rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec_point

end «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddAssignEdwardsPointx86_64-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec_point

end «CoreOpsArithAddAssignEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-no-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec_point (self _rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : _rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : _rhs.OnCurve) :
    add_assign self _rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + _rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec_point

end «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddAssignEdwardsPointx86_64-no-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec_point

end «CoreOpsArithAddAssignEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec_point (self other : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.Bounded) (hother : other.Bounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec_point

end «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec_point

end «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec_point

end «CoreOpsArithSubSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec_point (self rhs : edwards.EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec_point

end «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec_point (self other : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.Bounded) (hother : other.Bounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec_point

end «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec_point

end «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec_point

end «CoreOpsArithSubSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec_point (self rhs : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec_point

end «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec_point (self _rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : _rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : _rhs.OnCurve) :
    sub_assign self _rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - _rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec_point

end «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubAssignEdwardsPointx86_64-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec_point

end «CoreOpsArithSubAssignEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-no-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec_point (self _rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : _rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : _rhs.OnCurve) :
    sub_assign self _rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - _rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec_point

end «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubAssignEdwardsPointx86_64-no-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hrhs : rhs.Bounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec_point

end «CoreOpsArithSubAssignEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace CoreIterTraitsAccumSum

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`);
limbs `< 2^52`. -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«x86_64-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«x86_64-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«x86_64-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.Bounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace CoreIterTraitsAccumSum

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`);
limbs `< 2^52`. -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«x86_64-no-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«x86_64-no-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«x86_64-no-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.Bounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithNegEdwardsPointx86_64-tables»

/-- `Neg for &EdwardsPoint` negates the represented point. -/
recall neg_spec_point (self : edwards.EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec_point

end «CoreOpsArithNegEdwardsPointx86_64-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithNegEdwardsPointx86_64-tables»

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
recall neg_spec_point (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec_point

end «CoreOpsArithNegEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithNegEdwardsPointx86_64-no-tables»

/-- `Neg for &EdwardsPoint` negates the represented point. -/
recall neg_spec_point (self : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec_point

end «CoreOpsArithNegEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithNegEdwardsPointx86_64-no-tables»

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
recall neg_spec_point (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec_point

end «CoreOpsArithNegEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • P` (unreduced, `< 2^255`). -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-tables») (scalar : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignSharedAScalar
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignScalar
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • P` (unreduced, `< 2^255`). -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (scalar : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignSharedAScalar
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignScalar
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointx86_64-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointx86_64-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.Bounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.scalar.Scalar.Insts

namespace Curve25519Dalek.SharedAScalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.Bounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.SharedAScalar.Insts

namespace Curve25519Dalek.scalar.Scalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.Bounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.scalar.Scalar.Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (scalar : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.Bounded) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.Shared0Scalar.Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-no-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.Bounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.scalar.Scalar.Insts

namespace Curve25519Dalek.SharedAScalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.Bounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.SharedAScalar.Insts

namespace Curve25519Dalek.scalar.Scalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.Bounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.scalar.Scalar.Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-no-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (scalar : scalar.Scalar)
    (hself : self.Bounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.Bounded) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.Shared0Scalar.Insts

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
limbs `< 2^52`. -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • P`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. -/
recall mul_clamped_spec (self : EdwardsPoint.«x86_64-tables») (bytes : Array U8 32#usize)
    (hself : self.Bounded) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = clamp (bytes.asNat 8) • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • P`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. -/
recall mul_clamped_spec (self : EdwardsPoint.«x86_64-no-tables») (bytes : Array U8 32#usize)
    (hself : self.Bounded) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = clamp (bytes.asNat 8) • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. -/
recall mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = clamp (bytes.asNat 8) • basepoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
recall multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«x86_64-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«x86_64-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«x86_64-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.Bounded ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Array.Insts.ZeroizeZeroize.zeroize_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  zeroize.Zeroize.Blanket.zeroize_eq, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms multiscalar_mul_spec

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
recall multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«x86_64-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«x86_64-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«x86_64-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.Bounded ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Array.Insts.ZeroizeZeroize.zeroize_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  zeroize.Zeroize.Blanket.zeroize_eq, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms multiscalar_mul_spec

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `EdwardsPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; Straus below `190` points, Pippenger from `190` on; unreduced scalars
`< 2^255`); limbs `< 2^52`. -/
recall optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«x86_64-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.Bounded ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  core.num.Usize.div_ceil_spec, core.fmt.Formatter,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.backend.serial.scalar_mul.pippenger.Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables».optional_multiscalar_mul._native.decide.ax_5] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms optional_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `EdwardsPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; Straus below `190` points, Pippenger from `190` on; unreduced scalars
`< 2^255`); limbs `< 2^52`. -/
recall optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«x86_64-no-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.Bounded ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  core.num.Usize.div_ceil_spec, core.fmt.Formatter,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.backend.serial.scalar_mul.pippenger.Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables».optional_multiscalar_mul._native.decide.ax_5] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms optional_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`); limbs `< 2^52` in, `< 2^54` out. -/
recall new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«x86_64-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«x86_64-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«x86_64-tables») => P' = P ⦄) ys
          ps)
    (hps : ∀ P ∈ ps, P.Bounded ∧ P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeEdwardsPrecomputation.«x86_64-tables») =>
        r.Represents (ps.map (·.toPoint)) ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms new_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`); limbs `< 2^52` in, `< 2^54` out. -/
recall new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«x86_64-no-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«x86_64-no-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«x86_64-no-tables») => P' = P ⦄)
          ys ps)
    (hps : ∀ P ∈ ps, P.Bounded ∧ P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeEdwardsPrecomputation.«x86_64-no-tables») =>
        r.Represents (ps.map (·.toPoint)) ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms new_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
recall len_spec (self : VartimeEdwardsPrecomputation.«x86_64-tables»)
    (ps : List curve25519.edwards.Point) (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms len_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
recall len_spec (self : VartimeEdwardsPrecomputation.«x86_64-no-tables»)
    (ps : List curve25519.edwards.Point) (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms len_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeEdwardsPrecomputation` (static points `ps`): `none` iff some dynamic point is `none`;
otherwise `∑ s_i • ps_i + ∑ d_i • Q_i` (at most `|ps|` static scalars, the missing ones count
as `0`; as many dynamic scalars as dynamic points; unreduced scalars `< 2^255`); limbs
`< 2^52`. -/
recall optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«x86_64-tables») Clause4_IntoIter)
    (self : VartimeEdwardsPrecomputation.«x86_64-tables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (ps : List curve25519.edwards.Point) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«x86_64-tables»))
    (hself : self.Represents ps) (hself_b : self.Bounded)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.Bounded ∧ Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : ss.length ≤ ps.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss ps).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec, core.fmt.Formatter,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms optional_mixed_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeEdwardsPrecomputation` (static points `ps`): `none` iff some dynamic point is `none`;
otherwise `∑ s_i • ps_i + ∑ d_i • Q_i` (at most `|ps|` static scalars, the missing ones count
as `0`; as many dynamic scalars as dynamic points; unreduced scalars `< 2^255`); limbs
`< 2^52`. -/
recall optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«x86_64-no-tables») Clause4_IntoIter)
    (self : VartimeEdwardsPrecomputation.«x86_64-no-tables») (static_scalars : I)
        (dynamic_scalars : J)
    (dynamic_points : K) (ps : List curve25519.edwards.Point) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (hself : self.Represents ps) (hself_b : self.Bounded)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.Bounded ∧ Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : ss.length ≤ ps.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss ps).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec, core.fmt.Formatter,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms optional_mixed_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^52`. -/
recall vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«x86_64-no-tables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.Bounded) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec, core.fmt.Formatter,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_double_scalar_mul_basepoint_spec

end «EdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableAffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^4`): row `i` is the lookup table of
`2^(8 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
recall create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.Bounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents basepoint.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::basepoint` (radix `2^4`): the point `P` the table represents;
limbs `< 2^52`. -/
recall basepoint_spec (self : EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.Bounded) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::mul_base` (radix `2^4`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^52`. -/
recall mul_base_spec (self : EdwardsBasepointTable.«x86_64-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.Bounded) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTablex86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTable`: `mul_base`, i.e. `scalar • P`. -/
recall mul_spec (self : edwards.EdwardsBasepointTable.«x86_64-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.Bounded)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTablex86_64-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsBasepointTablex86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<&EdwardsBasepointTable> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.Bounded) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTablex86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix32AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^5`): row `i` is the lookup table of
`2^(10 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
recall create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.Bounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.Represents basepoint.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::basepoint` (radix `2^5`): the point `P` the table represents;
limbs `< 2^52`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.Bounded) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::mul_base` (radix `2^5`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^52`. -/
recall mul_base_spec (self : EdwardsBasepointTableRadix32.«x86_64-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.Bounded) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix32x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix32`: `mul_base`, i.e. `scalar • P`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix32.«x86_64-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.Bounded)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix32x86_64-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix32x86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<&EdwardsBasepointTableRadix32> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.Bounded) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix32x86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix64AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^6`): row `i` is the lookup table of
`2^(12 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
recall create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.Bounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.Represents basepoint.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::basepoint` (radix `2^6`): the point `P` the table represents;
limbs `< 2^52`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.Bounded) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::mul_base` (radix `2^6`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^52`. -/
recall mul_base_spec (self : EdwardsBasepointTableRadix64.«x86_64-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.Bounded) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix64x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix64`: `mul_base`, i.e. `scalar • P`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix64.«x86_64-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.Bounded)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix64x86_64-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix64x86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<&EdwardsBasepointTableRadix64> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.Bounded) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix64x86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix128AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^7`): row `i` is the lookup table of
`2^(14 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
recall create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.Bounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.Represents basepoint.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::basepoint` (radix `2^7`): the point `P` the table represents;
limbs `< 2^52`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.Bounded) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::mul_base` (radix `2^7`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^52`. -/
recall mul_base_spec (self : EdwardsBasepointTableRadix128.«x86_64-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.Bounded) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix128x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix128`: `mul_base`, i.e. `scalar • P`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix128.«x86_64-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.Bounded)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix128x86_64-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts
set_option linter.style.longLine false
namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix128x86_64-tablesEdwardsPointx86_64-tables»
set_option linter.style.longLine true

/-- `Mul<&EdwardsBasepointTableRadix128> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.Bounded) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix128x86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix256AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^8`): row `i` is the lookup table of
`2^(16 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
recall create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.Bounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.Represents basepoint.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::basepoint` (radix `2^8`): the point `P` the table represents;
limbs `< 2^52`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.Bounded) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::mul_base` (radix `2^8`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^52`. -/
recall mul_base_spec (self : EdwardsBasepointTableRadix256.«x86_64-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.Bounded) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix256x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix256`: `mul_base`, i.e. `scalar • P`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix256.«x86_64-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.Bounded)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix256x86_64-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts
set_option linter.style.longLine false
namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix256x86_64-tablesEdwardsPointx86_64-tables»
set_option linter.style.longLine true

/-- `Mul<&EdwardsBasepointTableRadix256> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.Bounded) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.Bounded ⦄

set_option linter.style.longLine false in
/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec, core.num.Usize.div_ceil_spec,
  core.fmt.Formatter, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  _private.Curve25519Dalek.Funs.0.Curve25519Dalek.scalar.read_le_u64_into_loop.body._native.decide.ax_1] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix256x86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.Bounded) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.Represents P ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  subtle.Choice.Insts.CoreConvertFromU8.from_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

/-- `EdwardsPoint::mul_by_cofactor`: `8 • P`; limbs `< 2^52`. -/
recall mul_by_cofactor_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_by_cofactor_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::mul_by_cofactor`: `8 • P`; limbs `< 2^52`. -/
recall mul_by_cofactor_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_by_cofactor_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

/-- `EdwardsPoint::is_small_order`: `8 • P = 0`; limbs `< 2^52`. -/
recall is_small_order_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    is_small_order self ⦃ (b : Bool) => b = true ↔ 8 • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec, U8.Insts.SubtleConstantTimeEq.ct_eq_spec,
  subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_small_order_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::is_small_order`: `8 • P = 0`; limbs `< 2^52`. -/
recall is_small_order_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    is_small_order self ⦃ (b : Bool) => b = true ↔ 8 • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec, U8.Insts.SubtleConstantTimeEq.ct_eq_spec,
  subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_small_order_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

/-- `EdwardsPoint::is_torsion_free`: `L • P = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`); limbs `< 2^52`. -/
recall is_torsion_free_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (b : Bool) => b = true ↔ L • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec, U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_torsion_free_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::is_torsion_free`: `L • P = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`); limbs `< 2^52`. -/
recall is_torsion_free_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.Bounded)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (b : Bool) => b = true ↔ L • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, core.array.from_fn_spec,
  Bool.Insts.CoreConvertFromChoice.from_spec,
  MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec,
  Slice.Insts.SubtleConstantTimeEq.ct_eq_spec, U16.Insts.SubtleConstantTimeEq.ct_eq_spec,
  U64.Insts.SubtleConditionallySelectable.conditional_assign_spec,
  U8.Insts.SubtleConstantTimeEq.ct_eq_spec, subtle.Choice.Insts.CoreConvertFromU8.from_spec,
  subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_torsion_free_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»
