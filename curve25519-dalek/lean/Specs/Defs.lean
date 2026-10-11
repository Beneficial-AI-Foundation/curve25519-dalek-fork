/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import Aeneas
public import Curve25519Dalek.Types
public import Mathlib.Data.Nat.Digits.Defs
@[expose] public section

/-! # Spec definitions used across the crate (audited) -/

open Aeneas.Std

/-- The natural number with the array's elements as little-endian digits in radix `2^bits`:
`a[0] + 2^bits · a[1] + 2^(2 bits) · a[2] + …`. The digits may exceed `2^bits`.
Bytes use `bits = 8`. -/
def Aeneas.Std.Array.asNat {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n) : ℕ :=
  Nat.ofDigits (2 ^ bits) (a.val.map (·.val))

/-- The integer with the array's signed elements as little-endian digits in radix `2^bits`:
`a[0] + 2^bits · a[1] + 2^(2 bits) · a[2] + …`. Used for the signed-digit recodings of scalars. -/
def Aeneas.Std.Array.asInt {ty : IScalarTy} {n : Usize} (bits : ℕ) (a : Array (IScalar ty) n) : ℤ :=
  (a.val.map (·.val)).foldr (fun d acc => d + 2 ^ bits * acc) 0

namespace Curve25519Dalek

/-- The natural number encoded little-endian by the 32 bytes of a `Scalar` (not necessarily
reduced modulo `L`). -/
def scalar.Scalar.asNat (self : scalar.Scalar) : ℕ :=
  self.bytes.asNat 8

/-- The natural number encoded by a `HalfWidthScalar` (a `Scalar` meant to be below `2^128`). -/
def scalar.HalfWidthScalar.asNat (self : scalar.HalfWidthScalar) : ℕ :=
  scalar.Scalar.asNat self

/-- Needed for `a[i]!` on arrays of scalars; the default (the zero scalar) is never observed for
in-range indices. -/
instance instInhabitedScalar : Inhabited scalar.Scalar := ⟨⟨Array.repeat 32#usize 0#u8⟩⟩

end Curve25519Dalek
