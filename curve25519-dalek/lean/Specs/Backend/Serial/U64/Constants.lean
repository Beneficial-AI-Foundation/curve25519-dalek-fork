/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
public import Defs.Scalar52
import Proofs.Backend.Serial.U64.Constants.Aplus2OverFour
import Proofs.Backend.Serial.U64.Constants.EdwardsD
import Proofs.Backend.Serial.U64.Constants.EdwardsD2
import Proofs.Backend.Serial.U64.Constants.EdwardsDMinusOneSquared
import Proofs.Backend.Serial.U64.Constants.InvsqrtAMinusD
import Proofs.Backend.Serial.U64.Constants.L
import Proofs.Backend.Serial.U64.Constants.Lfactor
import Proofs.Backend.Serial.U64.Constants.MinusOne
import Proofs.Backend.Serial.U64.Constants.OneMinusEdwardsDSquared
import Proofs.Backend.Serial.U64.Constants.R
import Proofs.Backend.Serial.U64.Constants.RR
import Proofs.Backend.Serial.U64.Constants.SqrtAdMinusOne
import Proofs.Backend.Serial.U64.Constants.SqrtM1
public section

/-! # Specs of `src/backend/serial/u64/constants.rs`

Spec summary: every constant of `constants.rs` with its spec statement, restated with `recall` from
the theorem proved in `Proofs/Backend/Serial/U64/Constants/`, and the axioms that proof depends on.
Definitions used: `FieldElement51.asNat` (`Defs/FieldElement51.lean`), `Scalar52.asNat`,
`montgomeryRadix` (`Defs/Scalar52.lean`), `p`, `a`, `d`, `A`, `sqrtM1`, `curve25519.L`
(`Curve25519/Basic.lean`).

Not yet specified (they need the curve model): `ED25519_BASEPOINT_POINT`,
`ED25519_BASEPOINT_128_POINT`, `EIGHT_TORSION`, `AFFINE_ODD_MULTIPLES_OF_BASEPOINT`,
`AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128`, `ED25519_BASEPOINT_TABLE`.
Not translated (`digest` feature off): `ED25519_SQRTAM2`, `MONTGOMERY_A`, `MONTGOMERY_A_NEG`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52 montgomeryRadix)
open curve25519 (p a d A sqrtM1)

namespace Curve25519Dalek.backend.serial.u64.constants

/-- `MINUS_ONE`: the field element `-1`. -/
recall MINUS_ONE_spec :
    MINUS_ONE ⦃ (r : FieldElement51) =>
      r.asNat + 1 = p ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms MINUS_ONE_spec

/-- `EDWARDS_D`: the Edwards coefficient `d`. -/
recall EDWARDS_D_spec :
    EDWARDS_D ⦃ (r : FieldElement51) =>
      r.asNat = d.val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EDWARDS_D_spec

/-- `EDWARDS_D2`: `2 d`. -/
recall EDWARDS_D2_spec :
    EDWARDS_D2 ⦃ (r : FieldElement51) =>
      r.asNat = (2 * d).val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EDWARDS_D2_spec

/-- `ONE_MINUS_EDWARDS_D_SQUARED`: `1 - d²`. -/
recall ONE_MINUS_EDWARDS_D_SQUARED_spec :
    ONE_MINUS_EDWARDS_D_SQUARED ⦃ (r : FieldElement51) =>
      r.asNat = (1 - d ^ 2).val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ONE_MINUS_EDWARDS_D_SQUARED_spec

/-- `EDWARDS_D_MINUS_ONE_SQUARED`: `(d - 1)²`. -/
recall EDWARDS_D_MINUS_ONE_SQUARED_spec :
    EDWARDS_D_MINUS_ONE_SQUARED ⦃ (r : FieldElement51) =>
      r.asNat = ((d - 1) ^ 2).val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms EDWARDS_D_MINUS_ONE_SQUARED_spec

/-- `SQRT_AD_MINUS_ONE`: a square root of `a d - 1`. -/
recall SQRT_AD_MINUS_ONE_spec :
    SQRT_AD_MINUS_ONE ⦃ (r : FieldElement51) =>
      r.asNat < p ∧
      r.asNat ^ 2 % p = (a * d - 1).val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms SQRT_AD_MINUS_ONE_spec

/-- `INVSQRT_A_MINUS_D`: `1 / sqrt(a - d)`, i.e. `r² (a - d) = 1`. -/
recall INVSQRT_A_MINUS_D_spec :
    INVSQRT_A_MINUS_D ⦃ (r : FieldElement51) =>
      r.asNat < p ∧
      r.asNat ^ 2 * (a - d).val % p = 1 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms INVSQRT_A_MINUS_D_spec

/-- `SQRT_M1`: the square root `sqrtM1` of `-1`. -/
recall SQRT_M1_spec :
    SQRT_M1 ⦃ (r : FieldElement51) =>
      r.asNat = sqrtM1 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms SQRT_M1_spec

/-- `APLUS2_OVER_FOUR`: `(A + 2) / 4 = 121666`. -/
recall APLUS2_OVER_FOUR_spec :
    APLUS2_OVER_FOUR ⦃ (r : FieldElement51) =>
      r.asNat * 4 = A + 2 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms APLUS2_OVER_FOUR_spec

/-- `L`: the group order `ℓ`, in canonical radix-2^52 limbs. -/
recall L_spec :
    Scalar52.asNat L = curve25519.L ∧ ∀ i < 5, L[i]!.val < 2 ^ 52

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms L_spec

/-- `LFACTOR`: `-ℓ⁻¹ mod 2^52`. -/
recall LFACTOR_spec :
    LFACTOR.val < 2 ^ 52 ∧ (LFACTOR.val * curve25519.L + 1) % 2 ^ 52 = 0

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms LFACTOR_spec

/-- `R`: the Montgomery radix `2^260 mod ℓ`. -/
recall R_spec :
    Scalar52.asNat R = montgomeryRadix % curve25519.L ∧ ∀ i < 5, R[i]!.val < 2 ^ 52

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms R_spec

/-- `RR`: `R² = 2^520 mod ℓ`. -/
recall RR_spec :
    Scalar52.asNat RR = montgomeryRadix ^ 2 % curve25519.L ∧ ∀ i < 5, RR[i]!.val < 2 ^ 52

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RR_spec

end Curve25519Dalek.backend.serial.u64.constants
