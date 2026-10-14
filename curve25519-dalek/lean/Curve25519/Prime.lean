/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
public section

/-! # Primality of `p` and `L`

TEMPORARY: both facts are axioms for now. They will be replaced by proofs with `PrimeCert`
(Pocklington certificates checked by the kernel) once the toolchain moves to Lean v4.33 or later:
`PrimeCert` releases for earlier toolchains do not use the module system, so they cannot be
imported here. See `notes.md`. -/

namespace curve25519

/-- `p = 2^255 - 19` is prime. Axiom until the `PrimeCert` proof can be imported. -/
axiom p_prime : p.Prime

/-- `L = 2^252 + 27742317777372353535851937790883648493` is prime. Axiom until the `PrimeCert`
proof can be imported. -/
axiom L_prime : L.Prime

instance : Fact p.Prime := ⟨p_prime⟩

instance : Fact L.Prime := ⟨L_prime⟩

end curve25519
