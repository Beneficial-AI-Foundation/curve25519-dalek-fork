/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
import Curve25519.Proofs.Prime.Certs
public section

/-! # Primality of `p` and `L`

`p_prime` and `L_prime`, from the Lucas certificates of `Curve25519.Proofs.Prime.Certs`, and the
`Fact` instances that make `ZMod p` and `ZMod L` fields. -/

namespace curve25519

/-- `p = 2^255 - 19` is prime. -/
theorem p_prime : p.Prime := by
  rw [p_eq_numeral]
  exact Proofs.p_numeral_prime

/-- `L = 2^252 + 27742317777372353535851937790883648493` is prime. -/
theorem L_prime : L.Prime := by
  rw [L_eq_numeral]
  exact Proofs.L_numeral_prime

instance : Fact p.Prime := ⟨p_prime⟩

instance : Fact L.Prime := ⟨L_prime⟩

end curve25519
