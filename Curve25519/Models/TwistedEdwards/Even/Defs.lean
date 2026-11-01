/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Group
public section

/-! # The 4-torsion of a complete twisted Edwards model: definitions

The equality test of Decaf/Ristretto representatives (Hamburg, *Decaf: eliminating cofactors
through point compression*; RFC 9496), independent of any encoding: for a complete twisted
Edwards model `E`, two points are related (`E.Rel`) iff they differ by an element of the
4-torsion `E.torsion4 = {P | 4 • P = 0}`. The even points themselves are Mathlib's `Even P`.

`torsion4` is a hidden construction; `Rel` is exposed (specifications unfold it). The
characterising lemmas are in `Curve25519.Models.TwistedEdwards.Even.Lemmas`. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] (E : TwistedEdwardsModel F) [E.IsComplete]

/-! ### The 4-torsion and the relation -/

/-- The 4-torsion `{P | 4 • P = 0}` of `E`. Hidden; see `mem_torsion4`. -/
def torsion4 : AddSubgroup E.Point where
  carrier := {P | 4 • P = 0}
  zero_mem' := nsmul_zero 4
  add_mem' {P Q} hP hQ := by
    change 4 • (P + Q) = 0
    rw [nsmul_add, Set.mem_ofPred_eq.mp hP, Set.mem_ofPred_eq.mp hQ, add_zero]
  neg_mem' {P} hP := by
    change 4 • -P = 0
    rw [neg_nsmul, Set.mem_ofPred_eq.mp hP, neg_zero]

variable {E}

/-- The 4-torsion is `{P | 4 • P = 0}`. -/
theorem mem_torsion4 {P : E.Point} : P ∈ E.torsion4 ↔ 4 • P = 0 :=
  Iff.rfl

variable (E)

/-- Two points are related iff they differ by 4-torsion: the equality test of Decaf/Ristretto
representatives. -/
@[expose] def Rel (P Q : E.Point) : Prop :=
  P - Q ∈ E.torsion4

end TwistedEdwardsModel
