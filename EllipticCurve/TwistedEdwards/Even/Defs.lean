/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Data.Fintype.EquivFin
public section

/-! # The even quotient of a complete twisted Edwards model: definitions

The Decaf/Ristretto construction (Hamburg, *Decaf: eliminating cofactors through point
compression*; RFC 9496), independent of any encoding: for a complete twisted Edwards model `E`,
the group `E.EvenQuotient` is the quotient of the subgroup of *even* points (Mathlib's
`AddSubgroup.even E.Point`, the doubles `2 • Q`) by its intersection with the 4-torsion
`E.torsion4 = {P | 4 • P = 0}`. When `E.Point ≅ ℤ/8 × G` (ristretto255) or `ℤ/4 × G` (Decaf)
with `G` of odd order, the quotient is `G`. Two even points represent the same element iff they
differ by 4-torsion (`E.Rel`, `EvenQuotient.mk_eq_mk_iff` in
`EllipticCurve.TwistedEdwards.Even.Lemmas`).

The 4-torsion and the quotient are hidden constructions; `Rel` is exposed (specifications unfold
it). The characterising lemmas are in `EllipticCurve.TwistedEdwards.Even.Lemmas`. -/

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

/-- Two points represent the same element of the even quotient iff they differ by 4-torsion:
the equality test of Decaf/Ristretto representatives. -/
@[expose] def Rel (P Q : E.Point) : Prop :=
  P - Q ∈ E.torsion4

/-! ### The even quotient -/

/-- The even quotient `(AddSubgroup.even E.Point) ⧸ (E.torsion4 ⊓ AddSubgroup.even E.Point)`:
the Decaf/Ristretto group of `E`. Hidden construction; see `EvenQuotient.mk`,
`EvenQuotient.mk_eq_mk_iff`, `EvenQuotient.mk_surjective` and the homomorphism lemmas in
`EllipticCurve.TwistedEdwards.Even.Lemmas`. -/
def EvenQuotient : Type u :=
  ↥(AddSubgroup.even E.Point) ⧸ E.torsion4.addSubgroupOf (AddSubgroup.even E.Point)

/-- The group law of the even quotient. Hidden construction; it is characterised by the
`EvenQuotient.mk_*` lemmas. -/
@[no_expose] noncomputable instance instAddCommGroupEvenQuotient : AddCommGroup E.EvenQuotient :=
  QuotientAddGroup.Quotient.addCommGroup _

instance instFiniteEvenQuotient [Finite E.Point] : Finite E.EvenQuotient :=
  Quotient.finite _

@[no_expose] noncomputable instance instFintypeEvenQuotient [Finite E.Point] :
    Fintype E.EvenQuotient :=
  Fintype.ofFinite _

namespace EvenQuotient

variable {E}

/-- The class of an even point in the even quotient. -/
noncomputable def mk (P : E.Point) (h : Even P) : E.EvenQuotient :=
  QuotientAddGroup.mk (⟨P, AddSubgroup.mem_even.mpr h⟩ : AddSubgroup.even E.Point)

/-- The equality of two classes in terms of the representatives, for
`EllipticCurve.TwistedEdwards.Even.Lemmas` and `decidableEq`. Internal. -/
private theorem mk_eq_mk_iff_aux (a b : AddSubgroup.even E.Point) :
    (QuotientAddGroup.mk a : ↥(AddSubgroup.even E.Point) ⧸
      E.torsion4.addSubgroupOf (AddSubgroup.even E.Point)) = QuotientAddGroup.mk b ↔
      E.Rel (a : E.Point) b := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg,
    Rel, neg_add_eq_sub, ← AddSubgroup.neg_mem_iff, neg_sub]

/-- Equality in the even quotient is decidable when `E.Rel` is (e.g. through the coordinate
formula `rel_iff`). Noncomputable, as everything built on the hidden group law. -/
noncomputable def decidableEq [DecidableRel E.Rel] : DecidableEq E.EvenQuotient := fun a b =>
  Quotient.recOnSubsingleton₂ (motive := fun a b => Decidable (a = b)) a b fun P Q =>
    decidable_of_iff (E.Rel (P : E.Point) Q) (mk_eq_mk_iff_aux P Q).symm

end EvenQuotient

end TwistedEdwardsModel
