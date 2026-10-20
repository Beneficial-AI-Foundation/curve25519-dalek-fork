/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
public import Defs.ScalarMul
import Proofs.Backend.VartimePrecomputedStrausNew
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
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
        r.Represents (ps.map (·.toPoint)) ∧ r.Bounded ⦄ := by
  unfold new
  step with backend.«VartimePrecomputedStrausx86_64-tables».new_spec _ _ _ ys ps hstatic_points
      hborrow
    hps hys as ⟨v, hv, hvb⟩
  exact ⟨hv, hvb⟩

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
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
        r.Represents (ps.map (·.toPoint)) ∧ r.Bounded ⦄ := by
  unfold new
  step with backend.«VartimePrecomputedStrausx86_64-no-tables».new_spec _ _ _ ys ps hstatic_points
      hborrow
    hps hys as ⟨v, hv, hvb⟩
  exact ⟨hv, hvb⟩

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts


