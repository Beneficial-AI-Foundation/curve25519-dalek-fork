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
import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.OptionalMixedMultiscalarMul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «VartimePrecomputedStrausx86_64-tables»

set_option linter.style.longLine false in
/-- `VartimePrecomputedStraus::optional_mixed_multiscalar_mul` (backend): the serial one. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«x86_64-tables») Clause4_IntoIter)
    (self : VartimePrecomputedStraus.«x86_64-tables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (ps : List curve25519.edwards.Point) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«x86_64-tables»))
    (hself : self.Represents ps) (hself_b : self.LimbsLt 54)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52 ∧ Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : ss.length ≤ ps.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss ps).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  rcases self with ⟨inner⟩
  unfold optional_mixed_multiscalar_mul
  exact
      serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-tables».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables».optional_mixed_multiscalar_mul_spec
    _ _ _ _ _ inner _ _ _ ps xs ss ys ds qops hself hself_b hstatic_scalars hdynamic_scalars
    hdynamic_points hborrow_static hborrow_dynamic hss hds hqs hxs hys hqops hstatic hdynamic

end «VartimePrecomputedStrausx86_64-tables»

namespace «VartimePrecomputedStrausx86_64-no-tables»

set_option linter.style.longLine false in
/-- `VartimePrecomputedStraus::optional_mixed_multiscalar_mul` (backend): the serial one. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«x86_64-no-tables») Clause4_IntoIter)
    (self : VartimePrecomputedStraus.«x86_64-no-tables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (ps : List curve25519.edwards.Point) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (hself : self.Represents ps) (hself_b : self.LimbsLt 54)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52 ∧ Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : ss.length ≤ ps.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss ps).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  rcases self with ⟨inner⟩
  unfold optional_mixed_multiscalar_mul
  exact
      serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-no-tables».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables».optional_mixed_multiscalar_mul_spec
    _ _ _ _ _ inner _ _ _ ps xs ss ys ds qops hself hself_b hstatic_scalars hdynamic_scalars
    hdynamic_points hborrow_static hborrow_dynamic hss hds hqs hxs hys hqops hstatic hdynamic

end «VartimePrecomputedStrausx86_64-no-tables»

end Curve25519Dalek.backend
