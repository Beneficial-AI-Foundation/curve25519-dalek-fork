/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
import Proofs.Backend.StrausMultiscalarMul
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
public section

/-! # `MultiscalarMul for EdwardsPoint`

The patched wrapper collects both inputs into vectors, asserts that they have the same length
and calls `backend::straus_multiscalar_mul` on the vectors. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
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
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  unfold multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold «MultiscalarMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».multiscalar_mul.collect
    «MultiscalarMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».multiscalar_mul.collect_loop
  apply spec_bind (collect.collectLoop_spec _ it xs hit (alloc.vec.Vec.new _) (by simpa using hxs))
  intro vs hvs
  step with hpoints' as ⟨it1, hit1⟩
  apply spec_bind
      (collect.collectLoop_spec _ it1 ys hit1 (alloc.vec.Vec.new _) (by simpa using hys))
  intro vp hvp
  replace hvs : vs.val = xs := by rw [hvs]; rfl
  replace hvp : vp.val = ys := by rw [hvp]; rfl
  step
  exact backend.«x86_64-tables».straus_multiscalar_mul_spec _ _ _ _ _ _ xs ys ss ps
    (hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs)
    (hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp)
    hborrow_scalars hborrow_points hss hps hxs hys

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-tables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«i686-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«i686-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«i686-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«i686-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 26 ⦄ := by
  unfold multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold «MultiscalarMulEdwardsPointi686-tablesEdwardsPointi686-tables».multiscalar_mul.collect
    «MultiscalarMulEdwardsPointi686-tablesEdwardsPointi686-tables».multiscalar_mul.collect_loop
  apply spec_bind (collect.collectLoop_spec _ it xs hit (alloc.vec.Vec.new _) (by simpa using hxs))
  intro vs hvs
  step with hpoints' as ⟨it1, hit1⟩
  apply spec_bind
      (collect.collectLoop_spec _ it1 ys hit1 (alloc.vec.Vec.new _) (by simpa using hys))
  intro vp hvp
  replace hvs : vs.val = xs := by rw [hvs]; rfl
  replace hvp : vp.val = ys := by rw [hvp]; rfl
  step
  exact backend.«i686-tables».straus_multiscalar_mul_spec _ _ _ _ _ _ xs ys ss ps
    (hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs)
    (hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp)
    hborrow_scalars hborrow_points hss hps hxs hys

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables»

open «MultiscalarMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables» in
/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
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
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  unfold multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold multiscalar_mul.collect multiscalar_mul.collect_loop
  apply spec_bind (collect.collectLoop_spec _ it xs hit (alloc.vec.Vec.new _) (by simpa using hxs))
  intro vs hvs
  step with hpoints' as ⟨it1, hit1⟩
  apply spec_bind
      (collect.collectLoop_spec _ it1 ys hit1 (alloc.vec.Vec.new _) (by simpa using hys))
  intro vp hvp
  replace hvs : vs.val = xs := by rw [hvs]; rfl
  replace hvp : vp.val = ys := by rw [hvp]; rfl
  step
  exact backend.«x86_64-no-tables».straus_multiscalar_mul_spec _ _ _ _ _ _ xs ys ss ps
    (hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs)
    (hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp)
    hborrow_scalars hborrow_points hss hps hxs hys

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-no-tables»

open «MultiscalarMulEdwardsPointi686-no-tablesEdwardsPointi686-no-tables» in
/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«i686-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«i686-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«i686-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 26 ⦄ := by
  unfold multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold multiscalar_mul.collect multiscalar_mul.collect_loop
  apply spec_bind (collect.collectLoop_spec _ it xs hit (alloc.vec.Vec.new _) (by simpa using hxs))
  intro vs hvs
  step with hpoints' as ⟨it1, hit1⟩
  apply spec_bind
      (collect.collectLoop_spec _ it1 ys hit1 (alloc.vec.Vec.new _) (by simpa using hys))
  intro vp hvp
  replace hvs : vs.val = xs := by rw [hvs]; rfl
  replace hvp : vp.val = ys := by rw [hvp]; rfl
  step
  exact backend.«i686-no-tables».straus_multiscalar_mul_spec _ _ _ _ _ _ xs ys ss ps
    (hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs)
    (hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp)
    hborrow_scalars hborrow_points hss hps hxs hys

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts


