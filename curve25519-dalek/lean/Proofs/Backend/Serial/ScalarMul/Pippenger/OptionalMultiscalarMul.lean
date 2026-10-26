/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Edwards.Add
import Proofs.Edwards.AddAssign
import Proofs.Edwards.AsProjectiveNiels
import Proofs.Edwards.Identity
import Proofs.Edwards.MulByPow2
public import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.AsInt
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.AsRadix2w
import Proofs.Scalar.ToRadix2wSizeHint
public import Proofs.Helpers.EdwardsOps.Instances
public import Proofs.Backend.Serial.ScalarMul.Pippenger.OptionalMultiscalarMulGeneric
public section

/-! # `Pippenger::optional_multiscalar_mul`

Pippenger's bucket method with radix-`2^w` digits (`w ∈ {6, 7, 8}` by the input size): for each
digit position `e` from the top, the points are added into the buckets `1, …, 2^(w-1)` by the
absolute value of their digit (subtracted for a negative digit), the buckets are combined into
`∑_b b • bucket_b = ∑_i d_i[e] • P_i` by two running sums, and the column is added to `2^w •` the
total. Only the first `min(|scalars|, |points|)` pairs are used (the patched zip); a `None`
among them gives `None`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.pippenger

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

private theorem optional_multiscalar_mul_loop0_eq (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables») (b : Usize) :
    optional_multiscalar_mul_loop0 bc buckets b =
      EdwardsOps.X86Tables.pippengerLoop0 bc buckets b := rfl

private theorem optional_multiscalar_mul_loop1_eq (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-tables»)
    (total : Option edwards.EdwardsPoint.«x86_64-tables») (di : Usize) :
    optional_multiscalar_mul_loop1 w bc sp buckets total di =
      EdwardsOps.X86Tables.pippengerLoop1 w bc sp buckets total di := by
  unfold optional_multiscalar_mul_loop1 EdwardsOps.pippengerLoop1
  congr 1
  funext ⟨b, t, d⟩
  -- the two bodies match on `total` with their own matchers
  cases t <;> rfl

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

namespace «VartimeMultiscalarMulPippengerEdwardsPointx86_64-tables».optional_multiscalar_mul

private theorem scalars_points_loop_eq {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It
      (Option edwards.EdwardsPoint.«x86_64-tables»))
    (scalars : Slice S) (points : It) (w : Usize)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-tables»))
    (k : Usize) :
    scalars_points_loop borrowInst iterInst scalars points w out k =
      EdwardsOps.X86Tables.pippengerScalarsPoints borrowInst iterInst scalars points w out
        k := by
  unfold scalars_points_loop EdwardsOps.pippengerScalarsPoints
  congr 1
  funext ⟨p, o, k⟩
  unfold scalars_points_loop.body EdwardsOps.pippengerScalarsPointsBody
  dsimp only
  -- the bodies match on the iterator's result with their own matchers
  split
  · congr 1; funext t; congr 1; funext s; congr 1; funext s1; congr 1; funext ⟨o, p1⟩
    rcases o with _ | _ | P <;> rfl
  · rfl

end «VartimeMultiscalarMulPippengerEdwardsPointx86_64-tables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

open «VartimeMultiscalarMulPippengerEdwardsPointx86_64-tables».optional_multiscalar_mul in
private theorem optional_multiscalar_mul_eq {I J Item IntoIter IntoIter2 : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item IntoIter)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option edwards.EdwardsPoint.«x86_64-tables») IntoIter2) (scalars : I) (points : J) :
    optional_multiscalar_mul scalarsInst borrowInst pointsInst scalars points =
      EdwardsOps.X86Tables.pippengerMain scalarsInst borrowInst pointsInst scalars points := by
  unfold optional_multiscalar_mul EdwardsOps.pippengerMain
  simp only [scalars_points, scalars_points_loop_eq, optional_multiscalar_mul_loop0_eq,
    optional_multiscalar_mul_loop1_eq]
  -- down the binds to the match on `o`, which each side does with its own matcher
  congr 1; funext t
  congr 1; funext scalars1
  congr 1; funext w; congr 1; funext md; congr 1; funext dc; congr 1; funext bc
  congr 1; funext t1; congr 1; funext o
  rcases o with _ | sp <;> rfl

/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^52`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
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
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (r = none ↔ none ∈ ops.take ss.length)
          ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  rw [optional_multiscalar_mul_eq]
  exact EdwardsOps.X86Tables.pippengerMain_spec
    EdwardsOps.X86Tables.identity_spec EdwardsOps.X86Tables.add_spec
    EdwardsOps.X86Tables.addAssign_spec EdwardsOps.X86Tables.mulByPow2_spec
    EdwardsOps.X86Tables.addN_spec EdwardsOps.X86Tables.subN_spec
    EdwardsOps.X86Tables.asExtended_spec EdwardsOps.X86Tables.asProjectiveNiels_spec scalarsInst
    borrowScalarInst pointsInst scalars points xs ops ss hscalars hpoints hborrow_scalars hss hps
    hxs

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

private theorem optional_multiscalar_mul_loop0_eq (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables») (b : Usize) :
    optional_multiscalar_mul_loop0 bc buckets b =
      EdwardsOps.I686Tables.pippengerLoop0 bc buckets b := rfl

private theorem optional_multiscalar_mul_loop1_eq (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-tables»)
    (total : Option edwards.EdwardsPoint.«i686-tables») (di : Usize) :
    optional_multiscalar_mul_loop1 w bc sp buckets total di =
      EdwardsOps.I686Tables.pippengerLoop1 w bc sp buckets total di := by
  unfold optional_multiscalar_mul_loop1 EdwardsOps.pippengerLoop1
  congr 1
  funext ⟨b, t, d⟩
  -- the two bodies match on `total` with their own matchers
  cases t <;> rfl

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

namespace «VartimeMultiscalarMulPippengerEdwardsPointi686-tables».optional_multiscalar_mul

private theorem scalars_points_loop_eq {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It
      (Option edwards.EdwardsPoint.«i686-tables»))
    (scalars : Slice S) (points : It) (w : Usize)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-tables»))
    (k : Usize) :
    scalars_points_loop borrowInst iterInst scalars points w out k =
      EdwardsOps.I686Tables.pippengerScalarsPoints borrowInst iterInst scalars points w out
        k := by
  unfold scalars_points_loop EdwardsOps.pippengerScalarsPoints
  congr 1
  funext ⟨p, o, k⟩
  unfold scalars_points_loop.body EdwardsOps.pippengerScalarsPointsBody
  dsimp only
  -- the bodies match on the iterator's result with their own matchers
  split
  · congr 1; funext t; congr 1; funext s; congr 1; funext s1; congr 1; funext ⟨o, p1⟩
    rcases o with _ | _ | P <;> rfl
  · rfl

end «VartimeMultiscalarMulPippengerEdwardsPointi686-tables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

open «VartimeMultiscalarMulPippengerEdwardsPointi686-tables».optional_multiscalar_mul in
private theorem optional_multiscalar_mul_eq {I J Item IntoIter IntoIter2 : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item IntoIter)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option edwards.EdwardsPoint.«i686-tables») IntoIter2) (scalars : I) (points : J) :
    optional_multiscalar_mul scalarsInst borrowInst pointsInst scalars points =
      EdwardsOps.I686Tables.pippengerMain scalarsInst borrowInst pointsInst scalars points := by
  unfold optional_multiscalar_mul EdwardsOps.pippengerMain
  simp only [scalars_points, scalars_points_loop_eq, optional_multiscalar_mul_loop0_eq,
    optional_multiscalar_mul_loop1_eq]
  -- down the binds to the match on `o`, which each side does with its own matcher
  congr 1; funext t
  congr 1; funext scalars1
  congr 1; funext w; congr 1; funext md; congr 1; funext dc; congr 1; funext bc
  congr 1; funext t1; congr 1; funext o
  rcases o with _ | sp <;> rfl

/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^26`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«i686-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«i686-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-tables») => (r = none ↔ none ∈ ops.take ss.length)
          ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  rw [optional_multiscalar_mul_eq]
  exact EdwardsOps.I686Tables.pippengerMain_spec
    EdwardsOps.I686Tables.identity_spec EdwardsOps.I686Tables.add_spec
    EdwardsOps.I686Tables.addAssign_spec EdwardsOps.I686Tables.mulByPow2_spec
    EdwardsOps.I686Tables.addN_spec EdwardsOps.I686Tables.subN_spec
    EdwardsOps.I686Tables.asExtended_spec EdwardsOps.I686Tables.asProjectiveNiels_spec scalarsInst
    borrowScalarInst pointsInst scalars points xs ops ss hscalars hpoints hborrow_scalars hss hps
    hxs

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

private theorem optional_multiscalar_mul_loop0_eq (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables») (b : Usize) :
    optional_multiscalar_mul_loop0 bc buckets b =
      EdwardsOps.X86NoTables.pippengerLoop0 bc buckets b := rfl

private theorem optional_multiscalar_mul_loop1_eq (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-no-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«x86_64-no-tables»)
    (total : Option edwards.EdwardsPoint.«x86_64-no-tables») (di : Usize) :
    optional_multiscalar_mul_loop1 w bc sp buckets total di =
      EdwardsOps.X86NoTables.pippengerLoop1 w bc sp buckets total di := by
  unfold optional_multiscalar_mul_loop1 EdwardsOps.pippengerLoop1
  congr 1
  funext ⟨b, t, d⟩
  -- the two bodies match on `total` with their own matchers
  cases t <;> rfl

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

namespace «VartimeMultiscalarMulPippengerEdwardsPointx86_64-no-tables».optional_multiscalar_mul

private theorem scalars_points_loop_eq {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It
      (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (scalars : Slice S) (points : It) (w : Usize)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«x86_64-no-tables»))
    (k : Usize) :
    scalars_points_loop borrowInst iterInst scalars points w out k =
      EdwardsOps.X86NoTables.pippengerScalarsPoints borrowInst iterInst scalars points w out
        k := by
  unfold scalars_points_loop EdwardsOps.pippengerScalarsPoints
  congr 1
  funext ⟨p, o, k⟩
  unfold scalars_points_loop.body EdwardsOps.pippengerScalarsPointsBody
  dsimp only
  -- the bodies match on the iterator's result with their own matchers
  split
  · congr 1; funext t; congr 1; funext s; congr 1; funext s1; congr 1; funext ⟨o, p1⟩
    rcases o with _ | _ | P <;> rfl
  · rfl

end «VartimeMultiscalarMulPippengerEdwardsPointx86_64-no-tables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

open «VartimeMultiscalarMulPippengerEdwardsPointx86_64-no-tables».optional_multiscalar_mul in
private theorem optional_multiscalar_mul_eq {I J Item IntoIter IntoIter2 : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item IntoIter)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option edwards.EdwardsPoint.«x86_64-no-tables») IntoIter2) (scalars : I) (points : J) :
    optional_multiscalar_mul scalarsInst borrowInst pointsInst scalars points =
      EdwardsOps.X86NoTables.pippengerMain scalarsInst borrowInst pointsInst scalars points := by
  unfold optional_multiscalar_mul EdwardsOps.pippengerMain
  simp only [scalars_points, scalars_points_loop_eq, optional_multiscalar_mul_loop0_eq,
    optional_multiscalar_mul_loop1_eq]
  -- down the binds to the match on `o`, which each side does with its own matcher
  congr 1; funext t
  congr 1; funext scalars1
  congr 1; funext w; congr 1; funext md; congr 1; funext dc; congr 1; funext bc
  congr 1; funext t1; congr 1; funext o
  rcases o with _ | sp <;> rfl

/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^52`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
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
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») =>
          (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  rw [optional_multiscalar_mul_eq]
  exact EdwardsOps.X86NoTables.pippengerMain_spec
    EdwardsOps.X86NoTables.identity_spec EdwardsOps.X86NoTables.add_spec
    EdwardsOps.X86NoTables.addAssign_spec EdwardsOps.X86NoTables.mulByPow2_spec
    EdwardsOps.X86NoTables.addN_spec EdwardsOps.X86NoTables.subN_spec
    EdwardsOps.X86NoTables.asExtended_spec EdwardsOps.X86NoTables.asProjectiveNiels_spec scalarsInst
    borrowScalarInst pointsInst scalars points xs ops ss hscalars hpoints hborrow_scalars hss hps
    hxs

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

private theorem optional_multiscalar_mul_loop0_eq (bc : Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables») (b : Usize) :
    optional_multiscalar_mul_loop0 bc buckets b =
      EdwardsOps.I686NoTables.pippengerLoop0 bc buckets b := rfl

private theorem optional_multiscalar_mul_loop1_eq (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-no-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«i686-no-tables»)
    (total : Option edwards.EdwardsPoint.«i686-no-tables») (di : Usize) :
    optional_multiscalar_mul_loop1 w bc sp buckets total di =
      EdwardsOps.I686NoTables.pippengerLoop1 w bc sp buckets total di := by
  unfold optional_multiscalar_mul_loop1 EdwardsOps.pippengerLoop1
  congr 1
  funext ⟨b, t, d⟩
  -- the two bodies match on `total` with their own matchers
  cases t <;> rfl

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

namespace «VartimeMultiscalarMulPippengerEdwardsPointi686-no-tables».optional_multiscalar_mul

private theorem scalars_points_loop_eq {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It
      (Option edwards.EdwardsPoint.«i686-no-tables»))
    (scalars : Slice S) (points : It) (w : Usize)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«i686-no-tables»))
    (k : Usize) :
    scalars_points_loop borrowInst iterInst scalars points w out k =
      EdwardsOps.I686NoTables.pippengerScalarsPoints borrowInst iterInst scalars points w out
        k := by
  unfold scalars_points_loop EdwardsOps.pippengerScalarsPoints
  congr 1
  funext ⟨p, o, k⟩
  unfold scalars_points_loop.body EdwardsOps.pippengerScalarsPointsBody
  dsimp only
  -- the bodies match on the iterator's result with their own matchers
  split
  · congr 1; funext t; congr 1; funext s; congr 1; funext s1; congr 1; funext ⟨o, p1⟩
    rcases o with _ | _ | P <;> rfl
  · rfl

end «VartimeMultiscalarMulPippengerEdwardsPointi686-no-tables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

open «VartimeMultiscalarMulPippengerEdwardsPointi686-no-tables».optional_multiscalar_mul in
private theorem optional_multiscalar_mul_eq {I J Item IntoIter IntoIter2 : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item IntoIter)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option edwards.EdwardsPoint.«i686-no-tables») IntoIter2) (scalars : I) (points : J) :
    optional_multiscalar_mul scalarsInst borrowInst pointsInst scalars points =
      EdwardsOps.I686NoTables.pippengerMain scalarsInst borrowInst pointsInst scalars points := by
  unfold optional_multiscalar_mul EdwardsOps.pippengerMain
  simp only [scalars_points, scalars_points_loop_eq, optional_multiscalar_mul_loop0_eq,
    optional_multiscalar_mul_loop1_eq]
  -- down the binds to the match on `o`, which each side does with its own matcher
  congr 1; funext t
  congr 1; funext scalars1
  congr 1; funext w; congr 1; funext md; congr 1; funext dc; congr 1; funext bc
  congr 1; funext t1; congr 1; funext o
  rcases o with _ | sp <;> rfl

/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^26`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«i686-no-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«i686-no-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-no-tables») =>
          (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  rw [optional_multiscalar_mul_eq]
  exact EdwardsOps.I686NoTables.pippengerMain_spec
    EdwardsOps.I686NoTables.identity_spec EdwardsOps.I686NoTables.add_spec
    EdwardsOps.I686NoTables.addAssign_spec EdwardsOps.I686NoTables.mulByPow2_spec
    EdwardsOps.I686NoTables.addN_spec EdwardsOps.I686NoTables.subN_spec
    EdwardsOps.I686NoTables.asExtended_spec EdwardsOps.I686NoTables.asProjectiveNiels_spec
    scalarsInst borrowScalarInst pointsInst scalars points xs ops ss hscalars hpoints
    hborrow_scalars hss hps hxs

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

end Curve25519Dalek.backend.serial.scalar_mul.pippenger
