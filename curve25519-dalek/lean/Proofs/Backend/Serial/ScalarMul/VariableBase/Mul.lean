/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.CompletedAsProjective
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Edwards.Identity
import Proofs.Helpers.AsInt
import Proofs.Helpers.Iterator
import Proofs.Helpers.StepSpecs
import Proofs.Scalar.AsRadix16
import Proofs.Window.LookupTableFrom
import Proofs.Window.LookupTableSelect
public section

/-! # `variable_base::mul`

Constant-time variable-base scalar multiplication: the radix-`16` digits `d[0], …, d[63]` of the
scalar (`as_radix_16`), Horner's rule from the top digit down, with `16 • Q` by four doublings and
`d[i] • P` from the lookup table of `P, 2 P, …, 8 P`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.variable_base

/-- The value `∑_{k < 64 - e} 16^k d[e + k]` of the top digits `d[e], …, d[63]`. -/
private def digitSum (d : Array I8 64#usize) (e : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (64 - e), 16 ^ k * d[e + k]!.val

private theorem digitSum_eq (d : Array I8 64#usize) (e : ℕ) (he : e < 64) :
    digitSum d e = d[e]!.val + 16 * digitSum d (e + 1) := by
  unfold digitSum
  rw [show 64 - e = 64 - (e + 1) + 1 by omega, Finset.sum_range_succ', Finset.mul_sum,
    pow_zero, one_mul, add_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ, show e + (k + 1) = e + 1 + k by omega]
  ring

private theorem digitSum_sixtyThree (d : Array I8 64#usize) : digitSum d 63 = d[63]!.val := by
  simp [digitSum]

private theorem digitSum_zero (d : Array I8 64#usize) : digitSum d 0 = d.asInt 4 := by
  rw [Array.asInt_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zero_add, pow_mul]
  norm_num

/-- One Horner step on points: four doublings of `z • P`, plus `d • P`. -/
private theorem horner_step (z d : ℤ) (P : curve25519.edwards.Point) :
    2 • 2 • 2 • 2 • (z • P) + d • P = (d + 16 * z) • P := by
  simp only [← natCast_zsmul, smul_smul, ← add_smul]
  congr 1
  push_cast
  ring

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (add_spec_point)
open edwards.EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity
  (identity_spec_point)

namespace «x86_64-tables»

open scoped Helpers.IndexStep in
/-- The loop of `mul`: after the digits `d[e], …, d[62]`, the accumulator represents
`digitSum d e • P`. -/
@[local step]
private theorem mul_loop_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_table : window.LookupTable ProjectiveNielsPoint.«x86_64-tables»)
    (scalar_digits : Array I8 64#usize) (tmp3 : edwards.EdwardsPoint.«x86_64-tables»)
    (tmp1 : CompletedPoint.«x86_64-tables») (P : curve25519.edwards.Point)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 63)
    (htab : lookup_table.Bounded) (hP : lookup_table.Represents P)
    (hd : ∀ i < 64, -8 ≤ scalar_digits[i]!.val ∧ scalar_digits[i]!.val ≤ 8)
    (hon : tmp1.OnCurve) (hb : tmp1.Bounded)
    (h1 : tmp1.toPoint = digitSum scalar_digits iter.iter.end.val • P) :
    mul.«x86_64-tables_loop» iter lookup_table scalar_digits tmp3 tmp1
      ⦃ (r : CompletedPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = digitSum scalar_digits 0 • P ∧ r.Bounded ⦄ := by
  unfold mul.«x86_64-tables_loop»
  apply loop.spec_decr_nat (measure := fun (it, _, _) => it.iter.end.val)
    (inv := fun (it, _, t) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 63 ∧ t.OnCurve ∧
      t.Bounded ∧ t.toPoint = digitSum scalar_digits it.iter.end.val • P)
  · rintro ⟨it, t3, t⟩ ⟨hst, hen, hton, htb, htp⟩
    unfold mul.«x86_64-tables_loop».body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, i, ho, hi, hstart1, hend1⟩
      subst ho
      step with «CompletedPointx86_64-tables».as_projective_spec_point as ⟨p1, hp1on, hp1, hp1b⟩
      step with «ProjectivePointx86_64-tables».double_spec_point as ⟨c1, hc1on, hc1, hc1b⟩
      step with «CompletedPointx86_64-tables».as_projective_spec_point as ⟨p2, hp2on, hp2, hp2b⟩
      step with «ProjectivePointx86_64-tables».double_spec_point as ⟨c2, hc2on, hc2, hc2b⟩
      step with «CompletedPointx86_64-tables».as_projective_spec_point as ⟨p3, hp3on, hp3, hp3b⟩
      step with «ProjectivePointx86_64-tables».double_spec_point as ⟨c3, hc3on, hc3, hc3b⟩
      step with «CompletedPointx86_64-tables».as_projective_spec_point as ⟨p4, hp4on, hp4, hp4b⟩
      step with «ProjectivePointx86_64-tables».double_spec_point as ⟨c4, hc4on, hc4, hc4b⟩
      step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨e, heon, he, heb⟩
      step as ⟨di, hdi⟩
      step with window.«LookupTableProjectiveNielsPointx86_64-tables».select_spec (P := P)
        as ⟨q, hqon, hq, hqb⟩
      step with add_spec_point as ⟨t', ht'on, ht', ht'b⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, ht'on, ht'b, ?_, by scalar_tac⟩
      rw [ht', he, hc4, hp4, hc3, hp3, hc2, hp2, hc1, hp1, htp, hq, hdi, horner_step, hend1, ← hi,
        digitSum_eq _ i.val (by scalar_tac)]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at htp
      exact ⟨hton, htp, htb⟩
  · exact ⟨hstart, hend, hon, hb, h1⟩

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`, the
precondition of `as_radix_16`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (point : edwards.EdwardsPoint.«x86_64-tables») (s : scalar.Scalar)
    (hpoint : point.Bounded) (hon : point.OnCurve) (hs : s.asNat < 2 ^ 255) :
    mul.«x86_64-tables» point s ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • point.toPoint ∧ r.Bounded ⦄ := by
  unfold mul.«x86_64-tables»
  step as ⟨table, hrep, htab⟩
  step as ⟨d, hval, hlow, h63l, h63u⟩
  have hd : ∀ i < 64, -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8 := fun i hi => by
    rcases Nat.lt_or_ge i 63 with h | h
    · exact ⟨(hlow i h).1, (hlow i h).2.le⟩
    · rw [show i = 63 by omega]; exact ⟨h63l, h63u⟩
  step with identity_spec_point as ⟨t3, ht3on, ht3, ht3b⟩
  step as ⟨d63, hd63⟩
  step with window.«LookupTableProjectiveNielsPointx86_64-tables».select_spec (P := point.toPoint)
    as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point as ⟨t1, ht1on, ht1, ht1b⟩
  step as ⟨iter, hiter⟩
  have h1 : t1.toPoint = digitSum d iter.iter.end.val • point.toPoint := by
    rw [ht1, ht3, hq, hd63, zero_add, hiter]
    exact congrArg (· • point.toPoint) (digitSum_sixtyThree d).symm
  step with mul_loop_spec iter table d t3 t1 point.toPoint (by rw [hiter]; rfl)
    (by rw [hiter]; decide) htab hrep hd ht1on ht1b h1 as ⟨t, hton, htp, htb⟩
  step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, htp, digitSum_zero, hval, natCast_zsmul]

end «x86_64-tables»

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
  (add_spec_point)
open edwards.EdwardsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity
  (identity_spec_point)

namespace «x86_64-no-tables»

open scoped Helpers.IndexStep in
/-- The loop of `mul`: after the digits `d[e], …, d[62]`, the accumulator represents
`digitSum d e • P`. -/
@[local step]
private theorem mul_loop_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_table : window.LookupTable ProjectiveNielsPoint.«x86_64-no-tables»)
    (scalar_digits : Array I8 64#usize) (tmp3 : edwards.EdwardsPoint.«x86_64-no-tables»)
    (tmp1 : CompletedPoint.«x86_64-no-tables») (P : curve25519.edwards.Point)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 63)
    (htab : lookup_table.Bounded) (hP : lookup_table.Represents P)
    (hd : ∀ i < 64, -8 ≤ scalar_digits[i]!.val ∧ scalar_digits[i]!.val ≤ 8)
    (hon : tmp1.OnCurve) (hb : tmp1.Bounded)
    (h1 : tmp1.toPoint = digitSum scalar_digits iter.iter.end.val • P) :
    mul.«x86_64-no-tables_loop» iter lookup_table scalar_digits tmp3 tmp1
      ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
        r.OnCurve ∧ r.toPoint = digitSum scalar_digits 0 • P ∧ r.Bounded ⦄ := by
  unfold mul.«x86_64-no-tables_loop»
  apply loop.spec_decr_nat (measure := fun (it, _, _) => it.iter.end.val)
    (inv := fun (it, _, t) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 63 ∧ t.OnCurve ∧
      t.Bounded ∧ t.toPoint = digitSum scalar_digits it.iter.end.val • P)
  · rintro ⟨it, t3, t⟩ ⟨hst, hen, hton, htb, htp⟩
    unfold mul.«x86_64-no-tables_loop».body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, i, ho, hi, hstart1, hend1⟩
      subst ho
      step with «CompletedPointx86_64-no-tables».as_projective_spec_point as ⟨p1, hp1on, hp1, hp1b⟩
      step with «ProjectivePointx86_64-no-tables».double_spec_point as ⟨c1, hc1on, hc1, hc1b⟩
      step with «CompletedPointx86_64-no-tables».as_projective_spec_point as ⟨p2, hp2on, hp2, hp2b⟩
      step with «ProjectivePointx86_64-no-tables».double_spec_point as ⟨c2, hc2on, hc2, hc2b⟩
      step with «CompletedPointx86_64-no-tables».as_projective_spec_point as ⟨p3, hp3on, hp3, hp3b⟩
      step with «ProjectivePointx86_64-no-tables».double_spec_point as ⟨c3, hc3on, hc3, hc3b⟩
      step with «CompletedPointx86_64-no-tables».as_projective_spec_point as ⟨p4, hp4on, hp4, hp4b⟩
      step with «ProjectivePointx86_64-no-tables».double_spec_point as ⟨c4, hc4on, hc4, hc4b⟩
      step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨e, heon, he, heb⟩
      step as ⟨di, hdi⟩
      step with window.«LookupTableProjectiveNielsPointx86_64-no-tables».select_spec (P := P)
        as ⟨q, hqon, hq, hqb⟩
      step with add_spec_point as ⟨t', ht'on, ht', ht'b⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, ht'on, ht'b, ?_, by scalar_tac⟩
      rw [ht', he, hc4, hp4, hc3, hp3, hc2, hp2, hc1, hp1, htp, hq, hdi, horner_step, hend1, ← hi,
        digitSum_eq _ i.val (by scalar_tac)]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at htp
      exact ⟨hton, htp, htb⟩
  · exact ⟨hstart, hend, hon, hb, h1⟩

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`, the
precondition of `as_radix_16`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (point : edwards.EdwardsPoint.«x86_64-no-tables») (s : scalar.Scalar)
    (hpoint : point.Bounded) (hon : point.OnCurve) (hs : s.asNat < 2 ^ 255) :
    mul.«x86_64-no-tables» point s ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • point.toPoint ∧ r.Bounded ⦄ := by
  unfold mul.«x86_64-no-tables»
  step as ⟨table, hrep, htab⟩
  step as ⟨d, hval, hlow, h63l, h63u⟩
  have hd : ∀ i < 64, -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8 := fun i hi => by
    rcases Nat.lt_or_ge i 63 with h | h
    · exact ⟨(hlow i h).1, (hlow i h).2.le⟩
    · rw [show i = 63 by omega]; exact ⟨h63l, h63u⟩
  step with identity_spec_point as ⟨t3, ht3on, ht3, ht3b⟩
  step as ⟨d63, hd63⟩
  step with window.«LookupTableProjectiveNielsPointx86_64-no-tables».select_spec
    (P := point.toPoint) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point as ⟨t1, ht1on, ht1, ht1b⟩
  step as ⟨iter, hiter⟩
  have h1 : t1.toPoint = digitSum d iter.iter.end.val • point.toPoint := by
    rw [ht1, ht3, hq, hd63, zero_add, hiter]
    exact congrArg (· • point.toPoint) (digitSum_sixtyThree d).symm
  step with mul_loop_spec iter table d t3 t1 point.toPoint (by rw [hiter]; rfl)
    (by rw [hiter]; decide) htab hrep hd ht1on ht1b h1 as ⟨t, hton, htp, htb⟩
  step with «CompletedPointx86_64-no-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, htp, digitSum_zero, hval, natCast_zsmul]

end «x86_64-no-tables»

end

end Curve25519Dalek.backend.serial.scalar_mul.variable_base
