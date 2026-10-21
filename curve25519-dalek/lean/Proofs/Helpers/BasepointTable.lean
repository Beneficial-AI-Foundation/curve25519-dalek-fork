/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.CurveModels.AddAffineNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Edwards.MulByPow2
import Proofs.Helpers.AsInt
import Proofs.Helpers.StepSpecs
public section

/-! # Generic forms of the basepoint-table functions

The five basepoint tables (`impl_basepoint_table!` with radix `2^w`, `w = 4, …, 8`) run the same
loops, differing only in the table type, its `From<&EdwardsPoint>` and `select`, the literal
`radix` and the number `adds` of digits. This file defines the generic loop bodies
(`createLoopBody`, `mulBaseLoopBody`), which the translated ones are definitionally equal to, and
proves their specs once:

- `create`: row `i` is the table of `2^(2 w i) • P`;
- `mul_base`: the loop over the digits `i ≡ i₀ (mod 2)` (`i₀ ∈ {0, 1}`, step `2`) adds
  `∑_k a[i₀ + 2 k] 2^(2 w k) • B`, selecting digit `i` from row `i / 2`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP ControlFlow
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards.basepointTable

/-! ### `create` -/

/-- The loop body of `BasepointTable::create`: row `i` is `from P`, then `P := 2^(2 radix) P`. -/
@[expose] def createLoopBody {Tab : Type}
    (fromF : EdwardsPoint.«x86_64-tables» → Result Tab) (radix : U32)
    (iter : core.ops.range.Range Usize) (a : Array Tab 32#usize)
    (P : EdwardsPoint.«x86_64-tables») :
    Result (ControlFlow ((core.ops.range.Range Usize) × (Array Tab 32#usize) ×
      EdwardsPoint.«x86_64-tables») (Array Tab 32#usize)) := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done a)
  | some i =>
    let lt ← fromF P
    let a1 ← Array.update a i lt
    let i1 ← radix + radix
    let P1 ← «EdwardsPointx86_64-tables».mul_by_pow_2 P i1
    ok (cont (iter1, a1, P1))

variable {Tab : Type} [Inhabited Tab]

open scoped Helpers.UpdateStep in
/-- The loop of `create` over `0..32`: row `i` represents `2^(2 w i) • B`. -/
theorem createLoop_spec (fromF : EdwardsPoint.«x86_64-tables» → Result Tab)
    (Rep : Tab → curve25519.edwards.Point → Prop) (Bnd : Tab → Prop)
    (hfrom : ∀ Q : EdwardsPoint.«x86_64-tables», Q.LimbsLt 52 → Q.OnCurve →
      fromF Q ⦃ (t : Tab) => Rep t Q.toPoint ∧ Bnd t ⦄)
    (radix : U32) (w : ℕ) (hw : radix.val = w) (hw' : 0 < w) (hw8 : w ≤ 8)
    (a : Array Tab 32#usize) (P : EdwardsPoint.«x86_64-tables»)
    (hP : P.LimbsLt 52) (hon : P.OnCurve) :
    loop (fun ((iter1, a1, P1) : (core.ops.range.Range Usize) × (Array Tab 32#usize) ×
        EdwardsPoint.«x86_64-tables») => createLoopBody fromF radix iter1 a1 P1)
      ({ start := 0#usize, «end» := 32#usize }, a, P)
      ⦃ (r : Array Tab 32#usize) =>
        ∀ i < 32, Rep r[i]! (2 ^ (2 * w * i) • P.toPoint) ∧ Bnd r[i]! ⦄ := by
  apply loop.spec_decr_nat (measure := fun (it, _, _) => it.end.val - it.start.val)
    (inv := fun (it, t, Q) => it.end.val = 32 ∧ it.start.val ≤ 32 ∧ Q.LimbsLt 52 ∧ Q.OnCurve ∧
      Q.toPoint = 2 ^ (2 * w * it.start.val) • P.toPoint ∧
      ∀ i < it.start.val, Rep t[i]! (2 ^ (2 * w * i) • P.toPoint) ∧ Bnd t[i]!)
  · rintro ⟨it, t, Q⟩ ⟨hend, hle, hQ, hQon, hQp, ht⟩
    unfold createLoopBody
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      step with hfrom Q hQ hQon as ⟨lt, hlt1, hlt2⟩
      step as ⟨a1, ha1, ha1'⟩
      step as ⟨i1, hi1⟩
      step with «EdwardsPointx86_64-tables».mul_by_pow_2_spec Q i1 hQ hQon (by scalar_tac)
        as ⟨Q1, hQ1on, hQ1, hQ1b⟩
      refine ⟨by rw [hend1, hend], by scalar_tac, hQ1b, hQ1on, ?_, fun i hi => ?_, by scalar_tac⟩
      · rw [hQ1, hQp, hstart1, smul_smul, ← pow_add, hi1]
        congr 1
        rw [hw]
        ring
      · rcases Nat.lt_or_ge i it.start.val with h | h
        · rw [ha1' i (by scalar_tac)]
          exact ht i h
        · have hi' : i = it.start.val := by scalar_tac
          subst hi'
          rw [ha1, ← hQp]
          exact ⟨hlt1, hlt2⟩
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      intro i hi
      exact ht i (by scalar_tac)
  · exact ⟨rfl, by decide, hP, hon, by rw [show (0#usize).val = 0 from rfl, mul_zero, pow_zero,
      one_smul], fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-! ### `mul_base` -/

open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (add_spec_point)

/-- The loop body of `BasepointTable::mul_base` (both loops): for `i < adds`, add the digit
`a[i]` selected from row `i / 2`, then `i := i + 2`. -/
@[expose] def mulBaseLoopBody (adds : Usize)
    (sel : Tab → I8 → Result AffineNielsPoint.«x86_64-tables») (a : Array I8 64#usize)
    (tables : Array Tab 32#usize) (P : EdwardsPoint.«x86_64-tables») (i : Usize) :
    Result (ControlFlow (EdwardsPoint.«x86_64-tables» × Usize) EdwardsPoint.«x86_64-tables») := do
  if i < adds
  then
    let i1 ← i / 2#usize
    let lt ← Array.index_usize tables i1
    let i2 ← Array.index_usize a i
    let anp ← sel lt i2
    let cp ←
      «CoreOpsArithAddSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables».add P anp
    let P1 ← «CompletedPointx86_64-tables».as_extended cp
    let i3 ← i + 2#usize
    ok (cont (P1, i3))
  else ok (done P)

private theorem zsmul_nsmul (x : ℤ) (n : ℕ) (B : curve25519.edwards.Point) :
    x • n • B = (x * n) • B := by
  rw [← natCast_zsmul, smul_smul]

/-- The sum over `k < m` of the digits `a[i₀ + 2 k]` vanishes from `m` on when the digits from
`adds` on do. -/
private theorem sum_range_eq_of_zero (a : Array I8 64#usize) (i0 m w : ℕ) (adds : ℕ)
    (hm : adds ≤ i0 + 2 * m) (hm32 : m ≤ 32) (hi0 : i0 < 2)
    (hz : ∀ j < 64, adds ≤ j → a[j]!.val = 0) :
    ∑ k ∈ Finset.range m, a[i0 + 2 * k]!.val * 2 ^ (2 * w * k) =
      ∑ k ∈ Finset.range 32, a[i0 + 2 * k]!.val * 2 ^ (2 * w * k) := by
  rw [← Finset.sum_range_add_sum_Ico _ hm32]
  have h0 : ∑ k ∈ Finset.Ico m 32, a[i0 + 2 * k]!.val * 2 ^ (2 * w * k) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      have hk' := Finset.mem_Ico.mp hk
      rw [hz _ (by omega) (by omega), zero_mul]
  rw [h0, add_zero]

open scoped Helpers.IndexStep in
/-- The loops of `mul_base` from `i₀ ∈ {0, 1}` in steps of `2`: they add
`∑_k a[i₀ + 2 k] 2^(2 w k) • B`, if digit `i` selected from row `i / 2` represents
`a[i] • 2^(2 w (i / 2)) • B` and the digits from `adds` on vanish. -/
theorem mulBaseLoop_spec (adds : Usize) (hadds : adds.val ≤ 64)
    (sel : Tab → I8 → Result AffineNielsPoint.«x86_64-tables») (a : Array I8 64#usize)
    (tables : Array Tab 32#usize) (B : curve25519.edwards.Point) (w : ℕ)
    (hsel : ∀ i < adds.val, sel tables[i / 2]! a[i]! ⦃ (q : AffineNielsPoint.«x86_64-tables») =>
      q.OnCurve ∧ q.toPoint = a[i]!.val • 2 ^ (2 * w * (i / 2)) • B ∧ q.LimbsLt 54 ⦄)
    (hz : ∀ j < 64, adds.val ≤ j → a[j]!.val = 0) (i0 : Usize) (hi0 : i0.val < 2)
    (P : EdwardsPoint.«x86_64-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve) :
    loop (fun ((P1, i1) : EdwardsPoint.«x86_64-tables» × Usize) =>
        mulBaseLoopBody adds sel a tables P1 i1) (P, i0)
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
        r.toPoint = P.toPoint +
          (∑ k ∈ Finset.range 32, a[i0.val + 2 * k]!.val * 2 ^ (2 * w * k)) • B ∧
        r.LimbsLt 52 ⦄ := by
  apply loop.spec_decr_nat (measure := fun (_, i) => adds.val + 2 - i.val)
    (inv := fun (Q, i) => i.val % 2 = i0.val ∧ i0.val ≤ i.val ∧ i.val ≤ adds.val + 1 ∧
      Q.OnCurve ∧ Q.LimbsLt 52 ∧ Q.toPoint = P.toPoint +
        (∑ k ∈ Finset.range (i.val / 2), a[i0.val + 2 * k]!.val * 2 ^ (2 * w * k)) • B)
  · rintro ⟨Q, i⟩ ⟨hpar, hge, hle, hQon, hQb, hQp⟩
    unfold mulBaseLoopBody
    by_cases hlt : i < adds
    · simp only [hlt, ite_true]
      have hi2 : i0.val + 2 * (i.val / 2) = i.val := by omega
      step as ⟨i1, hi1⟩
      step as ⟨lt, hlt'⟩
      step as ⟨d, hd⟩
      have hsel' := hsel i.val (by scalar_tac)
      rw [← hi1, ← hlt', ← hd] at hsel'
      step with hsel' as ⟨q, hqon, hq, hqb⟩
      step with add_spec_point Q q hQb hqb hQon hqon as ⟨c, hcon, hc, hcb⟩
      step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨Q1, hQ1on, hQ1, hQ1b⟩
      step as ⟨i3, hi3⟩
      refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, hQ1on, hQ1b, ?_, by scalar_tac⟩
      rw [hQ1, hc, hQp, hq, zsmul_nsmul, show i3.val / 2 = i.val / 2 + 1 by scalar_tac,
        Finset.sum_range_succ, hi2, add_smul, add_assoc, hd, hi1, Nat.cast_pow, Nat.cast_ofNat]
    · simp only [hlt, ite_false, WP.spec_ok]
      refine ⟨hQon, ?_, hQb⟩
      rw [hQp, sum_range_eq_of_zero a i0.val (i.val / 2) w adds.val (by scalar_tac)
        (by scalar_tac) hi0 hz]
  · refine ⟨Nat.mod_eq_of_lt hi0, le_refl _, by scalar_tac, hon, hP, ?_⟩
    rw [show i0.val / 2 = 0 by omega, Finset.sum_range_zero, zero_smul, add_zero]

private theorem sum_range_two_mul (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i = ∑ k ∈ Finset.range n, (f (2 * k) + f (1 + 2 * k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc, show 1 + 2 * n = 2 * n + 1 by ring]

/-- The radix-`2^w` digits split into the even ones and `2^w` times the odd ones, as summed by
the two loops of `mul_base`. -/
theorem asInt_eq_even_add_odd (a : Array I8 64#usize) (w : ℕ) :
    a.asInt w = ∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * w * k) +
      2 ^ w * ∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * w * k) := by
  rw [Array.asInt_eq_sum, show (64#usize).val = 2 * 32 from rfl, sum_range_two_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [zero_add, ← mul_assoc, mul_comm, mul_comm w 2]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, ← pow_add, show w * (1 + 2 * k) = w + 2 * w * k by ring, mul_comm]

/-- The result of `mul_base`: `2^w` times the odd-digit sum plus the even-digit sum. -/
theorem pow_nsmul_add_zsmul (S0 S1 : ℤ) (w : ℕ) (B : curve25519.edwards.Point) :
    2 ^ w • (S1 • B) + S0 • B = (S0 + 2 ^ w * S1) • B := by
  rw [← natCast_zsmul, smul_smul, ← add_smul, add_comm]
  push_cast
  rfl

end Curve25519Dalek.edwards.basepointTable
