/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
import Curve25519.Prime
import Mathlib.Algebra.Field.ZMod
import Specs.Backend.Serial.U64.Field.ConditionalAssign
import Specs.Backend.Serial.U64.Field.Mul
import Specs.Backend.Serial.U64.Field.One
import Specs.Field.Invert
import Specs.Field.IsZero
import Specs.Field.Lemmas
import Specs.Lemmas.Array
import Specs.Lemmas.ZMod
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.field.FieldElement51

/-! ## Prefix products of the nonzero inputs, in `ZMod p` -/

/-- The factor of input `k` in the running product: the input, or `1` if it is zero. -/
private def fac (inputs : Slice FieldElement51) (k : ℕ) : ZMod p :=
  if (inputs[k]!.asNat : ZMod p) = 0 then 1 else (inputs[k]!.asNat : ZMod p)

/-- The product of the nonzero inputs before index `i`. -/
private def pre (inputs : Slice FieldElement51) (i : ℕ) : ZMod p :=
  ∏ k ∈ Finset.range i, fac inputs k

private theorem fac_ne_zero (inputs : Slice FieldElement51) (k : ℕ) : fac inputs k ≠ 0 := by
  unfold fac
  split_ifs with h
  · exact one_ne_zero
  · exact h

private theorem pre_ne_zero (inputs : Slice FieldElement51) (i : ℕ) : pre inputs i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => fac_ne_zero inputs k

private theorem pre_succ (inputs : Slice FieldElement51) (i : ℕ) :
    pre inputs (i + 1) = pre inputs i * fac inputs i :=
  Finset.prod_range_succ _ i

private theorem not_one : (1#u8 &&& ~~~(1#u8 : subtle.Choice)) = 0#u8 := by decide

private theorem not_zero : (1#u8 &&& ~~~(0#u8 : subtle.Choice)) = 1#u8 := by decide

/-- `fe` is the product of the nonzero inputs before index `i`, with limbs `< 2^54`. -/
private def IsPre (inputs : Slice FieldElement51) (fe : FieldElement51) (i : ℕ) : Prop :=
  (fe.asNat : ZMod p) = pre inputs i ∧ ∀ j < 5, fe[j]!.val < 2 ^ 54

/-! ## First loop: prefix products into `scratch` -/

/-- Writing the prefix product at index `i` extends the prefix products of `s` to `i + 1`. -/
private theorem isPre_set {inputs s : Slice FieldElement51} {a : FieldElement51} {i : Usize}
    (hs : ∀ k < i.val, IsPre inputs s[k]! k) (ha : IsPre inputs a i.val) (hi : i.val < s.length) :
    ∀ k < i.val + 1, IsPre inputs (s.set i a)[k]! k :=
  Slice.forall_lt_succ_set (P := fun k x => IsPre inputs x k) hs ha hi

/-- One step of the first loop: store `acc` at `i`, multiply it by input `i` unless zero. -/
private theorem internal_invert_batch_loop0_body_spec (inputs scratch : Slice FieldElement51)
    (acc : FieldElement51) (n i : Usize) (hn : n.val = inputs.length)
    (hlen : scratch.length = inputs.length) (hlt : i < n)
    (hinputs : ∀ k < inputs.length, ∀ j < 5, (inputs[k]!)[j]!.val < 2 ^ 54)
    (hacc : IsPre inputs acc i.val) :
    internal_invert_batch_loop0.body inputs n scratch acc i ⦃ r =>
      ∃ acc1 i1, r = .cont (scratch.set i acc, acc1, i1) ∧ i1.val = i.val + 1 ∧
        IsPre inputs acc1 (i.val + 1) ⦄ := by
  unfold internal_invert_batch_loop0.body
  have hlt' : i.val < inputs.length := hn ▸ hlt
  have hab := hacc.2
  simp only [hlt, if_true]
  step as ⟨s1, hs1⟩
  step as ⟨fe, hfe⟩
  have hfe' : fe = inputs[i.val]! := by
    rw [hfe, Slice.getElem!_Nat_eq, getElem!_pos]
  have hfeb : ∀ j < 5, fe[j]!.val < 2 ^ 54 := hfe' ▸ hinputs i.val hlt'
  step as ⟨fe1, hfe1, hfe1b⟩
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨c1, _, hc1'⟩
  step as ⟨acc1, ha0, ha1⟩
  step as ⟨i1, hi1⟩
  refine ⟨acc1, i1, by rw [hs1], hi1, ?_⟩
  rw [IsPre, pre_succ, ← hacc.1, fac, ← hfe']
  by_cases hz : (fe.asNat : ZMod p) = 0
  · rw [hc1 (ZMod.natCast_eq_zero_iff_mod.mp hz), not_one] at hc1'
    rw [ha0 hc1', if_pos hz, mul_one]
    exact ⟨rfl, hab⟩
  · rw [hc0 (fun h => hz (ZMod.natCast_eq_zero_iff_mod.mpr h)), not_zero] at hc1'
    rw [ha1 hc1', if_neg hz, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
    exact ⟨hfe1, fun j hj => lt_trans (hfe1b j hj) (by norm_num)⟩

@[local step]
private theorem internal_invert_batch_loop0_spec (inputs scratch : Slice FieldElement51)
    (acc : FieldElement51) (n i : Usize) (hn : n.val = inputs.length)
    (hlen : scratch.length = inputs.length) (hi : i.val ≤ n.val)
    (hinputs : ∀ k < inputs.length, ∀ j < 5, (inputs[k]!)[j]!.val < 2 ^ 54)
    (hacc : IsPre inputs acc i.val) (hscratch : ∀ k < i.val, IsPre inputs scratch[k]! k) :
    internal_invert_batch_loop0 inputs scratch acc n i ⦃ (s : Slice FieldElement51)
      (a : FieldElement51) =>
      s.length = inputs.length ∧ IsPre inputs a inputs.length ∧
      ∀ k < inputs.length, IsPre inputs s[k]! k ⦄ := by
  unfold internal_invert_batch_loop0
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.2.val)
    (inv := fun x => x.2.2.val ≤ n.val ∧ x.1.length = inputs.length ∧
      IsPre inputs x.2.1 x.2.2.val ∧ ∀ k < x.2.2.val, IsPre inputs x.1[k]! k)
  · rintro ⟨s, a, i'⟩ ⟨hi', hsl, ha, hs⟩
    by_cases hlt : i' < n
    · apply spec_mono (internal_invert_batch_loop0_body_spec inputs s a n i' hn hsl hlt hinputs ha)
      rintro r ⟨acc1, i1, rfl, hi1, hacc1⟩
      have hsl' : i'.val < s.length := hsl ▸ hn ▸ hlt
      refine ⟨⟨hi1 ▸ hlt, by rw [Slice.set_length, hsl], hi1 ▸ hacc1, hi1 ▸ isPre_set hs ha hsl'⟩,
        ?_⟩
      dsimp only
      rw [hi1]
      exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self _)
    · unfold internal_invert_batch_loop0.body
      simp only [hlt, if_false, WP.spec_ok]
      have hin : i'.val = inputs.length := hn ▸ Nat.le_antisymm hi' (Nat.le_of_not_lt hlt)
      rw [hin] at ha hs
      exact ⟨hsl, ha, hs⟩
  · exact ⟨hi, hlen, hacc, hscratch⟩

/-! ## Second loop: the inverses, from the back -/

/-- What the batch inversion leaves in place of the input `x`. -/
private def Done (x r : FieldElement51) : Prop :=
  ((x.asNat : ZMod p) = 0 → r = x) ∧
  ((x.asNat : ZMod p) ≠ 0 → (r.asNat : ZMod p) * x.asNat = 1 ∧ ∀ i < 5, r[i]!.val < 2 ^ 52)

/-- One step of the second loop: input `k - 1` is replaced by its inverse, unless zero, and `acc`
becomes the inverse of the product before `k - 1`. -/
private theorem internal_invert_batch_loop1_body_spec
    (inputs0 inputs scratch : Slice FieldElement51) (acc : FieldElement51) (k : Usize)
    (hpos : k > 0#usize) (hk : k.val ≤ inputs0.length)
    (hlen : inputs.length = inputs0.length)
    (hinputs : ∀ k < inputs0.length, ∀ j < 5, (inputs0[k]!)[j]!.val < 2 ^ 54)
    (hscratch : ∀ k < inputs0.length, IsPre inputs0 scratch[k]! k)
    (hslen : scratch.length = inputs0.length)
    (hacc : (acc.asNat : ZMod p) * pre inputs0 k.val = 1)
    (haccb : ∀ j < 5, acc[j]!.val < 2 ^ 54)
    (hlow : ∀ j < k.val, inputs[j]! = inputs0[j]!) :
    internal_invert_batch_loop1.body scratch inputs acc k ⦃ r =>
      ∃ fe acc1 k1, r = .cont (inputs.set k1 fe, acc1, k1) ∧ k1.val + 1 = k.val ∧
        (acc1.asNat : ZMod p) * pre inputs0 k1.val = 1 ∧ (∀ j < 5, acc1[j]!.val < 2 ^ 54) ∧
        Done inputs0[k1.val]! fe ⦄ := by
  unfold internal_invert_batch_loop1.body
  simp only [hpos, if_true]
  step as ⟨k1, hk1⟩
  have hkk : k1.val + 1 = k.val := by scalar_tac
  have hk1' : k1.val < inputs0.length := lt_of_lt_of_le (hkk ▸ Nat.lt_succ_self k1.val) hk
  have hk1k : k1.val < k.val := hkk ▸ Nat.lt_succ_self _
  step as ⟨fe, hfe⟩
  have hfe' : fe = inputs0[k1.val]! := by
    rw [hfe, ← hlow k1.val hk1k, Slice.getElem!_Nat_eq, getElem!_pos]
  have hfeb : ∀ j < 5, fe[j]!.val < 2 ^ 54 := hfe' ▸ hinputs k1.val hk1'
  step as ⟨tmp, htmp, htmpb⟩
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨nz, _, hnz⟩
  step as ⟨fe1, hfe1⟩
  have hfe1' : fe1 = scratch[k1.val]! := by
    rw [hfe1, Slice.getElem!_Nat_eq, getElem!_pos]
  have hfe1b : ∀ j < 5, fe1[j]!.val < 2 ^ 54 := hfe1' ▸ (hscratch k1.val hk1').2
  step as ⟨prod, hprod, hprodb⟩
  step as ⟨fe2, back, hfe2, hback⟩
  step as ⟨fe3, hfe30, hfe31⟩
  step as ⟨acc1, ha0, ha1⟩
  refine ⟨fe3, acc1, k1, by rw [hback], hkk, ?_⟩
  have hfe2' : fe2 = inputs0[k1.val]! := by rw [hfe2, ← hfe, hfe']
  rw [← hkk, pre_succ, fac, ← hfe'] at hacc
  unfold Done
  rw [← hfe']
  by_cases hz : (fe.asNat : ZMod p) = 0
  · rw [hc1 (ZMod.natCast_eq_zero_iff_mod.mp hz), not_one] at hnz
    rw [ha0 hnz, hfe30 hnz, hfe2', ← hfe']
    rw [if_pos hz, mul_one] at hacc
    exact ⟨hacc, haccb, fun _ => rfl, fun h => absurd hz h⟩
  · rw [hc0 (fun h => hz (ZMod.natCast_eq_zero_iff_mod.mpr h)), not_zero] at hnz
    rw [ha1 hnz, hfe31 hnz]
    rw [if_neg hz] at hacc
    have htmp' : (tmp.asNat : ZMod p) = acc.asNat * fe.asNat := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
      exact htmp
    have hprod' : (prod.asNat : ZMod p) = acc.asNat * pre inputs0 k1.val := by
      rw [← (hscratch k1.val hk1').1, ← hfe1', ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
      exact hprod
    refine ⟨by rw [htmp', ← hacc]; ring, fun j hj => lt_trans (htmpb j hj) (by norm_num),
      fun h => absurd h hz, fun _ => ⟨by rw [hprod', ← hacc]; ring, hprodb⟩⟩

/-- Writing the result for index `k1` keeps the inputs below `k1` and extends the results to
`k1`. -/
private theorem done_set {inputs0 s : Slice FieldElement51} {fe : FieldElement51} {k1 : Usize}
    {k : ℕ} (hkk : k1.val + 1 = k) (hk1 : k1.val < s.length)
    (hl : ∀ j < k, s[j]! = inputs0[j]!)
    (hh : ∀ j < inputs0.length, k ≤ j → Done inputs0[j]! s[j]!)
    (hfe : Done inputs0[k1.val]! fe) :
    (∀ j < k1.val, (s.set k1 fe)[j]! = inputs0[j]!) ∧
    ∀ j < inputs0.length, k1.val ≤ j → Done inputs0[j]! (s.set k1 fe)[j]! := by
  obtain ⟨hkeep, hdone⟩ :=
    Slice.forall_ge_pred_set (P := fun j x => Done inputs0[j]! x) hkk hk1 hh hfe
  exact ⟨fun j hj => (hkeep j hj).trans (hl j (hkk ▸ Nat.lt_succ_of_lt hj)), hdone⟩

@[local step]
private theorem internal_invert_batch_loop1_spec (inputs0 inputs scratch : Slice FieldElement51)
    (acc : FieldElement51) (k : Usize) (hk : k.val ≤ inputs0.length)
    (hlen : inputs.length = inputs0.length)
    (hinputs : ∀ k < inputs0.length, ∀ j < 5, (inputs0[k]!)[j]!.val < 2 ^ 54)
    (hscratch : ∀ k < inputs0.length, IsPre inputs0 scratch[k]! k)
    (hslen : scratch.length = inputs0.length)
    (hacc : (acc.asNat : ZMod p) * pre inputs0 k.val = 1)
    (haccb : ∀ j < 5, acc[j]!.val < 2 ^ 54)
    (hlow : ∀ j < k.val, inputs[j]! = inputs0[j]!)
    (hhigh : ∀ j < inputs0.length, k.val ≤ j → Done inputs0[j]! inputs[j]!) :
    internal_invert_batch_loop1 inputs scratch acc k ⦃ (r : Slice FieldElement51) =>
      r.length = inputs0.length ∧ ∀ j < inputs0.length, Done inputs0[j]! r[j]! ⦄ := by
  unfold internal_invert_batch_loop1
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => x.2.2.val ≤ inputs0.length ∧ x.1.length = inputs0.length ∧
      (x.2.1.asNat : ZMod p) * pre inputs0 x.2.2.val = 1 ∧ (∀ j < 5, x.2.1[j]!.val < 2 ^ 54) ∧
      (∀ j < x.2.2.val, x.1[j]! = inputs0[j]!) ∧
      ∀ j < inputs0.length, x.2.2.val ≤ j → Done inputs0[j]! x.1[j]!)
  · rintro ⟨s, a, k'⟩ ⟨hk', hsl, ha, hab, hl, hh⟩
    by_cases hpos : k' > 0#usize
    · apply spec_mono (internal_invert_batch_loop1_body_spec inputs0 s scratch a k' hpos hk' hsl
        hinputs hscratch hslen ha hab hl)
      rintro r ⟨fe, acc1, k1, rfl, hkk, hacc1, hacc1b, hfe⟩
      have hk1 : k1.val < s.length := hsl ▸ lt_of_lt_of_le (hkk ▸ Nat.lt_succ_self k1.val) hk'
      have hk1k : k1.val < k'.val := hkk ▸ Nat.lt_succ_self _
      obtain ⟨hl1, hh1⟩ := done_set hkk hk1 hl hh hfe
      exact ⟨⟨Nat.le_of_lt (Nat.lt_of_lt_of_le hk1k hk'), by rw [Slice.set_length, hsl], hacc1,
        hacc1b, hl1, hh1⟩, hk1k⟩
    · unfold internal_invert_batch_loop1.body
      simp only [hpos, if_false, WP.spec_ok]
      have hk0 : k'.val = 0 := by scalar_tac
      rw [hk0] at hh
      exact ⟨hsl, fun j hj => hh j hj (Nat.zero_le j)⟩
  · exact ⟨hk, hlen, hacc, haccb, hlow, hhigh⟩

@[step]
theorem internal_invert_batch_spec (inputs scratch : Slice FieldElement51)
    (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, ∀ j < 5, (inputs[i]!)[j]!.val < 2 ^ 54) :
    internal_invert_batch inputs scratch ⦃ (r _scratch : Slice FieldElement51) =>
      r.length = inputs.length ∧
      ∀ i < inputs.length,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          ∀ j < 5, (r[i]!)[j]!.val < 2 ^ 52) ⦄ := by
  unfold internal_invert_batch
  step as ⟨hlen'⟩
  step as ⟨one, hone, honeb⟩
  have hone' : IsPre inputs one (0#usize).val := by
    refine ⟨?_, fun j hj => lt_trans (honeb j hj) (by norm_num)⟩
    rw [hone]
    simp [pre]
  step with internal_invert_batch_loop0_spec inputs scratch one inputs.len 0#usize (by simp) hlen
    (by simp) hinputs hone' (fun k hk => absurd hk (by simp))
    as ⟨scratch1, acc1, hs1len, hacc1', hs1⟩
  obtain ⟨hacc1, hacc1b⟩ := hacc1'
  step as ⟨c, _, hc1, hc0⟩
  rw [hc0 (fun h => pre_ne_zero inputs inputs.length
    (hacc1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h))]
  step as ⟨c1, _, hc1'⟩
  rw [not_zero] at hc1'
  subst hc1'
  step as ⟨b, hb⟩
  have hbt : b = true := by
    rw [hb]
    decide
  step as ⟨hbt'⟩
  step as ⟨acc2, hinv1, hinv0, hacc2b⟩
  have hn : inputs.len.val = inputs.length := by simp
  have hacc2 : (acc2.asNat : ZMod p) * pre inputs inputs.len.val = 1 := by
    have hne : acc1.asNat % p ≠ 0 := fun h =>
      pre_ne_zero inputs inputs.length (hacc1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h)
    have h := ZMod.natCast_eq_natCast_of_mod_eq (hinv1 hne)
    push_cast at h
    rw [hn, ← hacc1, h]
  step with internal_invert_batch_loop1_spec inputs inputs scratch1 acc2 inputs.len hn.le rfl
    hinputs hs1 hs1len hacc2 (fun j hj => lt_trans (hacc2b j hj) (by norm_num))
    (fun j _ => rfl) (fun j hj hkj => absurd hj (by rw [← hn]; exact Nat.not_lt.mpr hkj))
    as ⟨r, hrlen, hr⟩
  refine ⟨hrlen, fun i hi => ⟨fun h => (hr i hi).1 (ZMod.natCast_eq_zero_iff_mod.mpr h),
    fun h => ?_⟩⟩
  obtain ⟨h1, h2⟩ := (hr i hi).2 (fun h' => h (ZMod.natCast_eq_zero_iff_mod.mp h'))
  refine ⟨?_, h2⟩
  rw [← one_mod_p, ← ZMod.natCast_eq_natCast_iff']
  push_cast
  exact h1

end Curve25519Dalek.field.FieldElement51
