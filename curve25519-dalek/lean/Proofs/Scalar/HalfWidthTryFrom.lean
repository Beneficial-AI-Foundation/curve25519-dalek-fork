/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

/-- An array with digits below `2 ^ bits` is below `2 ^ (bits * m)` iff its digits from `m` on
are zero. -/
private theorem Aeneas.Std.Array.asNat_lt_pow_iff {ty : UScalarTy} {n : Usize} (bits m : ℕ)
    (a : Array (UScalar ty) n) (hmn : m ≤ n.val) (ha : ∀ j < n.val, a[j]!.val < 2 ^ bits) :
    a.asNat bits < 2 ^ (bits * m) ↔ ∀ j, m ≤ j → j < n.val → a[j]!.val = 0 := by
  rw [Array.asNat_eq_sum, ← Finset.sum_range_add_sum_Ico _ hmn]
  constructor
  · intro hlt j hmj hjn
    by_contra hne
    have hle : 2 ^ (bits * j) * a[j]!.val ≤
        ∑ k ∈ Finset.Ico m n.val, 2 ^ (bits * k) * a[k]!.val :=
      Finset.single_le_sum (f := fun k => 2 ^ (bits * k) * a[k]!.val) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Ico.mpr ⟨hmj, hjn⟩)
    have hpow : 2 ^ (bits * m) ≤ 2 ^ (bits * j) * a[j]!.val :=
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hmj)).trans
        (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne))
    exact absurd hlt (Nat.not_lt.mpr (hpow.trans (hle.trans (Nat.le_add_left _ _))))
  · intro hz
    have h0 : ∑ k ∈ Finset.Ico m n.val, 2 ^ (bits * k) * a[k]!.val = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [hz k hk.1 hk.2, Nat.mul_zero]
    rw [h0, Nat.add_zero]
    exact Nat.sum_pow_mul_lt bits m (fun j => a[j]!.val) fun j hj => ha j (hj.trans_le hmn)

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple

/-- The loop of `try_from` checks that the bytes from `i` to `31` are zero. -/
@[local step]
private theorem try_from_loop_spec (value : Scalar) (i : Usize) (hi : 16 ≤ i.val ∧ i.val ≤ 32)
    (hz : ∀ j : ℕ, 16 ≤ j → j < i.val → value.bytes[j]!.val = 0) :
    try_from_loop value i ⦃ (r : core.result.Result HalfWidthScalar Unit) =>
      ((∀ j : ℕ, 16 ≤ j → j < 32 → value.bytes[j]!.val = 0) → r = .Ok value) ∧
      (¬ (∀ j : ℕ, 16 ≤ j → j < 32 → value.bytes[j]!.val = 0) → r = .Err ()) ⦄ := by
  unfold try_from_loop
  apply loop.spec_decr_nat (measure := fun i => 32 - i.val)
    (inv := fun i => (16 ≤ i.val ∧ i.val ≤ 32) ∧
      ∀ j : ℕ, 16 ≤ j → j < i.val → value.bytes[j]!.val = 0)
  · rintro k ⟨hk, hzk⟩
    unfold try_from_loop.body
    by_cases hlt : k.val < 32
    · simp only [show k < 32#usize by scalar_tac, ite_true]
      step with Array.index_usize_getElem!_spec as ⟨x, hx⟩
      by_cases hx0 : x = 0#u8
      · simp only [hx0, bne_self_eq_false, Bool.false_eq_true, ite_false]
        step as ⟨k1, hk1⟩
        refine ⟨by scalar_tac, by scalar_tac, fun j hj hjk => ?_, by scalar_tac⟩
        by_cases hjk' : j = k.val
        · rw [hjk', ← hx, hx0]
          rfl
        · exact hzk j hj (by scalar_tac)
      · simp only [bne_iff_ne, ne_eq, hx0, not_false_eq_true, ite_true, WP.spec_ok]
        refine ⟨fun hall => absurd ?_ hx0, fun _ => trivial⟩
        rw [hx]
        exact UScalar.eq_of_val_eq (hall k.val hk.1 hlt)
    · simp only [show ¬ k < 32#usize by scalar_tac, ite_false, WP.spec_ok]
      exact ⟨fun _ => trivial, fun hn => absurd (fun j hj hj32 => hzk j hj (by scalar_tac)) hn⟩
  · exact ⟨hi, hz⟩

@[step]
theorem try_from_spec (value : Scalar) :
    try_from value ⦃ (r : core.result.Result HalfWidthScalar Unit) =>
      (value.asNat < 2 ^ 128 → r = .Ok value) ∧ (2 ^ 128 ≤ value.asNat → r = .Err ()) ⦄ := by
  unfold try_from
  step with try_from_loop_spec as ⟨r, hok, herr⟩
  have hiff := Array.asNat_lt_pow_iff 8 16 value.bytes (by simp)
    fun j _ => (value.bytes[j]!).hBounds
  simp only [scalar.Scalar.asNat_def] at *
  refine ⟨fun hlt => hok (hiff.mp hlt), fun hge => herr fun hall => ?_⟩
  exact absurd (hiff.mpr hall) (Nat.not_lt.mpr hge)

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple
