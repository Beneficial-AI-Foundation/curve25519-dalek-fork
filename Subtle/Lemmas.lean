/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Subtle.Contract
@[expose] public section
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek

/-! # Derived results for `subtle` (no axioms)

* Closure lemmas for `subtle.Choice.IsValid`, the 0/1 invariant defined in `Subtle/Contract.lean`.
  `IsValid` is reducible, so it unfolds to `c = 0#u8 ∨ c = 1#u8` and is decidable.
* The Boolean view `subtle.Choice.toBool`.
* Specs of the faithful bodies in `Subtle/Contract.lean`: the two `ConditionallySelectable` defaults
  and `ConditionallyNegatable::conditional_negate`.
-/

/-! ## Validity -/

namespace subtle.Choice

theorem isValid_zero : subtle.Choice.IsValid 0#u8 := Or.inl rfl

theorem isValid_one : subtle.Choice.IsValid 1#u8 := Or.inr rfl

/-- The output of an integer `ct_eq` is valid. -/
theorem isValid_ite (p : Prop) [Decidable p] :
    subtle.Choice.IsValid (if p then 1#u8 else 0#u8) := by
  by_cases hp : p <;> simp [hp, IsValid]

/-- The output of a `ct_eq` with the implication-form spec (e.g. on slices) is valid. -/
theorem isValid_of_imp {p : Prop} {c : subtle.Choice} (h1 : p → c = 1#u8) (h0 : ¬p → c = 0#u8) :
    c.IsValid := by
  by_cases hp : p
  · exact Or.inr (h1 hp)
  · exact Or.inl (h0 hp)

theorem isValid_iff (c : subtle.Choice) : c.IsValid ↔ c.val ≤ 1 := by
  constructor
  · rintro (rfl | rfl) <;> decide
  · intro h
    have : c.val = 0 ∨ c.val = 1 := by scalar_tac
    rcases this with h0 | h1
    · exact Or.inl (UScalar.eq_of_val_eq (by simpa using h0))
    · exact Or.inr (UScalar.eq_of_val_eq (by simpa using h1))

/-- Needed e.g. for `x.is_negative().unwrap_u8() << 7`. -/
theorem IsValid.val_lt_two {c : subtle.Choice} (h : c.IsValid) : c.val < 2 := by
  have := (isValid_iff c).mp h
  scalar_tac

theorem IsValid.and {a b : subtle.Choice} (ha : a.IsValid) (hb : b.IsValid) :
    subtle.Choice.IsValid (a &&& b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem IsValid.or {a b : subtle.Choice} (ha : a.IsValid) (hb : b.IsValid) :
    subtle.Choice.IsValid (a ||| b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- `0` absorbs a valid `Choice` under `&&&`. -/
theorem IsValid.and_zero {a : subtle.Choice} (ha : a.IsValid) : a &&& 0#u8 = 0#u8 := by
  rcases ha with rfl | rfl <;> decide

/-- The output of `Not` is valid for every input. -/
theorem isValid_not (a : subtle.Choice) : subtle.Choice.IsValid (1#u8 &&& ~~~a) := by
  rw [isValid_iff, UScalar.val_and]
  exact Nat.and_le_left

/-! ## Boolean view -/

/-- The Boolean a `Choice` stands for, as computed by `From<Choice> for bool`. -/
def toBool (c : subtle.Choice) : Bool := c != 0#u8

@[simp] theorem toBool_zero : toBool 0#u8 = false := rfl

@[simp] theorem toBool_one : toBool 1#u8 = true := rfl

@[simp] theorem toBool_ite (p : Prop) [Decidable p] :
    toBool (if p then 1#u8 else 0#u8) = decide p := by
  split <;> simp_all

theorem toBool_and {a b : subtle.Choice} (ha : a.IsValid) (hb : b.IsValid) :
    toBool (a &&& b) = (toBool a && toBool b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem toBool_or {a b : subtle.Choice} (ha : a.IsValid) (hb : b.IsValid) :
    toBool (a ||| b) = (toBool a || toBool b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem toBool_not {a : subtle.Choice} (ha : a.IsValid) :
    toBool (1#u8 &&& ~~~a) = !toBool a := by
  rcases ha with rfl | rfl <;> decide

/-- Valid choices are determined by their Boolean view. -/
theorem IsValid.eq_of_toBool_eq {a b : subtle.Choice} (ha : a.IsValid) (hb : b.IsValid)
    (h : toBool a = toBool b) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

end subtle.Choice

/-! ## Specs of the faithful bodies -/

/-- The default `conditional_assign` behaves like the instance's `conditional_select`. -/
theorem subtle.ConditionallySelectable.conditional_assign.default_spec {Self : Type}
    (inst : subtle.ConditionallySelectable Self) (a b : Self) (c : subtle.Choice)
    (h : inst.conditional_select a b c ⦃ r => (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄) :
    subtle.ConditionallySelectable.conditional_assign.default inst a b c ⦃ r =>
      (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄ := h

/-- The default `conditional_swap` swaps iff `c = 1`, given that the instance's
    `conditional_assign` follows its contract at `c`. -/
theorem subtle.ConditionallySelectable.conditional_swap.default_spec {Self : Type}
    (inst : subtle.ConditionallySelectable Self) (a b : Self) (c : subtle.Choice)
    (h : ∀ x y, inst.conditional_assign x y c ⦃ r => (c = 0#u8 → r = x) ∧ (c = 1#u8 → r = y) ⦄) :
    subtle.ConditionallySelectable.conditional_swap.default inst a b c ⦃ r =>
      (c = 0#u8 → r = (a, b)) ∧ (c = 1#u8 → r = (b, a)) ⦄ := by
  unfold subtle.ConditionallySelectable.conditional_swap.default
  step with h as ⟨a1, h1⟩
  step with h as ⟨b1, h2⟩
  grind

/-- `conditional_negate` negates iff `c = 1`, given the result `n` of `neg x` and that the
    instance's `conditional_assign` follows its contract at `c`. -/
theorem subtle.ConditionallyNegatable.Blanket.conditional_negate_spec {T : Type}
    (inst : subtle.ConditionallySelectable T) (negInst : core.ops.arith.Neg T T)
    (x : T) (c : subtle.Choice) (n : T)
    (hneg : negInst.neg x ⦃ r => r = n ⦄)
    (h : ∀ y, inst.conditional_assign x y c ⦃ r => (c = 0#u8 → r = x) ∧ (c = 1#u8 → r = y) ⦄) :
    subtle.ConditionallyNegatable.Blanket.conditional_negate inst negInst x c ⦃ r =>
      (c = 0#u8 → r = x) ∧ (c = 1#u8 → r = n) ⦄ := by
  unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
  step with hneg as ⟨n', hn⟩
  step with h as ⟨r, hr⟩
  grind
