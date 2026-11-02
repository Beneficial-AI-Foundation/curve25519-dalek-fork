/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Edwards
public import Defs.ScalarMul
public import Defs.Window
public section

/-! # `Represents`: tables and precomputations of given points (proof helper, not audited)

`t.Represents P` says that a table `t` holds the multiples of the point `P` that its algorithm
reads (`(j + 1) • P` for a lookup table, `(2 k + 1) • P` for a NAF table, row by row for the
basepoint tables), and `pre.Represents ps` that a precomputation holds the NAF tables of the
points `ps`. The proofs are stated with these relations; the public specifications use the
invariants `IsTable` and `IsValid` with the points `t.point` and `pre.points` (`Defs`), which
`represents_iff` relates to them. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

namespace window

variable {T : Type} [Inhabited T] [PointRepr T]

/-- Entry `j` of `t` (`j < 8`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTable.Represents (t : LookupTable T) (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 8, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Entry `j` of `t` (`j < 16`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix32.Represents (t : LookupTableRadix32 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 16, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Entry `j` of `t` (`j < 32`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix64.Represents (t : LookupTableRadix64 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 32, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Entry `j` of `t` (`j < 64`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix128.Represents (t : LookupTableRadix128 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 64, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Entry `j` of `t` (`j < 128`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix256.Represents (t : LookupTableRadix256 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 128, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Entry `k` of `t` (`k < 8`) is on the curve and represents the odd multiple `(2 k + 1) • P`. -/
@[expose] def NafLookupTable5.Represents (t : NafLookupTable5 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ k < 8, PointRepr.OnCurve t[k]! ∧ PointRepr.toPoint t[k]! = (2 * k + 1) • P

/-- Entry `k` of `t` (`k < 64`) is on the curve and represents the odd multiple
`(2 k + 1) • P`. -/
@[expose] def NafLookupTable8.Represents (t : NafLookupTable8 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ k < 64, PointRepr.OnCurve t[k]! ∧ PointRepr.toPoint t[k]! = (2 * k + 1) • P

end window

namespace edwards

/-- Row `i` of the radix-`16` table is the lookup table of `2^(8 i) • P`. -/
@[expose] def EdwardsBasepointTable.«x86_64-tables».Represents
    (self : EdwardsBasepointTable.«x86_64-tables») (P : curve25519.edwards.Point) : Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (8 * i) • P)

/-- Row `i` of the radix-`16` table is the lookup table of `2^(8 i) • P`. -/
@[expose] def EdwardsBasepointTable.«i686-tables».Represents
    (self : EdwardsBasepointTable.«i686-tables») (P : curve25519.edwards.Point) : Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (8 * i) • P)

/-- Row `i` of the radix-`32` table is the lookup table of `2^(10 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix32.«x86_64-tables».Represents
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (10 * i) • P)

/-- Row `i` of the radix-`32` table is the lookup table of `2^(10 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix32.«i686-tables».Represents
    (self : EdwardsBasepointTableRadix32.«i686-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (10 * i) • P)

/-- Row `i` of the radix-`64` table is the lookup table of `2^(12 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix64.«x86_64-tables».Represents
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (12 * i) • P)

/-- Row `i` of the radix-`64` table is the lookup table of `2^(12 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix64.«i686-tables».Represents
    (self : EdwardsBasepointTableRadix64.«i686-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (12 * i) • P)

/-- Row `i` of the radix-`128` table is the lookup table of `2^(14 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix128.«x86_64-tables».Represents
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (14 * i) • P)

/-- Row `i` of the radix-`128` table is the lookup table of `2^(14 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix128.«i686-tables».Represents
    (self : EdwardsBasepointTableRadix128.«i686-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (14 * i) • P)

/-- Row `i` of the radix-`256` table is the lookup table of `2^(16 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix256.«x86_64-tables».Represents
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (16 * i) • P)

/-- Row `i` of the radix-`256` table is the lookup table of `2^(16 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix256.«i686-tables».Represents
    (self : EdwardsBasepointTableRadix256.«i686-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (16 * i) • P)

/-- A table represents `P` iff it is a table (`IsTable`) of the point `P`. -/
theorem EdwardsBasepointTable.«x86_64-tables».represents_iff (self :
    EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) : self.Represents P ↔ self.IsTable ∧ self.point = P := by
  have hpoint : self.Represents P → self.point = P := fun h => by
    have := (h 0 (by decide) 0 (by decide)).2
    simpa [EdwardsBasepointTable.«x86_64-tables».point] using this
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, hpoint h⟩
    rw [hpoint h]
    exact h i hi j hj
  · rintro ⟨h, rfl⟩ i hi j hj
    exact h i hi j hj

/-- A table represents `P` iff it is a table (`IsTable`) of the point `P`. -/
theorem EdwardsBasepointTable.«i686-tables».represents_iff (self :
    EdwardsBasepointTable.«i686-tables»)
    (P : curve25519.edwards.Point) : self.Represents P ↔ self.IsTable ∧ self.point = P := by
  have hpoint : self.Represents P → self.point = P := fun h => by
    have := (h 0 (by decide) 0 (by decide)).2
    simpa [EdwardsBasepointTable.«i686-tables».point] using this
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, hpoint h⟩
    rw [hpoint h]
    exact h i hi j hj
  · rintro ⟨h, rfl⟩ i hi j hj
    exact h i hi j hj

/-- A table represents `P` iff it is a table (`IsTable`) of the point `P`. -/
theorem EdwardsBasepointTableRadix32.«x86_64-tables».represents_iff (self :
    EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) : self.Represents P ↔ self.IsTable ∧ self.point = P := by
  have hpoint : self.Represents P → self.point = P := fun h => by
    have := (h 0 (by decide) 0 (by decide)).2
    simpa [EdwardsBasepointTableRadix32.«x86_64-tables».point] using this
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, hpoint h⟩
    rw [hpoint h]
    exact h i hi j hj
  · rintro ⟨h, rfl⟩ i hi j hj
    exact h i hi j hj

/-- A table represents `P` iff it is a table (`IsTable`) of the point `P`. -/
theorem EdwardsBasepointTableRadix32.«i686-tables».represents_iff (self :
    EdwardsBasepointTableRadix32.«i686-tables»)
    (P : curve25519.edwards.Point) : self.Represents P ↔ self.IsTable ∧ self.point = P := by
  have hpoint : self.Represents P → self.point = P := fun h => by
    have := (h 0 (by decide) 0 (by decide)).2
    simpa [EdwardsBasepointTableRadix32.«i686-tables».point] using this
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, hpoint h⟩
    rw [hpoint h]
    exact h i hi j hj
  · rintro ⟨h, rfl⟩ i hi j hj
    exact h i hi j hj

/-- A table represents `P` iff it is a table (`IsTable`) of the point `P`. -/
theorem EdwardsBasepointTableRadix64.«x86_64-tables».represents_iff (self :
    EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) : self.Represents P ↔ self.IsTable ∧ self.point = P := by
  have hpoint : self.Represents P → self.point = P := fun h => by
    have := (h 0 (by decide) 0 (by decide)).2
    simpa [EdwardsBasepointTableRadix64.«x86_64-tables».point] using this
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, hpoint h⟩
    rw [hpoint h]
    exact h i hi j hj
  · rintro ⟨h, rfl⟩ i hi j hj
    exact h i hi j hj

/-- A table represents `P` iff it is a table (`IsTable`) of the point `P`. -/
theorem EdwardsBasepointTableRadix64.«i686-tables».represents_iff (self :
    EdwardsBasepointTableRadix64.«i686-tables»)
    (P : curve25519.edwards.Point) : self.Represents P ↔ self.IsTable ∧ self.point = P := by
  have hpoint : self.Represents P → self.point = P := fun h => by
    have := (h 0 (by decide) 0 (by decide)).2
    simpa [EdwardsBasepointTableRadix64.«i686-tables».point] using this
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, hpoint h⟩
    rw [hpoint h]
    exact h i hi j hj
  · rintro ⟨h, rfl⟩ i hi j hj
    exact h i hi j hj

/-- A table represents `P` iff it is a table (`IsTable`) of the point `P`. -/
theorem EdwardsBasepointTableRadix128.«x86_64-tables».represents_iff (self :
    EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) : self.Represents P ↔ self.IsTable ∧ self.point = P := by
  have hpoint : self.Represents P → self.point = P := fun h => by
    have := (h 0 (by decide) 0 (by decide)).2
    simpa [EdwardsBasepointTableRadix128.«x86_64-tables».point] using this
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, hpoint h⟩
    rw [hpoint h]
    exact h i hi j hj
  · rintro ⟨h, rfl⟩ i hi j hj
    exact h i hi j hj

/-- A table represents `P` iff it is a table (`IsTable`) of the point `P`. -/
theorem EdwardsBasepointTableRadix128.«i686-tables».represents_iff (self :
    EdwardsBasepointTableRadix128.«i686-tables»)
    (P : curve25519.edwards.Point) : self.Represents P ↔ self.IsTable ∧ self.point = P := by
  have hpoint : self.Represents P → self.point = P := fun h => by
    have := (h 0 (by decide) 0 (by decide)).2
    simpa [EdwardsBasepointTableRadix128.«i686-tables».point] using this
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, hpoint h⟩
    rw [hpoint h]
    exact h i hi j hj
  · rintro ⟨h, rfl⟩ i hi j hj
    exact h i hi j hj

/-- A table represents `P` iff it is a table (`IsTable`) of the point `P`. -/
theorem EdwardsBasepointTableRadix256.«x86_64-tables».represents_iff (self :
    EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) : self.Represents P ↔ self.IsTable ∧ self.point = P := by
  have hpoint : self.Represents P → self.point = P := fun h => by
    have := (h 0 (by decide) 0 (by decide)).2
    simpa [EdwardsBasepointTableRadix256.«x86_64-tables».point] using this
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, hpoint h⟩
    rw [hpoint h]
    exact h i hi j hj
  · rintro ⟨h, rfl⟩ i hi j hj
    exact h i hi j hj

/-- A table represents `P` iff it is a table (`IsTable`) of the point `P`. -/
theorem EdwardsBasepointTableRadix256.«i686-tables».represents_iff (self :
    EdwardsBasepointTableRadix256.«i686-tables»)
    (P : curve25519.edwards.Point) : self.Represents P ↔ self.IsTable ∧ self.point = P := by
  have hpoint : self.Represents P → self.point = P := fun h => by
    have := (h 0 (by decide) 0 (by decide)).2
    simpa [EdwardsBasepointTableRadix256.«i686-tables».point] using this
  constructor
  · intro h
    refine ⟨fun i hi j hj => ?_, hpoint h⟩
    rw [hpoint h]
    exact h i hi j hj
  · rintro ⟨h, rfl⟩ i hi j hj
    exact h i hi j hj

end edwards

namespace backend.serial.scalar_mul.precomputed_straus

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».Represents
    (self : VartimePrecomputedStraus.«x86_64-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«i686-tables».Represents
    (self : VartimePrecomputedStraus.«i686-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».Represents
    (self : VartimePrecomputedStraus.«x86_64-no-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«i686-no-tables».Represents
    (self : VartimePrecomputedStraus.«i686-no-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

end backend.serial.scalar_mul.precomputed_straus

namespace backend

/-- The serial precomputation inside the backend enum represents `ps`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».Represents :
    VartimePrecomputedStraus.«x86_64-tables» → List curve25519.edwards.Point → Prop
  | .Scalar pre, ps => pre.Represents ps

/-- The serial precomputation inside the backend enum represents `ps`. -/
@[expose] def VartimePrecomputedStraus.«i686-tables».Represents :
    VartimePrecomputedStraus.«i686-tables» → List curve25519.edwards.Point → Prop
  | .Scalar pre, ps => pre.Represents ps

/-- The serial precomputation inside the backend enum represents `ps`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».Represents :
    VartimePrecomputedStraus.«x86_64-no-tables» → List curve25519.edwards.Point → Prop
  | .Scalar pre, ps => pre.Represents ps

/-- The serial precomputation inside the backend enum represents `ps`. -/
@[expose] def VartimePrecomputedStraus.«i686-no-tables».Represents :
    VartimePrecomputedStraus.«i686-no-tables» → List curve25519.edwards.Point → Prop
  | .Scalar pre, ps => pre.Represents ps

/-- A precomputation represents `ps` iff it is valid (`IsValid`) with the static points `ps`. -/
theorem VartimePrecomputedStraus.«x86_64-tables».represents_iff (self :
    VartimePrecomputedStraus.«x86_64-tables»)
    (ps : List curve25519.edwards.Point) :
    self.Represents ps ↔ self.IsValid ∧ self.points = ps := by
  rcases self with ⟨pre⟩
  simp only [VartimePrecomputedStraus.«x86_64-tables».Represents,
      VartimePrecomputedStraus.«x86_64-tables».IsValid,
      VartimePrecomputedStraus.«x86_64-tables».points,
    serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-tables».Represents]
  constructor
  · intro h
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
    have h0 : ∀ n (h₁ : n < pre.static_lookup_tables.val.length),
        PointRepr.toPoint (pre.static_lookup_tables.val.get ⟨n, h₁⟩)[0]! =
          ps.get ⟨n, hlen ▸ h₁⟩ := fun n h₁ => by
      simpa using (hget n h₁ (hlen ▸ h₁) 0 (by decide)).2
    refine ⟨fun n hn k hk => ?_, ?_⟩
    · have hn' : n < pre.static_lookup_tables.val.length := hn
      have := hget n hn' (hlen ▸ hn') k hk
      simp only [List.get_eq_getElem] at this h0
      simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos
          pre.static_lookup_tables.val n hn']
      rw [h0 n hn']
      exact this
    · apply List.ext_get (by simp [hlen])
      intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_map] at h0 ⊢
      exact h0 n (by simpa using h₁)
  · rintro ⟨h, rfl⟩
    refine List.forall₂_iff_get.mpr ⟨by simp, fun n h₁ h₂ k hk => ?_⟩
    have := h n h₁ k hk
    simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos pre.static_lookup_tables.val
        n h₁]
      at this
    simpa using this

/-- A precomputation represents `ps` iff it is valid (`IsValid`) with the static points `ps`. -/
theorem VartimePrecomputedStraus.«i686-tables».represents_iff (self :
    VartimePrecomputedStraus.«i686-tables»)
    (ps : List curve25519.edwards.Point) :
    self.Represents ps ↔ self.IsValid ∧ self.points = ps := by
  rcases self with ⟨pre⟩
  simp only [VartimePrecomputedStraus.«i686-tables».Represents,
      VartimePrecomputedStraus.«i686-tables».IsValid, VartimePrecomputedStraus.«i686-tables».points,
    serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«i686-tables».Represents]
  constructor
  · intro h
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
    have h0 : ∀ n (h₁ : n < pre.static_lookup_tables.val.length),
        PointRepr.toPoint (pre.static_lookup_tables.val.get ⟨n, h₁⟩)[0]! =
          ps.get ⟨n, hlen ▸ h₁⟩ := fun n h₁ => by
      simpa using (hget n h₁ (hlen ▸ h₁) 0 (by decide)).2
    refine ⟨fun n hn k hk => ?_, ?_⟩
    · have hn' : n < pre.static_lookup_tables.val.length := hn
      have := hget n hn' (hlen ▸ hn') k hk
      simp only [List.get_eq_getElem] at this h0
      simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos
          pre.static_lookup_tables.val n hn']
      rw [h0 n hn']
      exact this
    · apply List.ext_get (by simp [hlen])
      intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_map] at h0 ⊢
      exact h0 n (by simpa using h₁)
  · rintro ⟨h, rfl⟩
    refine List.forall₂_iff_get.mpr ⟨by simp, fun n h₁ h₂ k hk => ?_⟩
    have := h n h₁ k hk
    simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos pre.static_lookup_tables.val
        n h₁]
      at this
    simpa using this

/-- A precomputation represents `ps` iff it is valid (`IsValid`) with the static points `ps`. -/
theorem VartimePrecomputedStraus.«x86_64-no-tables».represents_iff (self :
    VartimePrecomputedStraus.«x86_64-no-tables»)
    (ps : List curve25519.edwards.Point) :
    self.Represents ps ↔ self.IsValid ∧ self.points = ps := by
  rcases self with ⟨pre⟩
  simp only [VartimePrecomputedStraus.«x86_64-no-tables».Represents,
      VartimePrecomputedStraus.«x86_64-no-tables».IsValid,
      VartimePrecomputedStraus.«x86_64-no-tables».points,
    serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-no-tables».Represents]
  constructor
  · intro h
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
    have h0 : ∀ n (h₁ : n < pre.static_lookup_tables.val.length),
        PointRepr.toPoint (pre.static_lookup_tables.val.get ⟨n, h₁⟩)[0]! =
          ps.get ⟨n, hlen ▸ h₁⟩ := fun n h₁ => by
      simpa using (hget n h₁ (hlen ▸ h₁) 0 (by decide)).2
    refine ⟨fun n hn k hk => ?_, ?_⟩
    · have hn' : n < pre.static_lookup_tables.val.length := hn
      have := hget n hn' (hlen ▸ hn') k hk
      simp only [List.get_eq_getElem] at this h0
      simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos
          pre.static_lookup_tables.val n hn']
      rw [h0 n hn']
      exact this
    · apply List.ext_get (by simp [hlen])
      intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_map] at h0 ⊢
      exact h0 n (by simpa using h₁)
  · rintro ⟨h, rfl⟩
    refine List.forall₂_iff_get.mpr ⟨by simp, fun n h₁ h₂ k hk => ?_⟩
    have := h n h₁ k hk
    simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos pre.static_lookup_tables.val
        n h₁]
      at this
    simpa using this

/-- A precomputation represents `ps` iff it is valid (`IsValid`) with the static points `ps`. -/
theorem VartimePrecomputedStraus.«i686-no-tables».represents_iff (self :
    VartimePrecomputedStraus.«i686-no-tables»)
    (ps : List curve25519.edwards.Point) :
    self.Represents ps ↔ self.IsValid ∧ self.points = ps := by
  rcases self with ⟨pre⟩
  simp only [VartimePrecomputedStraus.«i686-no-tables».Represents,
      VartimePrecomputedStraus.«i686-no-tables».IsValid,
      VartimePrecomputedStraus.«i686-no-tables».points,
    serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«i686-no-tables».Represents]
  constructor
  · intro h
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
    have h0 : ∀ n (h₁ : n < pre.static_lookup_tables.val.length),
        PointRepr.toPoint (pre.static_lookup_tables.val.get ⟨n, h₁⟩)[0]! =
          ps.get ⟨n, hlen ▸ h₁⟩ := fun n h₁ => by
      simpa using (hget n h₁ (hlen ▸ h₁) 0 (by decide)).2
    refine ⟨fun n hn k hk => ?_, ?_⟩
    · have hn' : n < pre.static_lookup_tables.val.length := hn
      have := hget n hn' (hlen ▸ hn') k hk
      simp only [List.get_eq_getElem] at this h0
      simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos
          pre.static_lookup_tables.val n hn']
      rw [h0 n hn']
      exact this
    · apply List.ext_get (by simp [hlen])
      intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_map] at h0 ⊢
      exact h0 n (by simpa using h₁)
  · rintro ⟨h, rfl⟩
    refine List.forall₂_iff_get.mpr ⟨by simp, fun n h₁ h₂ k hk => ?_⟩
    have := h n h₁ k hk
    simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos pre.static_lookup_tables.val
        n h₁]
      at this
    simpa using this

end backend

end Curve25519Dalek
