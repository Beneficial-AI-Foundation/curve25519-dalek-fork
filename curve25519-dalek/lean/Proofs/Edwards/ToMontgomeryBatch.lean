/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Montgomery
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Montgomery
public import Proofs.Field.InvertBatchAlloc
import Proofs.Helpers.EdwardsMontgomery
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Helpers.Backend.U32.Bytes
import Proofs.Helpers.Backend.U64.Bytes
public section

/-! # `EdwardsPoint::to_montgomery_batch`

The denominators `Z - Y` are inverted in one batch (`invert_batch_alloc`, which leaves zeros in
place, so `Z = Y` gives `u = 0` as in `to_montgomery`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.Backend

variable (B : Backend)

open ControlFlow

/-- `to_montgomery_batch_loop0.body` over a backend: the coordinates `Z`, `Y` of a point by
`Zf`, `Yf`. -/
@[expose] def tmbLoop0Body {E : Type} (Zf Yf : E → B.F) (eds : Slice E) (n : Usize)
    (denominators : alloc.vec.Vec B.F) (i : Usize) :
    Result (ControlFlow ((alloc.vec.Vec B.F) × Usize) (alloc.vec.Vec B.F)) := do
  if i < n
  then
    let ep ← Slice.index_usize eds i
    let fe ← B.sub (Zf ep) (Yf ep)
    let denominators1 ← alloc.vec.Vec.push denominators fe
    let i1 ← i + 1#usize
    ok (cont (denominators1, i1))
  else ok (done denominators)

/-- `to_montgomery_batch_loop0` over a backend. -/
@[expose] def tmbLoop0 {E : Type} (Zf Yf : E → B.F) (eds : Slice E) (n : Usize)
    (denominators : alloc.vec.Vec B.F) (i : Usize) : Result (alloc.vec.Vec B.F) := do
  loop (fun (denominators1, i1) => B.tmbLoop0Body Zf Yf eds n denominators1 i1)
    (denominators, i)

/-- `to_montgomery_batch_loop1.body` over a backend. -/
@[expose] def tmbLoop1Body {E : Type} (Zf Yf : E → B.F) (eds : Slice E) (n : Usize)
    (denominators : alloc.vec.Vec B.F) (ret : alloc.vec.Vec montgomery.MontgomeryPoint)
    (i : Usize) :
    Result (ControlFlow ((alloc.vec.Vec montgomery.MontgomeryPoint) × Usize)
      (alloc.vec.Vec montgomery.MontgomeryPoint)) := do
  if i < n
  then
    let ep ← Slice.index_usize eds i
    let fe ← B.add (Zf ep) (Yf ep)
    let fe1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice B.F) denominators i
    let u ← B.mul fe fe1
    let a ← B.toBytes u
    let ret1 ← alloc.vec.Vec.push ret a
    let i1 ← i + 1#usize
    ok (cont (ret1, i1))
  else ok (done ret)

/-- `to_montgomery_batch_loop1` over a backend. -/
@[expose] def tmbLoop1 {E : Type} (Zf Yf : E → B.F) (eds : Slice E) (n : Usize)
    (denominators : alloc.vec.Vec B.F) (ret : alloc.vec.Vec montgomery.MontgomeryPoint)
    (i : Usize) : Result (alloc.vec.Vec montgomery.MontgomeryPoint) := do
  loop (fun (ret1, i1) => B.tmbLoop1Body Zf Yf eds n denominators ret1 i1) (ret, i)

/-- `EdwardsPoint::to_montgomery_batch` over a backend. -/
@[expose] def toMontgomeryBatch {E : Type} (Zf Yf : E → B.F) (eds : Slice E) :
    Result (alloc.vec.Vec montgomery.MontgomeryPoint) := do
  let n := Slice.len eds
  let denominators := alloc.vec.Vec.with_capacity B.F n
  let denominators1 ← B.tmbLoop0 Zf Yf eds n denominators 0#usize
  let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut denominators1)
  let s1 ← B.invertBatchAlloc s
  let ret := alloc.vec.Vec.with_capacity montgomery.MontgomeryPoint n
  let denominators2 := deref_mut_back s1
  B.tmbLoop1 Zf Yf eds n denominators2 ret 0#usize

open scoped Helpers.IndexStep in
/-- The first loop of `to_montgomery_batch`: the denominators `Z - Y`. -/
private theorem tmbLoop0_spec (hsub : B.SubSpec) {E : Type} [Inhabited E] (Zf Yf : E → B.F)
    (eds : Slice E) (heds : ∀ k < eds.length, B.Red (Zf eds[k]!) ∧ B.Red (Yf eds[k]!))
    (n : Usize) (hn : n.val = eds.length) (den : alloc.vec.Vec B.F) (i : Usize)
    (hi : i.val ≤ n.val) (hlen : den.length = i.val)
    (hden : ∀ k < i.val,
      B.toField den[k]! = B.toField (Zf eds[k]!) - B.toField (Yf eds[k]!) ∧ B.Red den[k]!) :
    B.tmbLoop0 Zf Yf eds n den i ⦃ (r : alloc.vec.Vec B.F) =>
      r.length = eds.length ∧ ∀ k < eds.length,
        B.toField r[k]! = B.toField (Zf eds[k]!) - B.toField (Yf eds[k]!) ∧ B.Red r[k]! ⦄ := by
  unfold tmbLoop0
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (d, i') => i'.val ≤ n.val ∧ d.length = i'.val ∧ ∀ k < i'.val,
      B.toField d[k]! = B.toField (Zf eds[k]!) - B.toField (Yf eds[k]!) ∧ B.Red d[k]!)
  · rintro ⟨d, i'⟩ ⟨hi', hl, hd⟩
    unfold tmbLoop0Body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      step as ⟨ep, hep⟩
      obtain ⟨hZ, hY⟩ := hep ▸ heds i'.val (by scalar_tac)
      step with hsub (Zf ep) (Yf ep) (B.red_mulIn hZ) (B.red_mulIn hY) as ⟨fe, hfe, hfeb⟩
      step as ⟨d1, hd1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hd1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
          B.toField x = B.toField (Zf eds[k]!) - B.toField (Yf eds[k]!) ∧ B.Red x)
        hd1 (hl ▸ hd) ⟨by rw [hfe, hep, hl], hfeb⟩
    · simp only [hlt, ite_false, WP.spec_ok]
      have hin : i'.val = eds.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ hd⟩
  · exact ⟨hi, hlen, hden⟩

open scoped Helpers.IndexStep in
/-- The second loop of `to_montgomery_batch`: `u = (Z + Y) · (Z - Y)⁻¹` as bytes. -/
private theorem tmbLoop1_spec (hadd : B.AddSpec) (hmul : B.MulSpec) (htb : B.ToBytesSpec)
    {E : Type} [Inhabited E] (Zf Yf : E → B.F) (eds : Slice E)
    (heds : ∀ k < eds.length, B.Red (Zf eds[k]!) ∧ B.Red (Yf eds[k]!)) (n : Usize)
    (hn : n.val = eds.length) (den : alloc.vec.Vec B.F) (hdenlen : den.length = eds.length)
    (hden : ∀ k < eds.length,
      B.toField den[k]! = (B.toField (Zf eds[k]!) - B.toField (Yf eds[k]!))⁻¹ ∧ B.Red den[k]!)
    (ret : alloc.vec.Vec montgomery.MontgomeryPoint) (i : Usize) (hi : i.val ≤ n.val)
    (hlen : ret.length = i.val)
    (hret : ∀ k < i.val, ret[k]!.asNat = ((B.toField (Zf eds[k]!) + B.toField (Yf eds[k]!)) /
      (B.toField (Zf eds[k]!) - B.toField (Yf eds[k]!))).val) :
    B.tmbLoop1 Zf Yf eds n den ret i
      ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
        r.length = eds.length ∧ ∀ k < eds.length, r[k]!.asNat =
          ((B.toField (Zf eds[k]!) + B.toField (Yf eds[k]!)) /
            (B.toField (Zf eds[k]!) - B.toField (Yf eds[k]!))).val ⦄ := by
  unfold tmbLoop1
  apply loop.spec_decr_nat (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (d, i') => i'.val ≤ n.val ∧ d.length = i'.val ∧ ∀ k < i'.val,
      d[k]!.asNat = ((B.toField (Zf eds[k]!) + B.toField (Yf eds[k]!)) /
        (B.toField (Zf eds[k]!) - B.toField (Yf eds[k]!))).val)
  · rintro ⟨d, i'⟩ ⟨hi', hl, hd⟩
    unfold tmbLoop1Body
    by_cases hlt : i' < n
    · simp only [hlt, ite_true]
      step as ⟨ep, hep⟩
      obtain ⟨hZ, hY⟩ := hep ▸ heds i'.val (by scalar_tac)
      step with hadd (Zf ep) (Yf ep) hZ hY as ⟨fe, hfe, hfeb⟩
      have hik : i'.val < eds.length := by scalar_tac
      obtain ⟨hdk, hdkb⟩ := hden i'.val hik
      have hfe1' : den.val[i'.val]! = den[i'.val]! := rfl
      step as ⟨fe1, hfe1⟩
      have hfe1e : fe1 = den[i'.val]! := by
        rw [hfe1, ← hfe1', getElem!_pos]
      rw [← hfe1e] at hdk hdkb
      step with hmul fe fe1 (B.sum2_mulIn hfeb) (B.red_mulIn hdkb) as ⟨u, hu, hub⟩
      step with htb u as ⟨a, ha⟩
      step as ⟨d1, hd1⟩
      step as ⟨i1, hi1⟩
      refine ⟨by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hd1, hl, hi1], ?_,
        by scalar_tac⟩
      rw [hi1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x => x.asNat =
        ((B.toField (Zf eds[k]!) + B.toField (Yf eds[k]!)) /
          (B.toField (Zf eds[k]!) - B.toField (Yf eds[k]!))).val)
        hd1 (hl ▸ hd) ?_
      rw [montgomery.MontgomeryPoint.asNat_def, ha, hu, hdk, hfe, hep, hl, div_eq_mul_inv]
    · simp only [hlt, ite_false, WP.spec_ok]
      have hin : i'.val = eds.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ hd⟩
  · exact ⟨hi, hlen, hret⟩

/-- `toMontgomeryBatch`: entry `i` is the canonical bytes of `(Z + Y) / (Z - Y)` of point `i`
(`0` if `Z = Y`). -/
theorem toMontgomeryBatch_spec (hadd : B.AddSpec) (hsub : B.SubSpec) (hmul : B.MulSpec)
    (htb : B.ToBytesSpec) (hinv : B.InvertBatchAllocSpec) {E : Type} [Inhabited E]
    (Zf Yf : E → B.F) (eds : Slice E)
    (heds : ∀ i < eds.length, B.Red (Zf eds[i]!) ∧ B.Red (Yf eds[i]!)) :
    B.toMontgomeryBatch Zf Yf eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧ ∀ i < eds.length, r[i]!.asNat =
        ((B.toField (Zf eds[i]!) + B.toField (Yf eds[i]!)) /
          (B.toField (Zf eds[i]!) - B.toField (Yf eds[i]!))).val ⦄ := by
  unfold toMontgomeryBatch
  step with B.tmbLoop0_spec hsub Zf Yf eds heds _ (Slice.len_val eds)
    (alloc.vec.Vec.with_capacity B.F (Slice.len eds)) 0#usize (by scalar_tac) (by rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) as ⟨d1, hd1len, hd1⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  step with hinv d1.slice (fun k hk => by
      rw [alloc.vec.Vec.getElem!_slice]
      exact (hd1 k (hd1len ▸ hk)).2) as ⟨s1, hs1len, hs1⟩
  have hs1' : ∀ k < eds.length,
      B.toField ({ slice := s1 } : alloc.vec.Vec B.F)[k]! =
        (B.toField (Zf eds[k]!) - B.toField (Yf eds[k]!))⁻¹ ∧
      B.Red ({ slice := s1 } : alloc.vec.Vec B.F)[k]! := by
    intro k hk
    obtain ⟨hdk, -⟩ := hd1 k hk
    rw [alloc.vec.Vec.getElem!_mk, ← hdk, ← alloc.vec.Vec.getElem!_slice]
    exact hs1 k (by rw [← hd1len] at hk; exact hk)
  step with B.tmbLoop1_spec hadd hmul htb Zf Yf eds heds _ (Slice.len_val eds) _
    (hs1len.trans hd1len) hs1' (alloc.vec.Vec.with_capacity montgomery.MontgomeryPoint
      (Slice.len eds)) 0#usize (by scalar_tac) (by rfl) (fun k hk => absurd hk (Nat.not_lt_zero k))
    as ⟨r, hrlen, hr⟩
  exact ⟨hrlen, hr⟩

end Curve25519Dalek.Backend

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

private theorem to_montgomery_batch_eq (eds : Slice EdwardsPoint.«x86_64-tables») :
    to_montgomery_batch eds = Backend.U64.toMontgomeryBatch (·.Z) (·.Y) eds := rfl

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is the canonical bytes of
`(Z + Y) / (Z - Y)` of point `i` (`0` if `Z = Y`); limbs `< 2^52`. -/
@[step]
theorem to_montgomery_batch_spec (eds : Slice EdwardsPoint.«x86_64-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 52) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧ ∀ i < eds.length, r[i]!.asNat =
        ((eds[i]!.Z.toField + eds[i]!.Y.toField) /
          (eds[i]!.Z.toField - eds[i]!.Y.toField)).val ⦄ := by
  rw [to_montgomery_batch_eq]
  exact Backend.toMontgomeryBatch_spec Backend.U64 Backend.U64.add_spec Backend.U64.sub_spec
    Backend.U64.mul_spec Backend.U64.to_bytes_spec Backend.U64.invertBatchAlloc_spec _ _ eds
    fun i hi => by obtain ⟨-, hY, hZ, -⟩ := heds i hi; exact ⟨hZ, hY⟩

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
theorem to_montgomery_batch_spec_point (eds : Slice EdwardsPoint.«x86_64-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 52) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.asNat = encodeU (edwardsToMontgomery eds[i]!.toPoint).u ⦄ :=
  spec_mono (to_montgomery_batch_spec eds heds) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, EdwardsPoint.«x86_64-tables».u_edwardsToMontgomery (heds_on i hi)]
    rfl⟩

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

private theorem to_montgomery_batch_eq (eds : Slice EdwardsPoint.«i686-tables») :
    to_montgomery_batch eds = Backend.U32.toMontgomeryBatch (·.Z) (·.Y) eds := rfl

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is the canonical bytes of
`(Z + Y) / (Z - Y)` of point `i` (`0` if `Z = Y`); limbs `< 2^26`. -/
@[step]
theorem to_montgomery_batch_spec (eds : Slice EdwardsPoint.«i686-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 26) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧ ∀ i < eds.length, r[i]!.asNat =
        ((eds[i]!.Z.toField + eds[i]!.Y.toField) /
          (eds[i]!.Z.toField - eds[i]!.Y.toField)).val ⦄ := by
  rw [to_montgomery_batch_eq]
  exact Backend.toMontgomeryBatch_spec Backend.U32 Backend.U32.add_spec Backend.U32.sub_spec
    Backend.U32.mul_spec Backend.U32.to_bytes_spec Backend.U32.invertBatchAlloc_spec _ _ eds
    fun i hi => by obtain ⟨-, hY, hZ, -⟩ := heds i hi; exact ⟨hZ, hY⟩

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
theorem to_montgomery_batch_spec_point (eds : Slice EdwardsPoint.«i686-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 26) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.asNat = encodeU (edwardsToMontgomery eds[i]!.toPoint).u ⦄ :=
  spec_mono (to_montgomery_batch_spec eds heds) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, EdwardsPoint.«i686-tables».u_edwardsToMontgomery (heds_on i hi)]
    rfl⟩

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

private theorem to_montgomery_batch_eq (eds : Slice EdwardsPoint.«x86_64-no-tables») :
    to_montgomery_batch eds = Backend.U64.toMontgomeryBatch (·.Z) (·.Y) eds := rfl

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is the canonical bytes of
`(Z + Y) / (Z - Y)` of point `i` (`0` if `Z = Y`); limbs `< 2^52`. -/
@[step]
theorem to_montgomery_batch_spec (eds : Slice EdwardsPoint.«x86_64-no-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 52) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧ ∀ i < eds.length, r[i]!.asNat =
        ((eds[i]!.Z.toField + eds[i]!.Y.toField) /
          (eds[i]!.Z.toField - eds[i]!.Y.toField)).val ⦄ := by
  rw [to_montgomery_batch_eq]
  exact Backend.toMontgomeryBatch_spec Backend.U64 Backend.U64.add_spec Backend.U64.sub_spec
    Backend.U64.mul_spec Backend.U64.to_bytes_spec Backend.U64.invertBatchAlloc_spec _ _ eds
    fun i hi => by obtain ⟨-, hY, hZ, -⟩ := heds i hi; exact ⟨hZ, hY⟩

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
theorem to_montgomery_batch_spec_point (eds : Slice EdwardsPoint.«x86_64-no-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 52) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.asNat = encodeU (edwardsToMontgomery eds[i]!.toPoint).u ⦄ :=
  spec_mono (to_montgomery_batch_spec eds heds) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, EdwardsPoint.«x86_64-no-tables».u_edwardsToMontgomery (heds_on i hi)]
    rfl⟩

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

private theorem to_montgomery_batch_eq (eds : Slice EdwardsPoint.«i686-no-tables») :
    to_montgomery_batch eds = Backend.U32.toMontgomeryBatch (·.Z) (·.Y) eds := rfl

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is the canonical bytes of
`(Z + Y) / (Z - Y)` of point `i` (`0` if `Z = Y`); limbs `< 2^26`. -/
@[step]
theorem to_montgomery_batch_spec (eds : Slice EdwardsPoint.«i686-no-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 26) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧ ∀ i < eds.length, r[i]!.asNat =
        ((eds[i]!.Z.toField + eds[i]!.Y.toField) /
          (eds[i]!.Z.toField - eds[i]!.Y.toField)).val ⦄ := by
  rw [to_montgomery_batch_eq]
  exact Backend.toMontgomeryBatch_spec Backend.U32 Backend.U32.add_spec Backend.U32.sub_spec
    Backend.U32.mul_spec Backend.U32.to_bytes_spec Backend.U32.invertBatchAlloc_spec _ _ eds
    fun i hi => by obtain ⟨-, hY, hZ, -⟩ := heds i hi; exact ⟨hZ, hY⟩

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
theorem to_montgomery_batch_spec_point (eds : Slice EdwardsPoint.«i686-no-tables»)
    (heds : ∀ i < eds.length, eds[i]!.LimbsLt 26) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.asNat = encodeU (edwardsToMontgomery eds[i]!.toPoint).u ⦄ :=
  spec_mono (to_montgomery_batch_spec eds heds) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, EdwardsPoint.«i686-no-tables».u_edwardsToMontgomery (heds_on i hi)]
    rfl⟩

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
