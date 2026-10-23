/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Ristretto.Map
public import Defs.CurveModels
public import Defs.Edwards
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.U64.Constants.EdwardsD
import Proofs.Backend.Serial.U64.Constants.EdwardsDMinusOneSquared
import Proofs.Backend.Serial.U64.Constants.MinusOne
import Proofs.Backend.Serial.U64.Constants.OneMinusEdwardsDSquared
import Proofs.Backend.Serial.U64.Constants.SqrtAdMinusOne
import Proofs.Backend.Serial.U64.Constants.SqrtM1
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U64.Field.ConditionalNegate
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Field.IsNegative
import Proofs.Field.SqrtRatioI
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U32.Constants.EdwardsD
import Proofs.Backend.Serial.U32.Constants.EdwardsDMinusOneSquared
import Proofs.Backend.Serial.U32.Constants.MinusOne
import Proofs.Backend.Serial.U32.Constants.OneMinusEdwardsDSquared
import Proofs.Backend.Serial.U32.Constants.SqrtAdMinusOne
import Proofs.Backend.Serial.U32.Constants.SqrtM1
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.ConditionalAssign
import Proofs.Backend.Serial.U32.Field.ConditionalNegate
import Proofs.Backend.Serial.U32.Field.FromBytes
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Backend.Serial.U32.Field.Square
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Helpers.ToField2625
public section

/-! # The Ristretto Elligator map (`ristretto/elligator.rs`)

`elligator_ristretto_flavor` is RFC 9496 §4.3.4 `MAP` (`Ristretto.mapRep`) step by step, the
point `(w0 : w2 : w1 : w3)` being formed as a completed point; `map_to_curve` applies it to the
low `255` bits of the bytes, reduced modulo `p`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.ristretto.elligator

namespace «RistrettoPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `RistrettoPoint::elligator_ristretto_flavor`: RFC 9496's `MAP(r₀)`; limbs `< 2^54` in,
`< 2^52` out. -/
@[step]
theorem elligator_ristretto_flavor_spec (r_0 : FieldElement51) (hr_0 : r_0.LimbsLt 54) :
    elligator_ristretto_flavor r_0 ⦃ (r : RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep r_0.toField ∧ r.LimbsLt 52 ⦄ := by
  unfold elligator_ristretto_flavor
  step as ⟨fi, hfi, hfib⟩
  step as ⟨fd, hfd, hfdb⟩
  step as ⟨f1d, hf1d, hf1db⟩
  step as ⟨fd1, hfd1, hfd1b⟩
  step as ⟨c, hc, hcb⟩
  step as ⟨one, hone, honeb⟩
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨r, hr, hrb⟩
  step as ⟨fe5, hfe5⟩
  step as ⟨Ns, hNs, hNsb⟩
  step as ⟨fe6, hfe6, hfe6b⟩
  step as ⟨fe7, hfe7, hfe7b⟩
  step as ⟨fe8, hfe8⟩
  step as ⟨D, hD, hDb⟩
  step as ⟨sq, s, hsqv, hs0, hs1, hs2, hs3, hspar, hsb⟩
  step as ⟨sp, hsp, hspb⟩
  step as ⟨c1, hc1v, hc1⟩
  step as ⟨pos, hposv, hpos⟩
  step as ⟨sp1, hsp10, hsp11⟩
  step as ⟨c2, hc2v, hc2⟩
  step as ⟨s1, hs10, hs11⟩
  step as ⟨c3, hc30, hc31⟩
  have hsp1b : sp1.LimbsLt 52 := by
    rcases hposv with h | h
    · rw [hsp10 h]; exact hspb
    · exact (hsp11 h).2
  have hs1b : s1.LimbsLt 52 := by
    rcases hc2v with h | h
    · rw [hs10 h]; exact hsb
    · rw [hs11 h]; exact hsp1b
  have hc3b : c3.LimbsLt 52 := by
    rcases hc2v with h | h
    · rw [hc30 h]; exact limbs_lt_of_le (by decide) hcb
    · rw [hc31 h]; exact hrb
  step as ⟨fe9, hfe9, hfe9b⟩
  step as ⟨fe10, hfe10, hfe10b⟩
  step as ⟨fe11, hfe11, hfe11b⟩
  step as ⟨Nt, hNt, hNtb⟩
  step as ⟨ssq, hssq, hssqb⟩
  step as ⟨fe12, hfe12⟩
  step as ⟨fe13, hfe13, hfe13b⟩
  step with backend.serial.u64.constants.SQRT_AD_MINUS_ONE_spec_eq as ⟨fK, hfK, hfKb⟩
  step as ⟨fe15, hfe15, hfe15b⟩
  step as ⟨fe16, hfe16, hfe16b⟩
  step as ⟨fe17, hfe17⟩
  -- the constants
  have Fi : fi.toField = sqrtM1 := by rw [toField_def, hfi]
  have Fd : fd.toField = d := toField_eq_d_of_asNat hfd
  have F1d : f1d.toField = 1 - d ^ 2 := by rw [toField_def, hf1d, ZMod.natCast_zmod_val]
  have Fd1 : fd1.toField = (d - 1) ^ 2 := by rw [toField_def, hfd1, ZMod.natCast_zmod_val]
  have C : c.toField = -1 := by
    have h : ((c.asNat + 1 : ℕ) : ZMod p) = 0 := by rw [hc]; exact ZMod.natCast_self p
    push_cast at h
    rw [toField_def]
    linear_combination h
  have One : one.toField = 1 := toField_eq_one_of_asNat hone
  have K : fK.toField = sqrtAdMinusOne := by rw [toField_def, hfK]
  -- RFC 9496 §4.3.4 step by step
  set r' : ZMod p := sqrtM1 * r_0.toField ^ 2 with hr'
  have R : r.toField = r' := by rw [toField_mul_of_mod hr, Fi, toField_sq_of_mod hfe4]
  set u' : ZMod p := (r' + 1) * (oneMinusDSq : ZMod p) with hu'
  have U : Ns.toField = u' := by
    rw [toField_mul_of_mod hNs, toField_add_of_limbs hfe5, R, One, F1d, ← oneMinusDSq_eq]
  set v' : ZMod p := (-1 - r' * curve25519.d) * (r' + curve25519.d) with hv'
  have V : D.toField = v' := by
    rw [toField_mul_of_mod hD, toField_sub_of_mod hfe7, toField_mul_of_mod hfe6,
      toField_add_of_limbs hfe8, C, Fd, R]
    ring
  have SQ := sqrtRatioM1_eq_of_spec hs0 hs1 (fun h ⟨x, hx⟩ => hs2 h x hx) hs3 hspar
  rw [U, V] at SQ
  have S0 : s.toField = (sqrtRatioM1 u' v').2 := by rw [SQ]
  have SQ1 : sq = 1#u8 ↔ (sqrtRatioM1 u' v').1 = true := by rw [SQ]; simp
  have Sp : sp.toField = (sqrtRatioM1 u' v').2 * r_0.toField := by
    rw [toField_mul_of_mod hsp, S0]
  have Pos : pos = 1#u8 ↔ ¬ sp.toField.isNeg := by
    rw [hpos, ← eq_one_iff_isNeg_toField hc1]
    rcases hc1v with rfl | rfl <;> decide
  have Sp1 : sp1.toField = -((sqrtRatioM1 u' v').2 * r_0.toField).abs := by
    have h := eq_ite_of_choice hposv Pos (fun h => by rw [hsp10 h])
      (fun h => toField_neg_of_mod (hsp11 h).1)
    rw [h, ← Sp]
    by_cases hn : sp.toField.isNeg
    · rw [ite_eq_right (not_not.mpr hn), ZMod.abs_of_isNeg hn, neg_neg]
    · rw [ite_eq_left hn, ZMod.abs_of_not_isNeg hn]
  have C2 : c2 = 1#u8 ↔ ¬ (sqrtRatioM1 u' v').1 = true := by
    rw [hc2, ← SQ1]
    rcases hsqv with rfl | rfl <;> decide
  set S : ZMod p := if (sqrtRatioM1 u' v').1 then (sqrtRatioM1 u' v').2
    else -((sqrtRatioM1 u' v').2 * r_0.toField).abs with hS
  have S1 : s1.toField = S := by
    have h : s1.toField = if ¬ (sqrtRatioM1 u' v').1 = true then sp1.toField else s.toField :=
      eq_ite_of_choice hc2v C2 (fun h => by rw [hs10 h]) (fun h => by rw [hs11 h])
    rw [h, Sp1, S0, hS]
    by_cases hb : (sqrtRatioM1 u' v').1 = true
    · rw [ite_eq_right (not_not.mpr hb), ite_eq_left hb]
    · rw [ite_eq_left hb, ite_eq_right hb]
  set Cc : ZMod p := if (sqrtRatioM1 u' v').1 then -1 else r' with hCc
  have C3 : c3.toField = Cc := by
    have h : c3.toField = if ¬ (sqrtRatioM1 u' v').1 = true then r.toField else c.toField :=
      eq_ite_of_choice hc2v C2 (fun h => by rw [hc30 h]) (fun h => by rw [hc31 h])
    rw [h, C, R, hCc]
    by_cases hb : (sqrtRatioM1 u' v').1 = true
    · rw [ite_eq_right (not_not.mpr hb), ite_eq_left hb]
    · rw [ite_eq_left hb, ite_eq_right hb]
  set N : ZMod p := Cc * (r' - 1) * (dMinusOneSq : ZMod p) - v' with hN
  have NT : Nt.toField = N := by
    rw [toField_sub_of_mod hNt, toField_mul_of_mod hfe11, toField_mul_of_mod hfe10, C3,
      toField_sub_of_mod hfe9, R, One, Fd1, ← dMinusOneSq_eq, V]
  have X13 : fe13.toField = 2 * S * v' := by
    rw [toField_mul_of_mod hfe13, toField_add_of_limbs hfe12, S1, V]
    ring
  have Z15 : fe15.toField = N * sqrtAdMinusOne := by rw [toField_mul_of_mod hfe15, NT, K]
  have Y16 : fe16.toField = 1 - S ^ 2 := by
    rw [toField_sub_of_mod hfe16, One, toField_sq_of_mod hssq, S1]
  have T17 : fe17.toField = 1 + S ^ 2 := by
    rw [toField_add_of_limbs hfe17, One, toField_sq_of_mod hssq, S1]
  have hon : CompletedPoint.«x86_64-tables».OnCurve ⟨fe13, fe16, fe15, fe17⟩ := by
    rw [CompletedPoint.«x86_64-tables».onCurve_iff_equation]
    dsimp only
    rw [X13, Z15, Y16, T17]
    exact ⟨Ristretto.mapRep_den_ne_zero _, Ristretto.mapRep_one_add_sq_ne_zero _,
      Ristretto.mapRep_equation _⟩
  have hb : CompletedPoint.«x86_64-tables».LimbsLt 54 ⟨fe13, fe16, fe15, fe17⟩ :=
    ⟨limbs_lt_of_le (by decide) hfe13b, limbs_lt_of_le (by decide) hfe16b,
      limbs_lt_of_le (by decide) hfe15b,
      limbs_lt_of_le (by decide) (limbs_add_lt hfe17 (limbs_lt_of_le (by decide) honeb) hssqb)⟩
  step with «CompletedPointx86_64-tables».as_extended_spec_point _ hb hon as ⟨ep, h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  rw [h2]
  apply Point.ext
  · rw [CompletedPoint.«x86_64-tables».toPoint_x hon, Ristretto.mapRep_x]
    dsimp only
    rw [X13, Z15]
  · rw [CompletedPoint.«x86_64-tables».toPoint_y hon, Ristretto.mapRep_y]
    dsimp only
    rw [Y16, T17]

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the low `255` bits of the bytes, reduced
modulo `p` (`decodeU`); limbs `< 2^52`. -/
@[step]
theorem map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep (decodeU (bytes.asNat 8)) ∧ r.LimbsLt 52 ⦄ := by
  unfold map_to_curve
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2, toField_eq_decodeU_of_asNat_eq hfe], h3⟩

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `RistrettoPoint::elligator_ristretto_flavor`: RFC 9496's `MAP(r₀)`; limbs `< 2^27` in,
`< 2^26` out. -/
@[step]
theorem elligator_ristretto_flavor_spec (r_0 : FieldElement2625) (hr_0 : r_0.LimbsLt 27) :
    elligator_ristretto_flavor r_0 ⦃ (r : RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep r_0.toField ∧ r.LimbsLt 26 ⦄ := by
  unfold elligator_ristretto_flavor
  step as ⟨fi, hfi, hfib⟩
  step as ⟨fd, hfd, hfdb⟩
  step as ⟨f1d, hf1d, hf1db⟩
  step as ⟨fd1, hfd1, hfd1b⟩
  step as ⟨c, hc, hcb⟩
  step as ⟨one, hone, honeb⟩
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨r, hr, hrb⟩
  step as ⟨fe5, hfe5⟩
  step as ⟨Ns, hNs, hNsb⟩
  step as ⟨fe6, hfe6, hfe6b⟩
  step as ⟨fe7, hfe7, hfe7b⟩
  step as ⟨fe8, hfe8⟩
  step as ⟨D, hD, hDb⟩
  step as ⟨sq, s, hsqv, hs0, hs1, hs2, hs3, hspar, hsb⟩
  step as ⟨sp, hsp, hspb⟩
  step as ⟨c1, hc1v, hc1⟩
  step as ⟨pos, hposv, hpos⟩
  step as ⟨sp1, hsp10, hsp11⟩
  step as ⟨c2, hc2v, hc2⟩
  step as ⟨s1, hs10, hs11⟩
  step as ⟨c3, hc30, hc31⟩
  have hsp1b : sp1.LimbsLt 26 := by
    rcases hposv with h | h
    · rw [hsp10 h]; exact hspb
    · exact (hsp11 h).2
  have hs1b : s1.LimbsLt 26 := by
    rcases hc2v with h | h
    · rw [hs10 h]; exact hsb
    · rw [hs11 h]; exact hsp1b
  have hc3b : c3.LimbsLt 26 := by
    rcases hc2v with h | h
    · rw [hc30 h]; exact limbs_lt_of_le (by decide) hcb
    · rw [hc31 h]; exact hrb
  step as ⟨fe9, hfe9, hfe9b⟩
  step as ⟨fe10, hfe10, hfe10b⟩
  step as ⟨fe11, hfe11, hfe11b⟩
  step as ⟨Nt, hNt, hNtb⟩
  step as ⟨ssq, hssq, hssqb⟩
  step as ⟨fe12, hfe12⟩
  step as ⟨fe13, hfe13, hfe13b⟩
  step with backend.serial.u32.constants.SQRT_AD_MINUS_ONE_spec_eq as ⟨fK, hfK, hfKb⟩
  step as ⟨fe15, hfe15, hfe15b⟩
  step as ⟨fe16, hfe16, hfe16b⟩
  step as ⟨fe17, hfe17⟩
  -- the constants
  have Fi : fi.toField = sqrtM1 := by rw [toField_def, hfi]
  have Fd : fd.toField = d := toField_eq_d_of_asNat hfd
  have F1d : f1d.toField = 1 - d ^ 2 := by rw [toField_def, hf1d, ZMod.natCast_zmod_val]
  have Fd1 : fd1.toField = (d - 1) ^ 2 := by rw [toField_def, hfd1, ZMod.natCast_zmod_val]
  have C : c.toField = -1 := by
    have h : ((c.asNat + 1 : ℕ) : ZMod p) = 0 := by rw [hc]; exact ZMod.natCast_self p
    push_cast at h
    rw [toField_def]
    linear_combination h
  have One : one.toField = 1 := toField_eq_one_of_asNat hone
  have K : fK.toField = sqrtAdMinusOne := by rw [toField_def, hfK]
  -- RFC 9496 §4.3.4 step by step
  set r' : ZMod p := sqrtM1 * r_0.toField ^ 2 with hr'
  have R : r.toField = r' := by rw [toField_mul_of_mod hr, Fi, toField_sq_of_mod hfe4]
  set u' : ZMod p := (r' + 1) * (oneMinusDSq : ZMod p) with hu'
  have U : Ns.toField = u' := by
    rw [toField_mul_of_mod hNs, toField_add_of_limbs hfe5, R, One, F1d, ← oneMinusDSq_eq]
  set v' : ZMod p := (-1 - r' * curve25519.d) * (r' + curve25519.d) with hv'
  have V : D.toField = v' := by
    rw [toField_mul_of_mod hD, toField_sub_of_mod hfe7, toField_mul_of_mod hfe6,
      toField_add_of_limbs hfe8, C, Fd, R]
    ring
  have SQ := sqrtRatioM1_eq_of_spec hs0 hs1 (fun h ⟨x, hx⟩ => hs2 h x hx) hs3 hspar
  rw [U, V] at SQ
  have S0 : s.toField = (sqrtRatioM1 u' v').2 := by rw [SQ]
  have SQ1 : sq = 1#u8 ↔ (sqrtRatioM1 u' v').1 = true := by rw [SQ]; simp
  have Sp : sp.toField = (sqrtRatioM1 u' v').2 * r_0.toField := by
    rw [toField_mul_of_mod hsp, S0]
  have Pos : pos = 1#u8 ↔ ¬ sp.toField.isNeg := by
    rw [hpos, ← eq_one_iff_isNeg_toField hc1]
    rcases hc1v with rfl | rfl <;> decide
  have Sp1 : sp1.toField = -((sqrtRatioM1 u' v').2 * r_0.toField).abs := by
    have h := eq_ite_of_choice hposv Pos (fun h => by rw [hsp10 h])
      (fun h => toField_neg_of_mod (hsp11 h).1)
    rw [h, ← Sp]
    by_cases hn : sp.toField.isNeg
    · rw [ite_eq_right (not_not.mpr hn), ZMod.abs_of_isNeg hn, neg_neg]
    · rw [ite_eq_left hn, ZMod.abs_of_not_isNeg hn]
  have C2 : c2 = 1#u8 ↔ ¬ (sqrtRatioM1 u' v').1 = true := by
    rw [hc2, ← SQ1]
    rcases hsqv with rfl | rfl <;> decide
  set S : ZMod p := if (sqrtRatioM1 u' v').1 then (sqrtRatioM1 u' v').2
    else -((sqrtRatioM1 u' v').2 * r_0.toField).abs with hS
  have S1 : s1.toField = S := by
    have h : s1.toField = if ¬ (sqrtRatioM1 u' v').1 = true then sp1.toField else s.toField :=
      eq_ite_of_choice hc2v C2 (fun h => by rw [hs10 h]) (fun h => by rw [hs11 h])
    rw [h, Sp1, S0, hS]
    by_cases hb : (sqrtRatioM1 u' v').1 = true
    · rw [ite_eq_right (not_not.mpr hb), ite_eq_left hb]
    · rw [ite_eq_left hb, ite_eq_right hb]
  set Cc : ZMod p := if (sqrtRatioM1 u' v').1 then -1 else r' with hCc
  have C3 : c3.toField = Cc := by
    have h : c3.toField = if ¬ (sqrtRatioM1 u' v').1 = true then r.toField else c.toField :=
      eq_ite_of_choice hc2v C2 (fun h => by rw [hc30 h]) (fun h => by rw [hc31 h])
    rw [h, C, R, hCc]
    by_cases hb : (sqrtRatioM1 u' v').1 = true
    · rw [ite_eq_right (not_not.mpr hb), ite_eq_left hb]
    · rw [ite_eq_left hb, ite_eq_right hb]
  set N : ZMod p := Cc * (r' - 1) * (dMinusOneSq : ZMod p) - v' with hN
  have NT : Nt.toField = N := by
    rw [toField_sub_of_mod hNt, toField_mul_of_mod hfe11, toField_mul_of_mod hfe10, C3,
      toField_sub_of_mod hfe9, R, One, Fd1, ← dMinusOneSq_eq, V]
  have X13 : fe13.toField = 2 * S * v' := by
    rw [toField_mul_of_mod hfe13, toField_add_of_limbs hfe12, S1, V]
    ring
  have Z15 : fe15.toField = N * sqrtAdMinusOne := by rw [toField_mul_of_mod hfe15, NT, K]
  have Y16 : fe16.toField = 1 - S ^ 2 := by
    rw [toField_sub_of_mod hfe16, One, toField_sq_of_mod hssq, S1]
  have T17 : fe17.toField = 1 + S ^ 2 := by
    rw [toField_add_of_limbs hfe17, One, toField_sq_of_mod hssq, S1]
  have hon : CompletedPoint.«i686-tables».OnCurve ⟨fe13, fe16, fe15, fe17⟩ := by
    rw [CompletedPoint.«i686-tables».onCurve_iff_equation]
    dsimp only
    rw [X13, Z15, Y16, T17]
    exact ⟨Ristretto.mapRep_den_ne_zero _, Ristretto.mapRep_one_add_sq_ne_zero _,
      Ristretto.mapRep_equation _⟩
  have hb : CompletedPoint.«i686-tables».MulBounded ⟨fe13, fe16, fe15, fe17⟩ :=
    ⟨mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hfe13b),
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hfe16b),
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hfe15b),
      mulBounded_of_limbsLt (limbs_add_lt hfe17 (limbs_lt_of_le (by decide) honeb) hssqb)⟩
  step with «CompletedPointi686-tables».as_extended_spec_point _ hb hon as ⟨ep, h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  rw [h2]
  apply Point.ext
  · rw [CompletedPoint.«i686-tables».toPoint_x hon, Ristretto.mapRep_x]
    dsimp only
    rw [X13, Z15]
  · rw [CompletedPoint.«i686-tables».toPoint_y hon, Ristretto.mapRep_y]
    dsimp only
    rw [Y16, T17]

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the low `255` bits of the bytes, reduced
modulo `p` (`decodeU`); limbs `< 2^26`. -/
@[step]
theorem map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep (decodeU (bytes.asNat 8)) ∧ r.LimbsLt 26 ⦄ := by
  unfold map_to_curve
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2, toField_eq_decodeU_of_mod hfe], h3⟩

end «RistrettoPointi686-tables»

namespace «RistrettoPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `RistrettoPoint::elligator_ristretto_flavor`: RFC 9496's `MAP(r₀)`; limbs `< 2^54` in,
`< 2^52` out. -/
@[step]
theorem elligator_ristretto_flavor_spec (r_0 : FieldElement51) (hr_0 : r_0.LimbsLt 54) :
    elligator_ristretto_flavor r_0 ⦃ (r : RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep r_0.toField ∧ r.LimbsLt 52 ⦄ := by
  unfold elligator_ristretto_flavor
  step as ⟨fi, hfi, hfib⟩
  step as ⟨fd, hfd, hfdb⟩
  step as ⟨f1d, hf1d, hf1db⟩
  step as ⟨fd1, hfd1, hfd1b⟩
  step as ⟨c, hc, hcb⟩
  step as ⟨one, hone, honeb⟩
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨r, hr, hrb⟩
  step as ⟨fe5, hfe5⟩
  step as ⟨Ns, hNs, hNsb⟩
  step as ⟨fe6, hfe6, hfe6b⟩
  step as ⟨fe7, hfe7, hfe7b⟩
  step as ⟨fe8, hfe8⟩
  step as ⟨D, hD, hDb⟩
  step as ⟨sq, s, hsqv, hs0, hs1, hs2, hs3, hspar, hsb⟩
  step as ⟨sp, hsp, hspb⟩
  step as ⟨c1, hc1v, hc1⟩
  step as ⟨pos, hposv, hpos⟩
  step as ⟨sp1, hsp10, hsp11⟩
  step as ⟨c2, hc2v, hc2⟩
  step as ⟨s1, hs10, hs11⟩
  step as ⟨c3, hc30, hc31⟩
  have hsp1b : sp1.LimbsLt 52 := by
    rcases hposv with h | h
    · rw [hsp10 h]; exact hspb
    · exact (hsp11 h).2
  have hs1b : s1.LimbsLt 52 := by
    rcases hc2v with h | h
    · rw [hs10 h]; exact hsb
    · rw [hs11 h]; exact hsp1b
  have hc3b : c3.LimbsLt 52 := by
    rcases hc2v with h | h
    · rw [hc30 h]; exact limbs_lt_of_le (by decide) hcb
    · rw [hc31 h]; exact hrb
  step as ⟨fe9, hfe9, hfe9b⟩
  step as ⟨fe10, hfe10, hfe10b⟩
  step as ⟨fe11, hfe11, hfe11b⟩
  step as ⟨Nt, hNt, hNtb⟩
  step as ⟨ssq, hssq, hssqb⟩
  step as ⟨fe12, hfe12⟩
  step as ⟨fe13, hfe13, hfe13b⟩
  step with backend.serial.u64.constants.SQRT_AD_MINUS_ONE_spec_eq as ⟨fK, hfK, hfKb⟩
  step as ⟨fe15, hfe15, hfe15b⟩
  step as ⟨fe16, hfe16, hfe16b⟩
  step as ⟨fe17, hfe17⟩
  -- the constants
  have Fi : fi.toField = sqrtM1 := by rw [toField_def, hfi]
  have Fd : fd.toField = d := toField_eq_d_of_asNat hfd
  have F1d : f1d.toField = 1 - d ^ 2 := by rw [toField_def, hf1d, ZMod.natCast_zmod_val]
  have Fd1 : fd1.toField = (d - 1) ^ 2 := by rw [toField_def, hfd1, ZMod.natCast_zmod_val]
  have C : c.toField = -1 := by
    have h : ((c.asNat + 1 : ℕ) : ZMod p) = 0 := by rw [hc]; exact ZMod.natCast_self p
    push_cast at h
    rw [toField_def]
    linear_combination h
  have One : one.toField = 1 := toField_eq_one_of_asNat hone
  have K : fK.toField = sqrtAdMinusOne := by rw [toField_def, hfK]
  -- RFC 9496 §4.3.4 step by step
  set r' : ZMod p := sqrtM1 * r_0.toField ^ 2 with hr'
  have R : r.toField = r' := by rw [toField_mul_of_mod hr, Fi, toField_sq_of_mod hfe4]
  set u' : ZMod p := (r' + 1) * (oneMinusDSq : ZMod p) with hu'
  have U : Ns.toField = u' := by
    rw [toField_mul_of_mod hNs, toField_add_of_limbs hfe5, R, One, F1d, ← oneMinusDSq_eq]
  set v' : ZMod p := (-1 - r' * curve25519.d) * (r' + curve25519.d) with hv'
  have V : D.toField = v' := by
    rw [toField_mul_of_mod hD, toField_sub_of_mod hfe7, toField_mul_of_mod hfe6,
      toField_add_of_limbs hfe8, C, Fd, R]
    ring
  have SQ := sqrtRatioM1_eq_of_spec hs0 hs1 (fun h ⟨x, hx⟩ => hs2 h x hx) hs3 hspar
  rw [U, V] at SQ
  have S0 : s.toField = (sqrtRatioM1 u' v').2 := by rw [SQ]
  have SQ1 : sq = 1#u8 ↔ (sqrtRatioM1 u' v').1 = true := by rw [SQ]; simp
  have Sp : sp.toField = (sqrtRatioM1 u' v').2 * r_0.toField := by
    rw [toField_mul_of_mod hsp, S0]
  have Pos : pos = 1#u8 ↔ ¬ sp.toField.isNeg := by
    rw [hpos, ← eq_one_iff_isNeg_toField hc1]
    rcases hc1v with rfl | rfl <;> decide
  have Sp1 : sp1.toField = -((sqrtRatioM1 u' v').2 * r_0.toField).abs := by
    have h := eq_ite_of_choice hposv Pos (fun h => by rw [hsp10 h])
      (fun h => toField_neg_of_mod (hsp11 h).1)
    rw [h, ← Sp]
    by_cases hn : sp.toField.isNeg
    · rw [ite_eq_right (not_not.mpr hn), ZMod.abs_of_isNeg hn, neg_neg]
    · rw [ite_eq_left hn, ZMod.abs_of_not_isNeg hn]
  have C2 : c2 = 1#u8 ↔ ¬ (sqrtRatioM1 u' v').1 = true := by
    rw [hc2, ← SQ1]
    rcases hsqv with rfl | rfl <;> decide
  set S : ZMod p := if (sqrtRatioM1 u' v').1 then (sqrtRatioM1 u' v').2
    else -((sqrtRatioM1 u' v').2 * r_0.toField).abs with hS
  have S1 : s1.toField = S := by
    have h : s1.toField = if ¬ (sqrtRatioM1 u' v').1 = true then sp1.toField else s.toField :=
      eq_ite_of_choice hc2v C2 (fun h => by rw [hs10 h]) (fun h => by rw [hs11 h])
    rw [h, Sp1, S0, hS]
    by_cases hb : (sqrtRatioM1 u' v').1 = true
    · rw [ite_eq_right (not_not.mpr hb), ite_eq_left hb]
    · rw [ite_eq_left hb, ite_eq_right hb]
  set Cc : ZMod p := if (sqrtRatioM1 u' v').1 then -1 else r' with hCc
  have C3 : c3.toField = Cc := by
    have h : c3.toField = if ¬ (sqrtRatioM1 u' v').1 = true then r.toField else c.toField :=
      eq_ite_of_choice hc2v C2 (fun h => by rw [hc30 h]) (fun h => by rw [hc31 h])
    rw [h, C, R, hCc]
    by_cases hb : (sqrtRatioM1 u' v').1 = true
    · rw [ite_eq_right (not_not.mpr hb), ite_eq_left hb]
    · rw [ite_eq_left hb, ite_eq_right hb]
  set N : ZMod p := Cc * (r' - 1) * (dMinusOneSq : ZMod p) - v' with hN
  have NT : Nt.toField = N := by
    rw [toField_sub_of_mod hNt, toField_mul_of_mod hfe11, toField_mul_of_mod hfe10, C3,
      toField_sub_of_mod hfe9, R, One, Fd1, ← dMinusOneSq_eq, V]
  have X13 : fe13.toField = 2 * S * v' := by
    rw [toField_mul_of_mod hfe13, toField_add_of_limbs hfe12, S1, V]
    ring
  have Z15 : fe15.toField = N * sqrtAdMinusOne := by rw [toField_mul_of_mod hfe15, NT, K]
  have Y16 : fe16.toField = 1 - S ^ 2 := by
    rw [toField_sub_of_mod hfe16, One, toField_sq_of_mod hssq, S1]
  have T17 : fe17.toField = 1 + S ^ 2 := by
    rw [toField_add_of_limbs hfe17, One, toField_sq_of_mod hssq, S1]
  have hon : CompletedPoint.«x86_64-no-tables».OnCurve ⟨fe13, fe16, fe15, fe17⟩ := by
    rw [CompletedPoint.«x86_64-no-tables».onCurve_iff_equation]
    dsimp only
    rw [X13, Z15, Y16, T17]
    exact ⟨Ristretto.mapRep_den_ne_zero _, Ristretto.mapRep_one_add_sq_ne_zero _,
      Ristretto.mapRep_equation _⟩
  have hb : CompletedPoint.«x86_64-no-tables».LimbsLt 54 ⟨fe13, fe16, fe15, fe17⟩ :=
    ⟨limbs_lt_of_le (by decide) hfe13b, limbs_lt_of_le (by decide) hfe16b,
      limbs_lt_of_le (by decide) hfe15b,
      limbs_lt_of_le (by decide) (limbs_add_lt hfe17 (limbs_lt_of_le (by decide) honeb) hssqb)⟩
  step with «CompletedPointx86_64-no-tables».as_extended_spec_point _ hb hon as ⟨ep, h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  rw [h2]
  apply Point.ext
  · rw [CompletedPoint.«x86_64-no-tables».toPoint_x hon, Ristretto.mapRep_x]
    dsimp only
    rw [X13, Z15]
  · rw [CompletedPoint.«x86_64-no-tables».toPoint_y hon, Ristretto.mapRep_y]
    dsimp only
    rw [Y16, T17]

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the low `255` bits of the bytes, reduced
modulo `p` (`decodeU`); limbs `< 2^52`. -/
@[step]
theorem map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep (decodeU (bytes.asNat 8)) ∧ r.LimbsLt 52 ⦄ := by
  unfold map_to_curve
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2, toField_eq_decodeU_of_asNat_eq hfe], h3⟩

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `RistrettoPoint::elligator_ristretto_flavor`: RFC 9496's `MAP(r₀)`; limbs `< 2^27` in,
`< 2^26` out. -/
@[step]
theorem elligator_ristretto_flavor_spec (r_0 : FieldElement2625) (hr_0 : r_0.LimbsLt 27) :
    elligator_ristretto_flavor r_0 ⦃ (r : RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep r_0.toField ∧ r.LimbsLt 26 ⦄ := by
  unfold elligator_ristretto_flavor
  step as ⟨fi, hfi, hfib⟩
  step as ⟨fd, hfd, hfdb⟩
  step as ⟨f1d, hf1d, hf1db⟩
  step as ⟨fd1, hfd1, hfd1b⟩
  step as ⟨c, hc, hcb⟩
  step as ⟨one, hone, honeb⟩
  step as ⟨fe4, hfe4, hfe4b⟩
  step as ⟨r, hr, hrb⟩
  step as ⟨fe5, hfe5⟩
  step as ⟨Ns, hNs, hNsb⟩
  step as ⟨fe6, hfe6, hfe6b⟩
  step as ⟨fe7, hfe7, hfe7b⟩
  step as ⟨fe8, hfe8⟩
  step as ⟨D, hD, hDb⟩
  step as ⟨sq, s, hsqv, hs0, hs1, hs2, hs3, hspar, hsb⟩
  step as ⟨sp, hsp, hspb⟩
  step as ⟨c1, hc1v, hc1⟩
  step as ⟨pos, hposv, hpos⟩
  step as ⟨sp1, hsp10, hsp11⟩
  step as ⟨c2, hc2v, hc2⟩
  step as ⟨s1, hs10, hs11⟩
  step as ⟨c3, hc30, hc31⟩
  have hsp1b : sp1.LimbsLt 26 := by
    rcases hposv with h | h
    · rw [hsp10 h]; exact hspb
    · exact (hsp11 h).2
  have hs1b : s1.LimbsLt 26 := by
    rcases hc2v with h | h
    · rw [hs10 h]; exact hsb
    · rw [hs11 h]; exact hsp1b
  have hc3b : c3.LimbsLt 26 := by
    rcases hc2v with h | h
    · rw [hc30 h]; exact limbs_lt_of_le (by decide) hcb
    · rw [hc31 h]; exact hrb
  step as ⟨fe9, hfe9, hfe9b⟩
  step as ⟨fe10, hfe10, hfe10b⟩
  step as ⟨fe11, hfe11, hfe11b⟩
  step as ⟨Nt, hNt, hNtb⟩
  step as ⟨ssq, hssq, hssqb⟩
  step as ⟨fe12, hfe12⟩
  step as ⟨fe13, hfe13, hfe13b⟩
  step with backend.serial.u32.constants.SQRT_AD_MINUS_ONE_spec_eq as ⟨fK, hfK, hfKb⟩
  step as ⟨fe15, hfe15, hfe15b⟩
  step as ⟨fe16, hfe16, hfe16b⟩
  step as ⟨fe17, hfe17⟩
  -- the constants
  have Fi : fi.toField = sqrtM1 := by rw [toField_def, hfi]
  have Fd : fd.toField = d := toField_eq_d_of_asNat hfd
  have F1d : f1d.toField = 1 - d ^ 2 := by rw [toField_def, hf1d, ZMod.natCast_zmod_val]
  have Fd1 : fd1.toField = (d - 1) ^ 2 := by rw [toField_def, hfd1, ZMod.natCast_zmod_val]
  have C : c.toField = -1 := by
    have h : ((c.asNat + 1 : ℕ) : ZMod p) = 0 := by rw [hc]; exact ZMod.natCast_self p
    push_cast at h
    rw [toField_def]
    linear_combination h
  have One : one.toField = 1 := toField_eq_one_of_asNat hone
  have K : fK.toField = sqrtAdMinusOne := by rw [toField_def, hfK]
  -- RFC 9496 §4.3.4 step by step
  set r' : ZMod p := sqrtM1 * r_0.toField ^ 2 with hr'
  have R : r.toField = r' := by rw [toField_mul_of_mod hr, Fi, toField_sq_of_mod hfe4]
  set u' : ZMod p := (r' + 1) * (oneMinusDSq : ZMod p) with hu'
  have U : Ns.toField = u' := by
    rw [toField_mul_of_mod hNs, toField_add_of_limbs hfe5, R, One, F1d, ← oneMinusDSq_eq]
  set v' : ZMod p := (-1 - r' * curve25519.d) * (r' + curve25519.d) with hv'
  have V : D.toField = v' := by
    rw [toField_mul_of_mod hD, toField_sub_of_mod hfe7, toField_mul_of_mod hfe6,
      toField_add_of_limbs hfe8, C, Fd, R]
    ring
  have SQ := sqrtRatioM1_eq_of_spec hs0 hs1 (fun h ⟨x, hx⟩ => hs2 h x hx) hs3 hspar
  rw [U, V] at SQ
  have S0 : s.toField = (sqrtRatioM1 u' v').2 := by rw [SQ]
  have SQ1 : sq = 1#u8 ↔ (sqrtRatioM1 u' v').1 = true := by rw [SQ]; simp
  have Sp : sp.toField = (sqrtRatioM1 u' v').2 * r_0.toField := by
    rw [toField_mul_of_mod hsp, S0]
  have Pos : pos = 1#u8 ↔ ¬ sp.toField.isNeg := by
    rw [hpos, ← eq_one_iff_isNeg_toField hc1]
    rcases hc1v with rfl | rfl <;> decide
  have Sp1 : sp1.toField = -((sqrtRatioM1 u' v').2 * r_0.toField).abs := by
    have h := eq_ite_of_choice hposv Pos (fun h => by rw [hsp10 h])
      (fun h => toField_neg_of_mod (hsp11 h).1)
    rw [h, ← Sp]
    by_cases hn : sp.toField.isNeg
    · rw [ite_eq_right (not_not.mpr hn), ZMod.abs_of_isNeg hn, neg_neg]
    · rw [ite_eq_left hn, ZMod.abs_of_not_isNeg hn]
  have C2 : c2 = 1#u8 ↔ ¬ (sqrtRatioM1 u' v').1 = true := by
    rw [hc2, ← SQ1]
    rcases hsqv with rfl | rfl <;> decide
  set S : ZMod p := if (sqrtRatioM1 u' v').1 then (sqrtRatioM1 u' v').2
    else -((sqrtRatioM1 u' v').2 * r_0.toField).abs with hS
  have S1 : s1.toField = S := by
    have h : s1.toField = if ¬ (sqrtRatioM1 u' v').1 = true then sp1.toField else s.toField :=
      eq_ite_of_choice hc2v C2 (fun h => by rw [hs10 h]) (fun h => by rw [hs11 h])
    rw [h, Sp1, S0, hS]
    by_cases hb : (sqrtRatioM1 u' v').1 = true
    · rw [ite_eq_right (not_not.mpr hb), ite_eq_left hb]
    · rw [ite_eq_left hb, ite_eq_right hb]
  set Cc : ZMod p := if (sqrtRatioM1 u' v').1 then -1 else r' with hCc
  have C3 : c3.toField = Cc := by
    have h : c3.toField = if ¬ (sqrtRatioM1 u' v').1 = true then r.toField else c.toField :=
      eq_ite_of_choice hc2v C2 (fun h => by rw [hc30 h]) (fun h => by rw [hc31 h])
    rw [h, C, R, hCc]
    by_cases hb : (sqrtRatioM1 u' v').1 = true
    · rw [ite_eq_right (not_not.mpr hb), ite_eq_left hb]
    · rw [ite_eq_left hb, ite_eq_right hb]
  set N : ZMod p := Cc * (r' - 1) * (dMinusOneSq : ZMod p) - v' with hN
  have NT : Nt.toField = N := by
    rw [toField_sub_of_mod hNt, toField_mul_of_mod hfe11, toField_mul_of_mod hfe10, C3,
      toField_sub_of_mod hfe9, R, One, Fd1, ← dMinusOneSq_eq, V]
  have X13 : fe13.toField = 2 * S * v' := by
    rw [toField_mul_of_mod hfe13, toField_add_of_limbs hfe12, S1, V]
    ring
  have Z15 : fe15.toField = N * sqrtAdMinusOne := by rw [toField_mul_of_mod hfe15, NT, K]
  have Y16 : fe16.toField = 1 - S ^ 2 := by
    rw [toField_sub_of_mod hfe16, One, toField_sq_of_mod hssq, S1]
  have T17 : fe17.toField = 1 + S ^ 2 := by
    rw [toField_add_of_limbs hfe17, One, toField_sq_of_mod hssq, S1]
  have hon : CompletedPoint.«i686-no-tables».OnCurve ⟨fe13, fe16, fe15, fe17⟩ := by
    rw [CompletedPoint.«i686-no-tables».onCurve_iff_equation]
    dsimp only
    rw [X13, Z15, Y16, T17]
    exact ⟨Ristretto.mapRep_den_ne_zero _, Ristretto.mapRep_one_add_sq_ne_zero _,
      Ristretto.mapRep_equation _⟩
  have hb : CompletedPoint.«i686-no-tables».MulBounded ⟨fe13, fe16, fe15, fe17⟩ :=
    ⟨mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hfe13b),
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hfe16b),
      mulBounded_of_limbsLt (limbs_lt_of_le (by decide) hfe15b),
      mulBounded_of_limbsLt (limbs_add_lt hfe17 (limbs_lt_of_le (by decide) honeb) hssqb)⟩
  step with «CompletedPointi686-no-tables».as_extended_spec_point _ hb hon as ⟨ep, h1, h2, h3⟩
  refine ⟨h1, ?_, h3⟩
  rw [h2]
  apply Point.ext
  · rw [CompletedPoint.«i686-no-tables».toPoint_x hon, Ristretto.mapRep_x]
    dsimp only
    rw [X13, Z15]
  · rw [CompletedPoint.«i686-no-tables».toPoint_y hon, Ristretto.mapRep_y]
    dsimp only
    rw [Y16, T17]

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the low `255` bits of the bytes, reduced
modulo `p` (`decodeU`); limbs `< 2^26`. -/
@[step]
theorem map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep (decodeU (bytes.asNat 8)) ∧ r.LimbsLt 26 ⦄ := by
  unfold map_to_curve
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2, toField_eq_decodeU_of_mod hfe], h3⟩

end «RistrettoPointi686-no-tables»

end Curve25519Dalek.ristretto.elligator
