/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public section

/-! # Primality of `p` and `L`

TODO: replace these by the much shorter `PrimeCert` proofs (Pocklington certificates,
https://github.com/b-mehta/PrimeCert). -/

set_option linter.style.longLine false

namespace curve25519

/-- Lucas's primality test, with the prime factors of `n - 1` given as a list `fs` of
`(prime, exponent)` pairs. -/
private theorem prime_of_lucas (n a : ℕ) (fs : List (ℕ × ℕ)) (hfs : fs.Forall fun f => f.1.Prime)
    (hfac : n - 1 = (fs.map fun f => f.1 ^ f.2).prod) (hpow : (a : ZMod n) ^ (n - 1) = 1)
    (hdiv : fs.Forall fun f => (a : ZMod n) ^ ((n - 1) / f.1) ≠ 1) : n.Prime := by
  rw [List.forall_iff_forall_mem] at hfs hdiv
  refine lucas_primality n a hpow fun q hq hdvd => ?_
  rw [hfac] at hdvd
  obtain ⟨_, hm, hqd⟩ := (Nat.Prime.prime hq).dvd_prod_iff.mp hdvd
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hm
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (hfs f hf)).mp (hq.dvd_of_dvd_pow hqd)
  exact hdiv f hf

private theorem prime_1224481 : Nat.Prime 1224481 :=
  prime_of_lucas 1224481 13
    [(2, 5), (3, 1), (5, 1), (2551, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_1923133 : Nat.Prime 1923133 :=
  prime_of_lucas 1923133 2
    [(2, 2), (3, 1), (43, 1), (3727, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_8574133 : Nat.Prime 8574133 :=
  prime_of_lucas 8574133 2
    [(2, 2), (3, 1), (7, 1), (103, 1), (991, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_14741173 : Nat.Prime 14741173 :=
  prime_of_lucas 14741173 2
    [(2, 2), (3, 2), (409477, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_58964693 : Nat.Prime 58964693 :=
  prime_of_lucas 58964693 2
    [(2, 2), (14741173, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, prime_14741173⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_292386187 : Nat.Prime 292386187 :=
  prime_of_lucas 292386187 2
    [(2, 1), (3, 4), (307, 1), (5879, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_2773320623 : Nat.Prime 2773320623 :=
  prime_of_lucas 2773320623 5
    [(2, 1), (2437, 1), (569003, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_72106336199 : Nat.Prime 72106336199 :=
  prime_of_lucas 72106336199 7
    [(2, 1), (13, 1), (2773320623, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, prime_2773320623⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_213441916511 : Nat.Prime 213441916511 :=
  prime_of_lucas 213441916511 13
    [(2, 1), (5, 1), (73, 1), (292386187, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, prime_292386187⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_1257559732178653 : Nat.Prime 1257559732178653 :=
  prime_of_lucas 1257559732178653 2
    [(2, 2), (3, 1), (7, 1), (23, 1), (531581, 1), (1224481, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_1224481⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_1919519569386763 : Nat.Prime 1919519569386763 :=
  prime_of_lucas 1919519569386763 2
    [(2, 1), (3, 1), (7, 1), (19, 1), (47, 2), (127, 1), (8574133, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_8574133⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_31757755568855353 : Nat.Prime 31757755568855353 :=
  prime_of_lucas 31757755568855353 10
    [(2, 3), (3, 1), (31, 1), (107, 1), (223, 1), (4153, 1), (430751, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_4434155615661930479 : Nat.Prime 4434155615661930479 :=
  prime_of_lucas 4434155615661930479 17
    [(2, 1), (41, 1), (43, 1), (1257559732178653, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, prime_1257559732178653⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_3044861653679985063343 : Nat.Prime 3044861653679985063343 :=
  prime_of_lucas 3044861653679985063343 5
    [(2, 1), (3, 1), (11, 1), (30703, 1), (82163, 1), (132667, 1), (137849, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_172054593956031949258510691 : Nat.Prime 172054593956031949258510691 :=
  prime_of_lucas 172054593956031949258510691 2
    [(2, 1), (5, 1), (1361, 1), (2851, 1), (4434155615661930479, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_4434155615661930479⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_198211423230930754013084525763697 : Nat.Prime 198211423230930754013084525763697 :=
  prime_of_lucas 198211423230930754013084525763697 5
    [(2, 4), (3, 1), (23, 1), (58964693, 1), (3044861653679985063343, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, prime_58964693, prime_3044861653679985063343⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_75445702479781427272750846543864801 : Nat.Prime 75445702479781427272750846543864801 :=
  prime_of_lucas 75445702479781427272750846543864801 7
    [(2, 5), (3, 2), (5, 2), (75707, 1), (72106336199, 1), (1919519569386763, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_72106336199, prime_1919519569386763⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_19757330305831588566944191468367130476339 : Nat.Prime 19757330305831588566944191468367130476339 :=
  prime_of_lucas 19757330305831588566944191468367130476339 2
    [(2, 1), (269, 1), (213441916511, 1), (172054593956031949258510691, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, prime_213441916511, prime_172054593956031949258510691⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_276602624281642239937218680557139826668747 : Nat.Prime 276602624281642239937218680557139826668747 :=
  prime_of_lucas 276602624281642239937218680557139826668747 2
    [(2, 1), (7, 1), (19757330305831588566944191468367130476339, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, prime_19757330305831588566944191468367130476339⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_74058212732561358302231226437062788676166966415465897661863160754340907 : Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 :=
  prime_of_lucas 74058212732561358302231226437062788676166966415465897661863160754340907 2
    [(2, 1), (3, 1), (353, 1), (57467, 1), (132049, 1), (1923133, 1), (31757755568855353, 1), (75445702479781427272750846543864801, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_1923133, prime_31757755568855353, prime_75445702479781427272750846543864801⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_7237005577332262213973186563042994240857116359379907606001950938285454250989 : Nat.Prime 7237005577332262213973186563042994240857116359379907606001950938285454250989 :=
  prime_of_lucas 7237005577332262213973186563042994240857116359379907606001950938285454250989 2
    [(2, 2), (3, 1), (11, 1), (198211423230930754013084525763697, 1), (276602624281642239937218680557139826668747, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, prime_198211423230930754013084525763697, prime_276602624281642239937218680557139826668747⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

private theorem prime_57896044618658097711785492504343953926634992332820282019728792003956564819949 : Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 :=
  prime_of_lucas 57896044618658097711785492504343953926634992332820282019728792003956564819949 2
    [(2, 2), (3, 1), (65147, 1), (74058212732561358302231226437062788676166966415465897661863160754340907, 1)]
    (by simp only [List.Forall]; exact ⟨by norm_num, by norm_num, by norm_num, prime_74058212732561358302231226437062788676166966415465897661863160754340907⟩)
    (by norm_num) (by reduce_mod_char)
    (by simp only [List.Forall]; and_intros <;> reduce_mod_char <;> decide)

/-- `p = 2^255 - 19` is prime. -/
theorem p_prime : p.Prime := by
  rw [show p = 57896044618658097711785492504343953926634992332820282019728792003956564819949 by norm_num [p]]
  exact prime_57896044618658097711785492504343953926634992332820282019728792003956564819949

/-- `L = 2^252 + 27742317777372353535851937790883648493` is prime. -/
theorem L_prime : L.Prime := by
  rw [show L = 7237005577332262213973186563042994240857116359379907606001950938285454250989 by norm_num [L]]
  exact prime_7237005577332262213973186563042994240857116359379907606001950938285454250989

instance : Fact p.Prime := ⟨p_prime⟩

instance : Fact L.Prime := ⟨L_prime⟩

end curve25519
