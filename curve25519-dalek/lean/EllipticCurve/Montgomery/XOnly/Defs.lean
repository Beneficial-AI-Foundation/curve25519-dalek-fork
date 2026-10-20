/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.Montgomery.Lemmas
import Mathlib.Algebra.GroupWithZero.Basic
public section

/-! # Montgomery models: x-only arithmetic, definitions

The x-only arithmetic of a Montgomery model `M`, i.e. everything that depends only on the
`u`-coordinate (RFC 7748 §5):

- the nonsingularity of the twist `M.twist c` (`isNonsingular_twist`);
- the hidden x-only scalar multiplication `M.xMul c n u`, defined through any lift of `u` to a
  point of `M` or, failing that, of the twist `M.twist c`, and characterised by
  `xMul_eq_u_nsmul`, `xMul_eq_u_nsmul_twist` (`EllipticCurve.Montgomery.XOnly.Lemmas`);
- the projective x-only points `XZ F` (`(U : W)`, with `W = 0` for `∞`), the exposed RFC 7748
  formulas `XZ.dbl`, `XZ.add` (`xDBL`, `xADD`) with the ladder constant `a24 = (A - 2) / 4`,
  and the Montgomery ladder `XZ.ladder` written as the RFC's pseudocode (conditional swaps,
  bits from the top). They are parametrised by the field element `a24` rather than by the
  model, so that the ladder of the twist is definitionally the ladder of `M` (`ladder_twist`);
  `M.xDBL`, `M.xADD`, `M.ladder` instantiate them at `M.a24`.
- the representation predicate `XZ.Represents`: `(U : W)` represents the point `Q`.

Only `xMul` is hidden; the formulas are exposed so that the kernel can evaluate them
(`curve-api.md` §8). -/

universe u

namespace MontgomeryModel

variable {F : Type u} [Field F] (M : MontgomeryModel F)

/-! ### The twist -/

/-- The twist of a nonsingular model by `c ≠ 0` is nonsingular. Not an instance, since `c ≠ 0`
is a hypothesis. -/
theorem isNonsingular_twist [M.IsNonsingular] {c : F} (hc : c ≠ 0) :
    (M.twist c).IsNonsingular where
  two_ne_zero := IsNonsingular.two_ne_zero (M := M)
  B_ne_zero := by
    rw [twist_B]
    exact mul_ne_zero IsNonsingular.B_ne_zero hc
  A_sq_ne_four := by
    rw [twist_A]
    exact IsNonsingular.A_sq_ne_four

/-! ### x-only scalar multiplication -/

open Classical in
/-- x-only scalar multiplication `u ↦ u(n • Q)`, total in `u`: through a point `Q` of `M` with
`Q.u = u` if one exists, else through a point of the twist `M.twist c` with that `u` if one
exists, else `0`. Hidden construction, characterised by `xMul_eq_u_nsmul` and
`xMul_eq_u_nsmul_twist` (for `c` a non-square); for a finite field every `u` lifts to `M` or to
the twist (`exists_point_u_or_twist`). -/
noncomputable def xMul [M.IsNonsingular] (c : F) (n : ℕ) (u : F) : F :=
  if h : ∃ Q : M.Point, Q.u = u then (n • h.choose).u
  else if hc : c = 0 then 0
  else
    haveI := M.isNonsingular_twist hc
    if h' : ∃ Q : (M.twist c).Point, Q.u = u then (n • h'.choose).u else 0

/-! ### Projective x-only points and the RFC 7748 formulas -/

/-- A projective x-only point `(U : W)`: the `u`-coordinate `U / W`, with `W = 0` for the
point at infinity. -/
structure XZ (F : Type u) where
  /-- The numerator. -/
  U : F
  /-- The denominator; `0` at infinity. -/
  W : F

/-- The ladder constant `a24 = (A - 2) / 4` of RFC 7748 (`121665` for curve25519). -/
@[expose] def a24 : F := (M.A - 2) / 4

namespace XZ

/-- The affine `u`-coordinate `U / W`, `0` at infinity. -/
@[expose] def toU (P : XZ F) : F :=
  P.U / P.W

/-- x-only doubling, RFC 7748 §5: `A = U + W`, `AA = A²`, `B = U - W`, `BB = B²`,
`E = AA - BB`, result `(AA · BB : E · (AA + a24 · E))`. Depends on the model only through
`a24 = (A - 2) / 4`. -/
@[expose] def dbl (a24 : F) (P : XZ F) : XZ F :=
  let A := P.U + P.W
  let AA := A ^ 2
  let B := P.U - P.W
  let BB := B ^ 2
  let E := AA - BB
  ⟨AA * BB, E * (AA + a24 * E)⟩

/-- x-only differential addition, RFC 7748 §5: for `P = (x₂ : z₂)`, `Q = (x₃ : z₃)` and the
affine `u`-coordinate `u₁` of the difference, `A = x₂ + z₂`, `B = x₂ - z₂`, `C = x₃ + z₃`,
`D = x₃ - z₃`, `DA = D · A`, `CB = C · B`, result `((DA + CB)² : u₁ · (DA - CB)²)`. Independent
of the model. -/
@[expose] def add (P Q : XZ F) (u₁ : F) : XZ F :=
  let A := P.U + P.W
  let B := P.U - P.W
  let C := Q.U + Q.W
  let D := Q.U - Q.W
  let DA := D * A
  let CB := C * B
  ⟨(DA + CB) ^ 2, u₁ * (DA - CB) ^ 2⟩

/-- The conditional swap `cswap` of RFC 7748, on a pair of projective points. -/
@[expose] def cswap (swap : Bool) (P Q : XZ F) : XZ F × XZ F :=
  if swap then (Q, P) else (P, Q)

/-- The state of the Montgomery ladder: the RFC's `(x_2 : z_2)`, `(x_3 : z_3)` and the pending
swap bit. -/
structure LadderState (F : Type u) where
  /-- `(x_2 : z_2)`. -/
  R₀ : XZ F
  /-- `(x_3 : z_3)`. -/
  R₁ : XZ F
  /-- The swap bit (the previous scalar bit). -/
  swap : Bool

/-- One iteration of the RFC 7748 ladder at a bit `k_t` of the scalar: `swap ^= k_t`,
`cswap`, `swap = k_t`, then `(x_2 : z_2) ← xDBL`, `(x_3 : z_3) ← xADD` with the base
coordinate `x₁`. -/
@[expose] def ladderStep (a24 x₁ : F) (s : LadderState F) (kt : Bool) : LadderState F :=
  let R := cswap (s.swap ^^ kt) s.R₀ s.R₁
  ⟨dbl a24 R.1, add R.1 R.2 x₁, kt⟩

/-- The ladder loop over the bits `t - 1, …, 0` of `k`, from the top. Structural recursion on
the bit index, so that the kernel can evaluate it. -/
@[expose] def ladderLoop (a24 x₁ : F) (k : ℕ) : ℕ → LadderState F → LadderState F
  | 0, s => s
  | t + 1, s => ladderLoop a24 x₁ k t (ladderStep a24 x₁ s (k.testBit t))

/-- The projective result `(x_2 : z_2)` of the RFC 7748 ladder over `bits` bits of `k` on the
base coordinate `u`: start from `(1 : 0)`, `(u : 1)`, `swap = 0`, run the loop, and apply the
final `cswap`. -/
@[expose] def ladderXZ (a24 : F) (bits k : ℕ) (u : F) : XZ F :=
  let s := ladderLoop a24 u k bits ⟨⟨1, 0⟩, ⟨u, 1⟩, false⟩
  (cswap s.swap s.R₀ s.R₁).1

/-- The Montgomery ladder of RFC 7748 §5 on field elements: `x_2 / z_2` after `ladderXZ`, with
`x / 0 = 0` (in `ZMod p`, the RFC's `x_2 · z_2^(p - 2)`; see `curve25519.toU_eq_mul_pow_sub_two`).
For `u = u(Q)` with `u ≠ 0` and `k < 2 ^ bits` it computes `u(k • Q)` (`ladder_eq_u_nsmul`). -/
@[expose] def ladder (a24 : F) (bits k : ℕ) (u : F) : F :=
  (ladderXZ a24 bits k u).toU

/-- `(U : W)` represents the point `Q`: for `Q = ∞`, `W = 0` and `U ≠ 0`; for `Q` affine,
`W ≠ 0` and `U = u(Q) · W`. The pair `(0 : 0)` represents nothing. -/
@[expose] def Represents (P : XZ F) {M : MontgomeryModel F} [M.IsNonsingular] (Q : M.Point) :
    Prop :=
  (Q = 0 ∧ P.W = 0 ∧ P.U ≠ 0) ∨ (Q ≠ 0 ∧ P.W ≠ 0 ∧ P.U = Q.u * P.W)

end XZ

/-- x-only doubling on `M` (RFC 7748 `xDBL`): `XZ.dbl` at `M.a24`. -/
@[expose] def xDBL (P : XZ F) : XZ F :=
  XZ.dbl M.a24 P

/-- x-only differential addition (RFC 7748 `xADD`), with the affine `u`-coordinate `u₁` of the
difference: `XZ.add`. It does not depend on the model, so it takes none. -/
@[expose] def xADD (P Q : XZ F) (u₁ : F) : XZ F :=
  XZ.add P Q u₁

/-- The Montgomery ladder of `M` over `bits` bits: `XZ.ladder` at `M.a24`. -/
@[expose] def ladder (bits k : ℕ) (u : F) : F :=
  XZ.ladder M.a24 bits k u

end MontgomeryModel
