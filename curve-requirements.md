# Elliptic curves: what the point specs need

Working note (2026-10-16), Phase 1 of the curve-framework plan. For every translated
point-related Rust item, it states what the item's spec must say and which mathematical notions
that requires. From this it derives the minimum framework, and lists the design questions to
decide **before** anything is coded.

The per-item tables are in the appendices:
- **A:** curve_models, edwards, affine, window, scalar_mul, traits, point constants;
- **B:** montgomery, the Edwards↔Montgomery items, Ristretto, constants.

Sources used:
- the Rust code and its doc comments;
- the Lean names in `translation.json` and `Funs.lean`;
- RFC 8032, RFC 7748 and RFC 9496;
- the old project's statements (`~/Projects/curve25519-dalek-lean-verify`);
- FEC (`/mnt/projects/Maths/FEC`).

## 1. Summary

- **Most items only need the Ed25519 group.** About 80 % of the items are stated purely in
  terms of a point type with an `AddCommGroup` (`+`, `-`, `0`, `n •`): every add, sub, neg,
  double, scalar mul, `Sum`, multiscalar, table, `is_small_order` (`8 • P = 0`) and
  `is_torsion_free` (`L • P = 0`). Nothing else at curve level.
- **A few items need small extras.** `compress` needs the parity of `x` and the encoding
  `y + 2^255·parity(x)`; `decompress` needs square roots; `to_montgomery` needs the formula
  `(1+y)/(1−y)`; the clamped muls need `clamp`; the basepoint items need `B`; and
  `EIGHT_TORSION` needs a point of order 8.
- **The Montgomery ladder needs the twist.** `mul_clamped` is exactly X25519 (RFC 7748). It is
  total on all byte inputs, and half of the `u` values lie on the quadratic twist. A faithful
  spec needs x-only scalar multiplication defined for the curve **and** its twist.
- **Ristretto is self-contained and can be deferred.** It needs the 4-torsion `E[4]`, the even
  points `2E`, and RFC 9496 encode/decode/map with their theorems. It needs no quotient type.
- **Not needed by any statement:**
  - the group order `#E = 8L` and point counting;
  - `L • B = 0` (only a sanity lemma);
  - cyclicity of `E[8]`;
  - a quotient group;
  - a general projective-space library.
- **Things the code forces, which the old project got wrong or missed:**
  - **Decompression is more lenient than RFC 8032.** A `y ≥ p` is accepted and reduced, and
    `x = 0` with the sign bit set is accepted. The old project's decoder modelled RFC 8032
    instead.
  - **Scalars are unreduced.** Specs say `s.asNat • P`, with precondition `s.asNat < 2^255`
    (not "canonical").
  - **`EdwardsPoint` needs limbs `< 2^52`.** The old project's `< 2^53` is too weak for the
    affine-Niels addition (see §4, Q4).
  - **`is_valid` is weaker than validity.** It never checks `Z ≠ 0`.
  - **Each struct compares differently.** `CompressedEdwardsY` equality is byte equality.
    Ristretto `ct_eq` means `P − Q ∈ E[4]`.
  - **The old Montgomery `mul_spec` is false.** Its statement `mkPoint result = m • mkPoint P`
    fails on the sign of `v`, on low-order inputs and on twist inputs, and it rests on `sorry`s.

## 2. Notions needed (consolidated)

### 2.1 Mathematics (independent of dalek)

Split over two libraries (`curve-api.md`): generic model theory in `EllipticCurve` (C2–C7, C11
generic parts, M1–M3, R1–R2 constructions), curve25519 instances and facts in `Curve25519`
(C8–C10, M4–M5, R3–R4, and the instantiations).

| # | Notion | Needed by | Tier |
|---|---|---|---|
| C1 | Field `ZMod p` with `a = −1`, `d`, `A`, `sqrtM1` | everything | exists |
| C2 | Ed25519: curve `−x² + y² = 1 + d x² y²`, point type `E` (affine, with on-curve proof) | almost every item | core |
| C3 | Group law on `E`: `0 = (0,1)`, `−(x,y) = (−x,y)`, `+` given by the complete twisted-Edwards formula, `AddCommGroup` (giving ℕ/ℤ `•` and `List.sum`); lemmas for the explicit formula | all arithmetic, tables, scalar mul, `Sum`, multiscalar, torsion checks | core |
| C4 | Completeness: `d` non-square and `−1` square, so the denominators `1 ± d x₁x₂y₁y₂ ≠ 0` | proofs only (validity of `CompletedPoint`, decompress) | core |
| C5 | Parity `isNeg x := x.val % 2 = 1` on `ZMod p` | compress family, decompress, `to_edwards` sign, Ristretto | core |
| C6 | Encoding `encode P := P.y.val + 2^255 · (P.x.val % 2)` (RFC 8032 §5.1.2) | `compress` ×3, `AffinePoint::compress`, `BASEPOINT_COMPRESSED` | core |
| C7 | Decoding: **no function needed**. The spec characterises the result: success ⇔ some `x` puts `(x, y)` on the curve, with `y := (n mod 2^255) mod p`, and `x = 0 ∨ parity(x) = sign`. Dalek's lenient behaviour, not RFC 8032's | `decompress`, `step_1`/`step_2` | core |
| C8 | Basepoint `B` (y = 4/5, x even) | `mul_base*`, vartime double/triple base, basepoint constants and tables | core |
| C9 | `clamp n := 2^254 + 8·⌊(n mod 2^254)/8⌋` (RFC 7748), or reuse `clamp_integer_spec`'s value | `mul_clamped`, `mul_base_clamped` (Edwards and Montgomery) | core |
| C10 | A point of order 8 (`8•T = 0 ∧ 4•T ≠ 0`) | `EIGHT_TORSION` only | core |
| C11 | Edwards→Montgomery u-formula `(1+y)/(1−y)` (with `/0 = 0`) | `to_montgomery`, `to_montgomery_batch` | core |
| M1 | Montgomery curves `B v² = u³ + A u² + u` with a group: Curve25519 `E_M` (B = 1) **and its twist `E_M'`** (B = 2, any non-square) | all ladder items, `to_edwards`, `X25519_LOW_ORDER_POINTS` | Montgomery |
| M2 | `u₀ : point → ZMod p`, sending ∞ to 0 | ladder, `mul_base` | Montgomery |
| M3 | `xMul n u := u₀(n • Q)` for any `Q` on `E_M` or `E_M'` with `u₀ Q = u`; lemma: independent of the choice of `Q`. Then `x25519 k u := xMul (clamp k) u` | `mul` ×8, `mul_assign`, `mul_bits_be`, `mul_clamped`, `mul_base*`, low-order theorem | Montgomery |
| M4 | Birational group isomorphism `φ : E ≃+ E_M` with `u₀ (φ P) = (1+y)/(1−y)`; basepoint `u₀ (φ B) = 9` | `mul_base` (Montgomery), `to_edwards`, `X25519_BASEPOINT` | Montgomery |
| M5 | Quadratic-character facts: `A²−4`, `A−2` and `d` are non-squares; `A+2`, `−1`, `−(A+2)` are squares | proofs of `to_edwards`, ladder edge cases, Ristretto | Montgomery |
| R1 | `E[4]` and the relation `P ≈ Q :↔ P − Q ∈ E[4]` | Ristretto `ct_eq`/`eq`, coset invariance | Ristretto |
| R2 | `IsEven Q :↔ ∃ R, Q = 2 • R`, plus the 2-descent `IsSquare (1 − y²) → IsEven`. The old project left this as `sorry` | invariant of every Ristretto point, decode/map outputs | Ristretto |
| R3 | RFC 9496 decode, encode and MAP as pure `ZMod p` functions, with: decode lands in `2E`; encode is constant on `≈` classes; encode is injective modulo `≈` on `2E`; the round trips; MAP is on the curve and lands in `2E` | `compress`, `decompress`, `double_and_compress_batch`, elligator, `from_uniform_bytes`, Ristretto constants | Ristretto |
| R4 | Sign conventions for the Ristretto constants (`INVSQRT_A_MINUS_D`, `SQRT_AD_MINUS_ONE`, …: RFC 9496 fixes the non-negative roots) | R3 | Ristretto |

### 2.2 Implementation layer (`Defs` lib, specific to dalek)

Terminology (fixed 2026-10-19, see `curve-api.md` §0): *curve* = isomorphism class, *model* =
equation (`TwistedEdwardsModel`, `MontgomeryModel`), *coordinates* = redundant point
representation within one model (extended, projective, completed, Niels). The appendices
predate this and say "representation" for both the coordinate systems and this `Defs` layer.

All relations are equalities in `ZMod p` of the field elements' values.

| # | Notion | Content (forced by the code) | Limb bound | Needed by |
|---|---|---|---|---|
| D1 | `FieldElement51.toField : ZMod p := ↑asNat` | the bridge from the `ℕ % p` field specs | – | all point items |
| D2 | `EdwardsPoint`: `OnCurve` + `toPoint` | `Z ≠ 0`, `X·Y = Z·T`, `(Y²−X²)Z² = Z⁴ + dX²Y²`; point `(X/Z, Y/Z)` | all `< 2^52` | nearly everything |
| D3 | `ProjectivePoint` | `Z ≠ 0`, the same equation; `(X/Z, Y/Z)` | `< 2^52` | double, conversions, vartime loops |
| D4 | `CompletedPoint` | `Z ≠ 0`, `T ≠ 0`, `−X²T² + Y²Z² = Z²T² + dX²Y²`; `(X/Z, Y/T)` | `< 2^54` | double, mixed add/sub, conversions |
| D5 | `ProjectiveNielsPoint` | `X := (YpX−YmX)/2`, `Y := (YpX+YmX)/2`; equation of D3 and `T2d·Z = 2d·X·Y`; `(X/Z, Y/Z)` | `< 2^54` | add/sub/neg, PN tables |
| D6 | `AffineNielsPoint` | `x := (ypx−ymx)/2`, `y := (ypx+ymx)/2`; `(x, y)` on the curve and `xy2d = 2d·x·y` | `< 2^54` | add/sub/neg, AN tables, basepoint tables |
| D7 | `AffinePoint` | `(x, y)` on the curve | `< 2^52` | `edwards/affine.rs` |
| D8 | Tables: lookup (`entry j = (j+1)•P`), NAF (`entry k = (2k+1)•A`), basepoint table (`row i = lookup table of 2^(2wi)•B`), precomputation ↔ its list of points | – | via D5/D6 | window, scalar_mul, basepoint tables |
| D9 | Byte arrays: `CompressedEdwardsY` bytes as a number; `MontgomeryPoint.u := ((bytes.asNat % 2^255 : ℕ) : ZMod p)`; canonical output `r.asNat < p`; `CompressedRistretto` `s = bytes.asNat` with canonicity `s < p` and sign | – | – | compress/decompress, all Montgomery and Ristretto byte inputs and outputs |
| D10 | Montgomery `ProjectivePoint (U:W) ↦ U/W` (0 when `W = 0`) | – | – | `as_affine`, ladder |
| D11 | `RistrettoPoint.Valid P := EdwardsPoint valid ∧ IsEven P.toPoint` (`RistrettoPoint` is literally `EdwardsPoint`) | – | – | all Ristretto points |
| D12 | Existing: `Iterator.Yields`, `Scalar.asNat`, `clamp_integer_spec`; big-endian bits → ℕ | – | – | `Sum`, multiscalar, `mul_bits_be` |

## 3. Scope of the framework milestone

**Reframed after review (2026-10-17).** The goal is a relatively complete specification of
curve25519 that is independent of dalek, eventually of Mathlib quality for all the curve models.
The task now is to fix the **Lean API**: how to talk about a curve, its points in each
representation, conversions between representations, encodings, and the group facts. The
implementations behind the API are hidden (module system: non-exposed definitions, facts only
through lemmas), so that the first proofs can be certificate-heavy (as in FEC's `Messy/` files)
and be replaced by better proofs later without touching the API or any spec.

Decisions taken:
- `OnCurve` (algebra) and limb bounds stay **separate** predicates (Q2/Q3).
- FEC and aeneas-use-cases are **guidance**; reuse pieces where they help, with credit.
- The order facts `addOrderOf B = L`, `#E = 8L`, `(8L) • P = 0`, the 8-torsion structure etc.
  **are in scope** (Q6), as part of the dalek-independent specification.
- The API draft is `curve-api.md`; the tiers below say what the API must cover first.

### Tiers

Three tiers. Each later tier only adds; nothing in an earlier tier changes.

1. **Edwards core** (unblocks `curve_models.rs`, `edwards.rs`, `edwards/affine.rs`, `window.rs`,
   `scalar_mul/*` and the Edwards point constants):
   - C2–C11 in `Curve25519`;
   - D1–D9 in `Defs`, without the Montgomery and Ristretto parts of D9.
2. **Montgomery**, in two steps:
   - **2a. RFC conformance:** an executable transcription of RFC 7748 `X25519` in
     `Curve25519` (no curve needed), plus D9 (Montgomery part) and D10. This is enough for a
     precondition-free, byte-exact spec of `mul_clamped`/`mul`/`mul_base_clamped` on every
     input, including twist inputs (§6).
   - **2b. Group meaning:** M1–M5, i.e. the curve, its twist, `xMul`, and the birational map,
     with the theorem `X25519 k u = x25519 k u`. Unblocks `to_edwards`, `to_montgomery*` and
     the semantic reading of the ladder.
3. **Ristretto**: R1–R4, D9 (Ristretto part) and D11. Unblocks `ristretto.rs`. **In scope**
   (decision 2026-10-19): the API is fixed now (`curve-api.md` §7), including the quotient group
   of order `L`; proofs may be certificate-backed at first.

Scope of this milestone (2026-10-19): the **API for all three tiers**, with implementations that
may be certificate-backed; see `curve-api.md` §10 for the order of work.

## 4. Design questions (with recommendations)

**Q1. Source of the Edwards group law.**
- Mathlib has only Weierstrass curves; its affine `Point` group is fully proved. The options:
  - **(a)** Prove `AddCommGroup` directly on the Edwards formula. Associativity is the hard part:
    the old project left it as `sorry`.
  - **(b)** Transport the group from Mathlib along `E ≃ E_M ≃ Weierstrass`, as FEC does, then
    prove that the explicit formula agrees with the transported law (FEC `addFormula_eq_add`,
    via polynomial certificates).
- **Recommendation: (b).** Associativity comes for free. The same transport also gives tier 2
  (M1, M4): Montgomery curves with general `B` are Weierstrass curves with `a₂ = AB`, `a₄ = B²`.
- The work is the explicit point bijection (finite exceptional cases), the formula agreement,
  and the model scaling. FEC's map lands in `B = −486664`, so an isomorphism to `B = 1` is
  needed.
- **Implementation template:** aeneas-use-cases (§6) proves an injective homomorphism
  `phi : Edwards → Weierstrass.Point` with explicit `linear_combination` certificates (generic
  over any field, plus the special case `(0,−1) ↦ (0,0)`). With `phi` injective and additive,
  `Function.Injective.addCommGroup` gives `AddCommGroup` on our point type. This needs no
  transport of the point set: only `phi_add`, `phi_neg` and `phi_zero` plus injectivity, which is
  less work than FEC's full bijection.
- Unlike aeneas-use-cases, keep a real group instance: statements use `n •`, `List.sum` and
  `addOrderOf` directly.
- To check in Phase 2: which of FEC's and aeneas-use-cases' certificates port to our toolchain
  (both are older Lean versions, without the module system).

**Q2. How Rust structs map to points.**
- **Recommendation:** for each struct, an algebraic predicate (`OnCurve`: the relations of
  D2–D7) and a separate limb-bound predicate. A **total** `toPoint` returns the identity when
  `OnCurve` fails.
- Statements then read `hP : P.OnCurve` / `hb : P.Bounded`, and the result is `r.toPoint = …`.
- Keeping bounds separate follows the field-spec style. The proofs of `step*` never carry
  validity proofs inside terms.
- Name the predicate `OnCurve`, not `IsValid`, to avoid confusion with Rust's weaker `is_valid`.

**Q3. Limb-bound conventions.** Adopt the bounds in the D2–D7 table: `< 2^52` for
Edwards/Projective/Affine, `< 2^54` for Completed and both Niels forms. They are the weakest
uniform invariants that every operation preserves and every consumer accepts. They are checked
against the code in appendix A, Q2.

**Q4. X25519 and the twist.**
- **Recommendation, in two steps:**
  1. **(2a)** Prove that the code refines an executable transcription of the RFC 7748 `X25519`
     pseudocode, byte for byte and on all inputs. This is aeneas-use-cases'
     `mul_clamped_refines_X25519`: cheap, and needs no curve.
  2. **(2b)** Give it group meaning: model the twist as a second Montgomery curve (`B = 2`), define
     `xMul` as in M3, and prove `X25519 k u = u₀ (clamp k • Q)`. This is the minimum that is
     faithful on all 2^256 inputs.
- Restricting to inputs on the curve would leave the attacker-controlled case unspecified.
  x-only semantics over `F_{p²}` would need a second field.

**Q5. Ristretto.**
- **Recommendation:** no quotient type. State specs about Edwards representatives:
  - arithmetic as exact Edwards equality plus evenness;
  - `ct_eq` as `≈`;
  - `compress`/`decompress` via R3.
- Defer to after the Edwards and Montgomery specs.

**Q6. Constants and computation.**
- These facts are decidable but expensive in the kernel:
  - `8 • T₈ = 0` (cheap: three doublings);
  - `L • B = 0` (a sanity lemma, not needed by any spec);
  - the 1024 entries of `ED25519_BASEPOINT_TABLE` equal to `(j+1)·256^i • B`;
  - the NAF tables.
- `native_decide` is banned here. **Recommendation:**
  - prove the cheap ones with `decide` and kernel GMP;
  - use kernel-checked certificates as in aeneas-use-cases (§6):
    - `addOrderOf B = L` via an addition-chain certificate (`decide +kernel`);
    - `#E = 8L`, hence `(8·L) • P = 0` for every `P`, from an injective point encoding plus an
      explicit point of order `8L` (no point counting).

    Optional, since no spec needs them: add them only if a statement benefits (e.g.
    `is_torsion_free` corollaries, or a prime-order Ristretto group);
  - specify the big tables relative to their `create` function where possible;
  - leave the per-entry constant specs to the spec campaign, to be decided item by item.

**Q7. Equality semantics** (no new notion; fix the convention now):
- `EdwardsPoint::ct_eq` is projective equality, so it compares points via `toPoint`;
- `AffinePoint`/`AffineNiels` equality is coordinate-wise mod p;
- `CompressedEdwardsY` equality is byte equality;
- Ristretto equality is `≈`.

**Q8. Parity and sign.**
- Reuse the convention fixed by the existing field specs: `is_negative_spec` gives the parity of
  the canonical representative, and `sqrt_ratio_i_spec` returns the even root. C5 should be
  stated so that those specs connect directly.

**Q9. Decompression: relational or functional.**
- **Relational** (our draft): success ⇔ a square root exists; then `y` and the parity of `x` are
  as described. Keeps dalek-specific decoders out of `curve25519`.
- **Functional** (aeneas-use-cases): `r.map toPoint = edwardsDecode n`, with dalek's lenient
  decoder as a pure function in `Defs`. Shorter, and pins down rejection exactly, but the
  definition mirrors the algorithm.
- **Recommendation:** functional, with `edwardsDecode` in `Defs` (it is dalek's behaviour, not
  the curve's) and a characterisation lemma that gives the relational facts. The same pattern
  applies to Ristretto later (RFC 9496 decode as a pure function).

## 5. Next step after review

With the tiers and Q1–Q9 decided, Phase 2 implements:
- **`Curve25519` lib:** `Curve25519/Edwards.lean` (C2–C4), `Curve25519/Encoding.lean` (C5–C7),
  `Curve25519/Torsion.lean` (C8, C10), `Curve25519/X25519.lean` (RFC 7748 transcription, tier 2a),
  and `Curve25519/Montgomery.lean` (the Montgomery curve as the transport target; the rest of
  tier 2b later).
  Large proofs go in helper files.
- **`Defs` lib:** `Defs/FieldElement51.lean` (D1), `Defs/EllipticCurve.lean` (D3–D6),
  `Defs/Edwards.lean` (D2, D7, D9), `Defs/Window.lean` (D8).
- **Verification:**
  - sanity lemmas only;
  - `#print axioms` shows standard axioms only;
  - `--wfail` build and `runLinter`;
  - a smoke test that a draft spec such as `CompletedPoint::as_extended` can be stated.

## 6. Further ideas from `aeneas-use-cases` (Curve25519-Dalek)

`/home/oliver/Temp/aeneas-use-cases-main/Curve25519-Dalek` is an independent verification of the
same crate.
- 74 contracts, restated in `lean/Curve25519Dalek/EndToEnd.lean`.
- Lean 4.31, without the module system.
- Licences: MIT (Microsoft VCR) for its own parts, plus our own BAIF field layer under Apache 2.0.
- Serial 64-bit backend only, with **precomputed tables disabled**, so `mul_base` is variable-base
  and no table constants are checked.

**How it compares with Q1–Q8:**
- **Q1, group law.** They use the same idea as our (b), but lighter. Edwards points are a plain
  structure `{x y : F}`, with no group instance. An injective homomorphism `phi` into Mathlib's
  Weierstrass `Point` is proved with explicit `linear_combination` certificates
  (`Parity/EdwardsGroup.lean`: `phi_add`, `phi_neg`, `phi_inj`, the generic `G1–G4`, the special
  case `(0,−1) ↦ (0,0)`). Scalar multiplication is a custom recursion; associativity is never
  stated.
  - **Takeaway:** their certificates can make our formula-agreement proof cheaper.
  - With an injective homomorphism, `AddCommGroup` on our subtype follows by
    `Function.Injective.addCommGroup`. So we can still have a real group at little extra cost.
    I'd keep the group: statements with `n •`, `List.sum` and `addOrderOf` are clearer.
- **Q2, struct to point.** Same total `toPoint` (X/Z, Y/Z). They bundle bounds and curve facts in
  one `edwardsValid` (bound `< 2^53`). The intermediate structs are *relations* to a point
  (`NielsRep`, `CompRep`, `TableRep`).
  - Our split predicates and the `< 2^52` bound (forced by the affine-Niels path) stand.
  - Their relational form for Niels points is an alternative to our "recover X, Y from
    YpX/YmX" definition, if the definition turns out awkward.
- **Q4, X25519.** They don't model the twist. The group-level theorem requires `u` to come from a
  curve point (`X25519_eq_scalarMultiplication`). For all inputs they instead prove **byte-exact
  refinement to an executable RFC 7748 transcription** (`mul_clamped_refines_X25519`, no
  precondition, via a step-by-step ladder simulation `MontLadder.LRel`).
  - **New option:** add an executable RFC 7748 `x25519` function and a refinement theorem. It is
    cheap, needs no curve at all, and pins down the behaviour on twist inputs. Our twist model (M3)
    would then give it group meaning.
  - These can be staged: refinement first (tier 2a), group meaning later (tier 2b).
  - Reusable for the ladder proof: `LadderRepresentsU` (handles the degenerate `(0:0)` state),
    `ladder_invariant`.
- **Q5, Ristretto.** Theirs is weaker than our proposal.
  - `even := IsSquare (1 − y²)` is never connected to `2E`.
  - `ristretto_eq` is the RFC formula, never tied to coset equality.
  - No decode∘encode round trip.

  Reusable: the RFC 9496 functions as pure definitions (`sqrtRatio` with all branches,
  `ristrettoEncode`, `ristrettoDecode`, `elligator`, `uniformMap`) and their agreement proofs.
- **Q6, constants.** Their trust base includes ~100 `native_decide`/`bv_decide` axioms (Lucas
  certificates, byte lemmas); ours has none. But their **group certificates are kernel-only**
  (`decide +kernel`):
  - **Basepoint order:** `basePoint_order : addOrderOf B = L`, via an addition-chain certificate
    (`GroupCert.runBits`, `runBits_sound`).
  - **Group order without point counting:** `#E = 8L` follows from (1) an injective encoding
    `ptCode`, so `#E ≤ 2p+1`, and (2) an explicit point of order `8L`, so `8L ∣ #E`, and
    `2·8L > 2p+1`. Hence `(8·L) • P = 0` for every `P` (`cofactor_mul_order_nsmul`).

  **New possibility:** both are reusable without `native_decide`. They would also give the
  Ristretto group its prime order (`2E/E[4]` of order `L`) if we ever want to state it.
- **Decompression.** They characterise it **functionally**: `r.map toPoint = edwardsDecode n`,
  with a dalek-lenient `edwardsDecode` written as a pure function. Our proposal is relational.
  - Functional is shorter to state and pins down rejection exactly, but the definition mirrors the
    algorithm (the `sqrtRatio` branches).
  - Either works. Choose at the review: relational if `curve25519` should stay free of
    dalek-specific decoders, functional otherwise (the decoder would then live in `Defs`).

**Other ideas:**
- **Audit harness.** `DalekAudit.check` compares the kernel types of the restated statements and
  their axiom sets against an allow-list (`audit/axiom-policy.json`). Our spec summaries do the
  same with `recall` and `#guard_msgs`, so nothing to add.
- **Disabling `precomputed-tables`.** Our translation already covers both configurations, so the
  table specs remain, but they can be scheduled last: `mul_base` on the no-tables targets needs
  no table constants.

**Changes to the recommendations:**
- Q1 stays (b), with their homomorphism certificates as the template and `AddCommGroup` from
  injectivity.
- Q4 becomes two steps: an executable RFC 7748 refinement first, then twist semantics.
- Q6 adds the kernel certificates for `addOrderOf B = L` and `#E = 8L`, if we want them.
- The decompression style is a new open choice for the review.

---

## Appendix A: Edwards side, item by item

(Raw analysis; the numbering M1–M15 / R1–R13 here is this appendix's own, consolidated in §2.)

Scope: `src/backend/serial/curve_models.rs`, `src/edwards.rs`, `src/edwards/affine.rs`,
`src/window.rs`, `src/backend/serial/scalar_mul/*.rs`, `src/backend.rs` (dispatchers),
`src/traits.rs`, point constants in `src/constants.rs` / `src/backend/serial/u64/constants.rs`.
Only the `«x86_64-tables»` variants are listed; the other three targets have the same shape
(`no-tables` variants call `NafLookupTable5::from(&ED25519_BASEPOINT_POINT)` instead of the
precomputed tables, and `mul_base` uses `scalar * ED25519_BASEPOINT_POINT`).

Item list obtained from `translation.json` (all `is_local` functions/globals whose source is in
scope) cross-checked against the `def`s in `Funs.lean`. Excluded: derived `Clone`/`Copy`,
`Debug`/`Hash` (Charon-excluded), closure `call_mut`/`call_once` wrappers, and loop / loop-body
helpers (they get local specs in proof files).

**Not translated** (nothing to specify): the trait *default* methods
`VartimeMultiscalarMul::vartime_multiscalar_mul`,
`VartimePrecomputedMultiscalarMul::{vartime_multiscalar_mul, vartime_mixed_multiscalar_mul}`,
`BasepointTable::mul_base_clamped` (no instantiation in the crate); everything behind
`digest` (`map_to_curve`, `encode_to_curve`, `hash_to_curve`), `rand_core` (`random`), `group`
(`SubgroupPoint`, `Group`, `GroupEncoding`, `CofactorGroup`), `serde`, `lizard`.

**Public API** (needs a spec summary per the guidelines): `edwards.rs` items marked (pub);
everything in `backend/**`, `window.rs`, `edwards/affine.rs` (private module, `AffinePoint` not
re-exported), `traits::ValidityCheck` is crate-internal and only needs proved specs. The u64
point constants `ED25519_BASEPOINT_POINT`, `ED25519_BASEPOINT_128_POINT`, `EIGHT_TORSION`,
`ED25519_BASEPOINT_TABLE` are public through `pub use backend::serial::u64::constants::*` in
`constants.rs`; `AFFINE_ODD_MULTIPLES_*`, `BASEPOINT_ORDER` are `pub(crate)`.

#### Lean-name abbreviations used in the tables

| Abbrev | Expands to |
|---|---|
| `CM.` | `backend.serial.curve_models.` |
| `EPm.` | `edwards.«EdwardsPointx86_64-tables».` (inherent methods) |
| `EPI.` | `edwards.EdwardsPoint.«x86_64-tables».Insts.` (trait impls on by-value `EdwardsPoint`) |
| `S0EP.` | `«Shared0EdwardsPointx86_64-tables».Insts.` (trait impls on `&EdwardsPoint`, lhs) |
| `SAEP.` | `«SharedAEdwardsPointx86_64-tables».Insts.` |
| `‹EP›` | `EdwardsPointx86_64-tables` inside a «…» impl name |
| `‹PN›`, `‹AN›`, `‹CP›` | `ProjectiveNielsPointx86_64-tables`, `AffineNielsPointx86_64-tables`, `CompletedPointx86_64-tables` |
| `AFm.` / `AFI.` | `edwards.affine.«AffinePointx86_64-tables».` / `edwards.affine.AffinePoint.«x86_64-tables».Insts.` |
| `CEY.` | `edwards.CompressedEdwardsY.` |
| `BT(R).` | `edwards.EdwardsBasepointTable{,Radix32,Radix64,Radix128,Radix256}.«x86_64-tables».Insts.` |
| `C64.` | `backend.serial.u64.constants.` |

Notation in the postconditions: `⟦P⟧` = the mathematical point denoted by a struct value
(`toPoint`); `Valid_S(v)` = the representation predicate of struct `S` (algebraic relations +
`Z ≠ 0` + limb bounds, see §R); `0` = neutral element `(0,1)`; `n • P` = ℕ- or ℤ-smul in the
group `E(F_p)`; `s.asNat` = the *unreduced* integer value of the scalar bytes (existing
`Scalar.asNat`); `B` = Ed25519 basepoint; `fe.val` = `fe.asNat % p` (as `ZMod p`: `↑fe.asNat`).

---

#### 1. `src/backend/serial/curve_models.rs` (all crate-internal)

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `Identity for ProjectivePoint` | `CM.ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity` | `r = (0:1:1)`; `Valid_PP(r)`, `⟦r⟧ = 0` | – | R: Valid_PP, toPoint_PP; M: neutral element |
| `Identity for ProjectiveNielsPoint` | `CM.ProjectiveNielsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity` | `r = (1,1,1,0)`; `Valid_PN(r)`, `⟦r⟧ = 0` | – | R: Valid_PN; M: neutral |
| `Default for ProjectiveNielsPoint` | `CM.ProjectiveNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault.default` | same as identity | – | as above |
| `Identity for AffineNielsPoint` | `CM.AffineNielsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity` | `r = (1,1,0)`; `Valid_AN(r)`, `⟦r⟧ = 0` | – | R: Valid_AN; M: neutral |
| `Default for AffineNielsPoint` | `CM.AffineNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault.default` | same as identity | – | as above |
| `PartialEq for AffineNielsPoint` (derived) | `CM.AffineNielsPoint.«x86_64-tables».Insts.«CoreCmpPartialEqAffineNielsPointx86_64-tables».eq` | `b = true ↔` the three coordinates agree mod p (field-wise `FieldElement::eq`); for valid inputs `↔ ⟦a⟧ = ⟦b⟧` (affine Niels coords are unique) | (none for the coordinate form) | R: Valid_AN (only for the corollary) |
| `ValidityCheck for ProjectivePoint` | `CM.ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsValidityCheck.is_valid` | `b = true ↔ (Y²−X²)·Z² = Z⁴ + d·X²·Y²` in `ZMod p`. **Does not check `Z ≠ 0`**: `(0:Y:0)` and `(0:0:0)` return `true`. Corollary: `Z ≠ 0 → (b ↔ OnCurve_PP)` | limbs `< 2^54` | M: `d`; R: projective curve eq. |
| `ConditionallySelectable for ProjectiveNielsPoint` | `CM.ProjectiveNielsPoint.«x86_64-tables».Insts.SubtleConditionallySelectable.conditional_select` / `.conditional_assign` | `c=0 → r = a`, `c=1 → r = b` (struct equality) | `c.IsValid` | none (structural) |
| `ConditionallySelectable for AffineNielsPoint` | `CM.AffineNielsPoint.«x86_64-tables».Insts.SubtleConditionallySelectable.conditional_select` / `.conditional_assign` | same | `c.IsValid` | none |
| `ProjectivePoint::as_extended` | `CM.«ProjectivePointx86_64-tables».as_extended` | `r = (XZ, YZ, Z², XY)`; `Valid_PP(q) → Valid_EP(r) ∧ ⟦r⟧ = ⟦q⟧` | limbs `< 2^54` (coordinate form); `Valid_PP` | R: Valid_PP, Valid_EP, toPoint |
| `CompletedPoint::as_projective` | `CM.«CompletedPointx86_64-tables».as_projective` | `r = (XT, YZ, ZT)`; `Valid_CP(c) → Valid_PP(r) ∧ ⟦r⟧ = ⟦c⟧` | limbs `< 2^54` | R: Valid_CP, Valid_PP |
| `CompletedPoint::as_extended` | `CM.«CompletedPointx86_64-tables».as_extended` | `r = (XT, YZ, ZT, XY)`; `Valid_CP(c) → Valid_EP(r) ∧ ⟦r⟧ = ⟦c⟧` | limbs `< 2^54` | R: Valid_CP, Valid_EP |
| `ProjectivePoint::double` | `CM.«ProjectivePointx86_64-tables».double` | `Valid_CP(r) ∧ ⟦r⟧ = 2 • ⟦q⟧` (= `⟦q⟧ + ⟦q⟧`) | `Valid_PP(q)` (code needs X,Y `< 2^53`, Z `< 2^54`) | M: group law (doubling), completeness (`T,Z ≠ 0` of output); R: Valid_PP, Valid_CP |
| `Add<&ProjectiveNielsPoint> for &EdwardsPoint` | `S0EP.«CoreOpsArithAddSharedA‹PN›‹CP›».add` | `Valid_CP(r) ∧ ⟦r⟧ = ⟦self⟧ + ⟦other⟧` | `Valid_EP(self)`, `Valid_PN(other)` | M: group law + completeness; R: Valid_EP, Valid_PN, Valid_CP |
| `Sub<&ProjectiveNielsPoint> for &EdwardsPoint` | `S0EP.«CoreOpsArithSubSharedA‹PN›‹CP›».sub` | `Valid_CP(r) ∧ ⟦r⟧ = ⟦self⟧ − ⟦other⟧` | same | M: group law, negation |
| `Add<&AffineNielsPoint> for &EdwardsPoint` | `S0EP.«CoreOpsArithAddSharedA‹AN›‹CP›».add` | `Valid_CP(r) ∧ ⟦r⟧ = ⟦self⟧ + ⟦other⟧` | `Valid_EP(self)` (needs `Z < 2^52`, see §Q2), `Valid_AN(other)` | as above; R: Valid_AN |
| `Sub<&AffineNielsPoint> for &EdwardsPoint` | `S0EP.«CoreOpsArithSubSharedA‹AN›‹CP›».sub` | `Valid_CP(r) ∧ ⟦r⟧ = ⟦self⟧ − ⟦other⟧` | same | as above |
| `Neg for &ProjectiveNielsPoint` | `«Shared0ProjectiveNielsPointx86_64-tables».Insts.«CoreOpsArithNeg‹PN›».neg` | `r = (YmX, YpX, Z, −T2d)`; `Valid_PN(r) ∧ ⟦r⟧ = −⟦self⟧` | `Valid_PN(self)` (T2d `< 2^54`) | M: negation `−(x,y) = (−x,y)` |
| `Neg for &AffineNielsPoint` | `«Shared0AffineNielsPointx86_64-tables».Insts.«CoreOpsArithNeg‹AN›».neg` | `r = (ymx, ypx, −xy2d)`; `Valid_AN(r) ∧ ⟦r⟧ = −⟦self⟧` | `Valid_AN(self)` | M: negation |

Remarks.
- All of these can be stated purely in terms of `⟦·⟧` and the group, once the representation
  predicates exist. The old project instead stated many of them as raw coordinate congruences
  (e.g. its `AffineNielsPoint` `add_spec`: `Z' % p = (2Z + T·XY2D) % p …`, no curve semantics and
  no output limb bounds). Both forms are useful: a coordinate-level lemma for the proof, the
  `⟦·⟧`-level statement as the spec.
- `double` and the mixed additions are *complete* on Ed25519 (no exceptional inputs), which is
  what makes `Z ≠ 0`, `T ≠ 0` of the `CompletedPoint` provable: this needs `d` non-square and
  `a = −1` square in `F_p` (MATH).

#### 2. `src/edwards.rs`

##### 2a. `CompressedEdwardsY` (pub)

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `as_bytes` | `CEY.as_bytes` | `r = self.0` | – | none |
| `to_bytes` | `CEY.to_bytes` | `r = self.0` | – | none |
| `decompress` | `CEY.decompress.«x86_64-tables»` | Let `n = bytes.asNat 8`, `y = (n % 2^255 : ZMod p)` (**non-canonical `y ∈ [p, 2^255)` accepted and reduced**), `s = n / 2^255` (bit 255). (i) `r.isSome ↔ ∃ x, (x,y) ∈ E` (`↔ (y²−1)/(dy²+1)` is a square); (ii) `r = some e → Valid_EP(e) ∧ ⟦e⟧.y = y ∧ (⟦e⟧.x = 0 ∨ ⟦e⟧.x.val % 2 = s)`. Also `e.Z = ONE`. Edge case: **`x = 0` with sign bit 1 is accepted** and yields `x = 0` (−0 = 0), unlike RFC 8032 §5.1.3 step 4 (which rejects it, and also rejects `y ≥ p`). (ii) determines `⟦e⟧` uniquely. | – | M: curve eq., parity of `ZMod p` elements (`is_negative`), square-root existence (`IsSquare`); R: Valid_EP, toPoint_EP |
| `decompress::step_1` | `edwards.decompress.step_1.«x86_64-tables»` | `(c, X, Y, Z)`: `Y.asNat = n % 2^255`, Y limbs `< 2^51`; `Z = ONE`; `c.IsValid`; `c = 1 ↔ ∃ x, (x,y) ∈ E`; `c = 1 → X.val² · (d y² + 1) = y² − 1 ∧ X.val` even; X limbs `< 2^52` (direct restatement of `sqrt_ratio_i_spec` with `u = y²−1`, `v = dy²+1`, using `v ≠ 0` because `−1/d` is a non-square) | – | M: `d` non-square ⇒ `dy²+1 ≠ 0`; field only |
| `decompress::step_2` | `edwards.decompress.step_2.«x86_64-tables»` | `r = (X', Y, Z, X'·Y)` with `X' = s ? −X : X`; `Valid_EP(r)` and `⟦r⟧ = (X'.val, y)` when the step-1 relation holds and `Z = ONE` | X limbs `< 2^54`, Y `< 2^54` | as above |
| `TryFrom<&[u8]>` | `CEY.Insts.CoreConvertTryFromShared0SliceU8TryFromSliceError.try_from` | `ok r ↔ len = 32`, then `r.0 = slice`; else `Err` | – | none |
| `from_slice` | `CEY.from_slice` | same | – | none |
| `ConstantTimeEq` | `CEY.Insts.SubtleConstantTimeEq.ct_eq` | `c.IsValid ∧ (c = 1 ↔ self.0 = other.0)` — **byte equality, not point equality**: two encodings of one point (non-canonical y, or x=0 with sign 1) compare unequal | – | none |
| `PartialEq` | `CEY.Insts.CoreCmpPartialEqCompressedEdwardsY.eq` | `b ↔ self.0 = other.0` | – | none |
| `Identity` | `CEY.Insts.Curve25519_dalekTraitsIdentity.identity` | `r.0 = [1,0,…,0]` (`asNat = 1`); `= encode(0)` | – | M: encode (optional corollary) |
| `Default` | `CEY.Insts.CoreDefaultDefault.default` | `= identity` | – | none |
| `Zeroize` | `CEY.Insts.ZeroizeZeroize.zeroize` | result `= [1,0,…,0]` | – | none |

##### 2b. `EdwardsPoint` (pub unless marked)

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `Identity` | `EPI.Curve25519_dalekTraitsIdentity.identity` | `r = (0,1,1,0)`; `Valid_EP(r) ∧ ⟦r⟧ = 0` | – | R: Valid_EP; M: neutral |
| `Default` | `EPI.CoreDefaultDefault.default` | `= identity` | – | same |
| `Zeroize` | `EPI.ZeroizeZeroize.zeroize` | result `= (0,1,1,0)` | – | same |
| `ValidityCheck::is_valid` (crate) | `EPI.Curve25519_dalekTraitsValidityCheck.is_valid` | `b ↔ (Y²−X²)Z² = Z⁴ + dX²Y² ∧ XY = ZT` (mod p). **No `Z ≠ 0` check**: e.g. `(0,0,0,0)` and `(0,Y,0,0)` return `true`. Corollary: `Z ≠ 0 → (b ↔ OnCurve_EP)` | limbs `< 2^54` | M: `d`; R: OnCurve_EP |
| `ConditionallySelectable` | `EPI.SubtleConditionallySelectable.conditional_select` | `c=0 → r=a`, `c=1 → r=b` | `c.IsValid` | none |
| `ConstantTimeEq` | `EPI.SubtleConstantTimeEq.ct_eq` | `c.IsValid ∧ (c = 1 ↔ X₁Z₂ = X₂Z₁ ∧ Y₁Z₂ = Y₂Z₁` in `ZMod p`) — **T is not compared**; under `Valid_EP` of both: `c = 1 ↔ ⟦a⟧ = ⟦b⟧`. Without `Z ≠ 0` the relation is not point equality (any two `Z = 0` values compare equal) | limbs `< 2^54` (coordinate form); validity for the point form | R: toPoint_EP |
| `PartialEq` | `EPI.«CoreCmpPartialEq‹EP›».eq` | `b ↔ (same)` | same | same |
| `as_projective_niels` (crate) | `EPm.as_projective_niels` | `r = (Y+X, Y−X, Z, 2d·T)`; `Valid_PN(r) ∧ ⟦r⟧ = ⟦self⟧` | `Valid_EP(self)` | M: `d`; R: Valid_PN |
| `as_projective` (crate) | `EPm.as_projective` | `r = (X,Y,Z)`; `Valid_PP(r) ∧ ⟦r⟧ = ⟦self⟧` | `Valid_EP(self)` | R: Valid_PP |
| `as_affine_niels` (crate) | `EPm.as_affine_niels` | `r = (y+x, y−x, 2d·xy)` with `x = X/Z`, `y = Y/Z`; `Valid_AN(r) ∧ ⟦r⟧ = ⟦self⟧` | `Valid_EP(self)` | R: Valid_AN |
| `to_affine` (crate) | `EPm.to_affine` | `Valid_AF(r) ∧ ⟦r⟧ = ⟦self⟧` (`r.x = X/Z`, `r.y = Y/Z`) | `Valid_EP(self)` | R: Valid_AF |
| `to_montgomery` | `EPm.to_montgomery` | `r.0.asNat 8 = (((1+y)/(1−y) : ZMod p)).val` where `(x,y) = ⟦self⟧`, **with Lean's `a/0 = 0`**: matches dalek's exceptional case (identity `y=1` ↦ `u = 0`). Coordinate form: `u·(Z−Y) = Z+Y` if `Z ≠ Y`, `u = 0` if `Z = Y`; output canonical (`< p`) | `Valid_EP(self)` (for the point form); limbs `< 2^53` for the code | M: birational map Edwards→Montgomery `u = (1+y)/(1−y)` (just a formula; no Montgomery curve needed for this spec); canonical byte encoding of `ZMod p` |
| `to_montgomery_batch` | `EPm.to_montgomery_batch` | `r.len = eds.len ∧ ∀ i, r[i] = to_montgomery(eds[i])` (same formula, zero denominators give `u = 0`, as `invert_batch_alloc` keeps zeros) | `∀ i, Valid_EP(eds[i])` | as `to_montgomery` |
| `compress` | `EPm.compress` | `r.0.asNat 8 = encode(⟦self⟧)` where `encode(x,y) = y.val + 2^255·(x.val % 2)` (RFC 8032 §5.1.2) | `Valid_EP(self)` | M: encode, parity (`is_negative`) |
| `compress_batch` (const N) | `EPm.compress_batch` | `∀ i < N, r[i].0.asNat 8 = encode(⟦inputs[i]⟧)` | `∀ i, Valid_EP(inputs[i])` | same |
| `compress_batch_alloc` | `EPm.compress_batch_alloc` | `r.len = inputs.len ∧ ∀ i, r[i] = encode(⟦inputs[i]⟧)` | same | same |
| `double` (crate) | `EPm.double` | `Valid_EP(r) ∧ ⟦r⟧ = 2 • ⟦self⟧` | `Valid_EP(self)` | M: group law |
| `Add` `&a + &b` | `S0EP.«CoreOpsArithAddSharedA‹EP›‹EP›».add` | `Valid_EP(r) ∧ ⟦r⟧ = ⟦a⟧ + ⟦b⟧` | `Valid_EP(a)`, `Valid_EP(b)` | M: group law |
| `Add` by-value variants | `EPI.«CoreOpsArithAdd‹EP›‹EP›».add`, `EPI.«CoreOpsArithAddSharedB‹EP›‹EP›».add`, `SAEP.«CoreOpsArithAdd‹EP›‹EP›».add` | same | same | same |
| `AddAssign` (both) | `EPI.«CoreOpsArithAddAssignSharedA‹EP›».add_assign`, `EPI.«CoreOpsArithAddAssign‹EP›».add_assign` | same | same | same |
| `Sub` `&a − &b` + variants | `S0EP.«CoreOpsArithSubSharedA‹EP›‹EP›».sub`, `EPI.«CoreOpsArithSub‹EP›‹EP›».sub`, `EPI.«CoreOpsArithSubSharedB‹EP›‹EP›».sub`, `SAEP.«CoreOpsArithSub‹EP›‹EP›».sub` | `Valid_EP(r) ∧ ⟦r⟧ = ⟦a⟧ − ⟦b⟧` | same | M: group (neg) |
| `SubAssign` (both) | `EPI.«CoreOpsArithSubAssignSharedA‹EP›».sub_assign`, `EPI.«CoreOpsArithSubAssign‹EP›».sub_assign` | same | same | same |
| `Sum<T>` | `EPI.CoreIterTraitsAccumSum.sum` | with `iterInst.Yields iter xs`, `borrow` returning `ps` (as in `Scalar` `sum_spec`): `Valid_EP(r) ∧ ⟦r⟧ = (ps.map ⟦·⟧).sum` | `∀ q ∈ ps, Valid_EP(q)` | M: `AddCommMonoid` (List.sum); R: `Iterator.Yields` (exists), Borrow hypothesis |
| `Neg` `-&P`, `-P` | `S0EP.«CoreOpsArithNeg‹EP›».neg`, `EPI.«CoreOpsArithNeg‹EP›».neg` | `r = (−X, Y, Z, −T)`; `Valid_EP(r) ∧ ⟦r⟧ = −⟦self⟧` | `Valid_EP(self)` | M: negation |
| `Mul<&Scalar> for &EdwardsPoint` | `S0EP.«CoreOpsArithMulSharedAScalar‹EP›».mul` | `Valid_EP(r) ∧ ⟦r⟧ = s.asNat • ⟦self⟧` — **unreduced integer**, not `s mod L` (matters for torsion: `is_torsion_free` calls it with `s.asNat = L`) | `Valid_EP(self)`, `s.asNat < 2^255` (from `as_radix_16`; the crate's `Scalar` invariant) | M: `ℕ`-smul; R: Scalar.asNat (exists) |
| `Mul<&EdwardsPoint> for &Scalar` | `Shared0Scalar.Insts.«CoreOpsArithMulSharedA‹EP›‹EP›».mul` | same | same | same |
| by-value Mul variants (6) | `EPI.«CoreOpsArithMulScalar‹EP›».mul`, `EPI.«CoreOpsArithMulSharedBScalar‹EP›».mul`, `SAEP.«CoreOpsArithMulScalar‹EP›».mul`, `scalar.Scalar.Insts.«CoreOpsArithMul‹EP›‹EP›».mul`, `scalar.Scalar.Insts.«CoreOpsArithMulSharedB‹EP›‹EP›».mul`, `SharedAScalar.Insts.«CoreOpsArithMul‹EP›‹EP›».mul` | same | same | same |
| `MulAssign<&Scalar>`, `MulAssign<Scalar>` | `EPI.CoreOpsArithMulAssignSharedAScalar.mul_assign`, `EPI.CoreOpsArithMulAssignScalar.mul_assign` | same | same | same |
| `mul_base` | `EPm.mul_base` | `Valid_EP(r) ∧ ⟦r⟧ = s.asNat • B` | `s.asNat < 2^255` | M: basepoint `B` |
| `mul_clamped` | `EPm.mul_clamped` | `Valid_EP(r) ∧ ⟦r⟧ = clamp(bytes.asNat) • ⟦self⟧` with `clamp(n) = 2^254 + 8·⌊(n % 2^254)/8⌋` (RFC 7748 `decodeScalar25519`; equals the existing `clamp_integer_spec` value) | `Valid_EP(self)` | M: clamp |
| `mul_base_clamped` | `EPm.mul_base_clamped` | `Valid_EP(r) ∧ ⟦r⟧ = clamp(bytes.asNat) • B` | – | M: clamp, B |
| `MultiscalarMul::multiscalar_mul` (pub, alloc) | `EPI.«Curve25519_dalekTraitsMultiscalarMul‹EP›».multiscalar_mul` | `Yields` scalars `ss`, points `ps` (via Borrow): `Valid_EP(r) ∧ ⟦r⟧ = Σᵢ ss[i].asNat • ⟦ps[i]⟧` | `ss.length = ps.length` (patched `massert`), `∀ s, s.asNat < 2^255`, `∀ P, Valid_EP(P)` | M: group only (`List.sum`/`zipWith`); R: Yields, Borrow |
| `VartimeMultiscalarMul::optional_multiscalar_mul` | `EPI.«Curve25519_dalekTraitsVartimeMultiscalarMul‹EP›».optional_multiscalar_mul` | points are `Option`s: `r = none ↔ ∃ i, ps[i] = none`; `r = some e → Valid_EP(e) ∧ ⟦e⟧ = Σ ss[i].asNat • ⟦ps[i].get⟧` (dispatches on `size < 190` Straus/Pippenger: same result) | same as above (validity for the `some` points) | same |
| `VartimeEdwardsPrecomputation::new` | `edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMul‹EP›».new` | `r` *represents* the static points `ps` (R: `Precomp.Represents r ps`) | `∀ P ∈ ps, Valid_EP(P)` | R: precomputation predicate (abstract list of points) |
| `…::len` | `….len` | `r = ps.length` (for `Represents self ps`) | `Represents self ps` | same |
| `…::is_empty` | `….is_empty` | `r ↔ ps = []` | same | same |
| `…::optional_mixed_multiscalar_mul` | `….optional_mixed_multiscalar_mul` | static scalars `ss` (`ss.length ≤ ps.length`, panics otherwise), dynamic scalars `ds`, dynamic `Option` points `qs` (`ds.length = qs.length`, panics otherwise, but only after the `None` check): `r = none ↔ ∃ i, qs[i] = none`; else `⟦r⟧ = Σ_{i<|ss|} ss[i].asNat • ps[i] + Σ ds[i].asNat • ⟦qs[i]⟧` (missing static scalars count as 0) | `Represents self ps`; all scalars `< 2^255`; dynamic points valid | M: group; R: Represents, Yields |
| `vartime_double_scalar_mul_basepoint` | `EPm.vartime_double_scalar_mul_basepoint` | `Valid_EP(r) ∧ ⟦r⟧ = a.asNat • ⟦A⟧ + b.asNat • B` | `Valid_EP(A)`, `a.asNat, b.asNat < 2^255` (NAF) | M: B |
| `vartime_triple_scalar_mul_basepoint` | `EPm.vartime_triple_scalar_mul_basepoint` | `Valid_EP(r) ∧ ⟦r⟧ = a1.asNat • ⟦A1⟧ + a2.asNat • ⟦A2⟧ + b.asNat • B` | `Valid_EP(A1)`, `Valid_EP(A2)`; `a1, a2 : HalfWidthScalar` (`< 2^128` by type); `b` **any** (split into two 128-bit halves; no `2^255` bound needed) | M: B (and `2^128 • B` for the table) |
| `mul_by_cofactor` | `EPm.mul_by_cofactor` | `Valid_EP(r) ∧ ⟦r⟧ = 8 • ⟦self⟧` | `Valid_EP(self)` | M: cofactor 8 (just a numeral) |
| `mul_by_pow_2` (crate) | `EPm.mul_by_pow_2` | `Valid_EP(r) ∧ ⟦r⟧ = 2^k • ⟦self⟧` | `k > 0` (`massert`), `Valid_EP(self)` | group |
| `is_small_order` | `EPm.is_small_order` | `b ↔ 8 • ⟦self⟧ = 0` | `Valid_EP(self)` | group only (`E[8]` = kernel of `8•`) |
| `is_torsion_free` | `EPm.is_torsion_free` | `b ↔ L • ⟦self⟧ = 0` | `Valid_EP(self)` | M: `L` (exists in `Curve25519`); group only |

##### 2c. Basepoint tables (pub; five types via `impl_basepoint_table!`, radix `w ∈ {4,5,6,7,8}`)

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `BasepointTable::create` (×5) | `BT(R).«Curve25519_dalekTraitsBasepointTable‹EP›».create` | `Table_w(r, ⟦basepoint⟧)`: `∀ i < 32, ∀ j < 2^(w−1)`, entry `r.0[i].0[j]` is `Valid_AN` with `⟦·⟧ = (j+1)·2^(2wi) • P` | `Valid_EP(basepoint)` | R: Table_w predicate (built on LookupTable predicate) |
| `BasepointTable::basepoint` (×5) | `….basepoint` | `Valid_EP(r) ∧ ⟦r⟧ = P` | `Table_w(self, P)` | same |
| `BasepointTable::mul_base` (×5) | `….mul_base` | `Valid_EP(r) ∧ ⟦r⟧ = s.asNat • P` | `Table_w(self, P)`, `s.asNat < 2^255` (`as_radix_2w`) | same; group |
| `Mul<&Scalar> for &Table` (×5) | `«SharedAEdwardsBasepointTable{,Radix32,…}x86_64-tables».Insts.«CoreOpsArithMulSharedBScalar‹EP›».mul` | same as `mul_base` | same | same |
| `Mul<&Table> for &Scalar` (×5) | `SharedBScalar.Insts.«CoreOpsArithMulSharedAEdwardsBasepointTable{,Radix32,…}x86_64-tables‹EP›».mul` | same | same | same |
| `From<&TableA> for TableB` (20 impls) | `BT(R).«CoreConvertFromSharedAEdwardsBasepointTable…x86_64-tables».from` | `Table_wA(t, P) → Table_wB(r, P)` | `Table_wA(t, P)` | same |

Note: `constants::ED25519_BASEPOINT_TABLE` has type `EdwardsBasepointTable` (radix 16, w = 4).

#### 3. `src/edwards/affine.rs` (crate-internal: private module)

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `ConstantTimeEq` | `AFI.SubtleConstantTimeEq.ct_eq` | `c.IsValid ∧ (c = 1 ↔ x₁ ≡ x₂ ∧ y₁ ≡ y₂ mod p)`; for valid: `↔ ⟦a⟧ = ⟦b⟧` (no projective scaling here) | – | R: Valid_AF |
| `PartialEq` | `AFI.«CoreCmpPartialEqAffinePointx86_64-tables».eq` | same as bool | – | same |
| `ConditionallySelectable` | `AFI.SubtleConditionallySelectable.conditional_select` | structural | `c.IsValid` | none |
| `Identity` | `AFI.Curve25519_dalekTraitsIdentity.identity` | `r = (0,1)`; `Valid_AF(r) ∧ ⟦r⟧ = 0` | – | M: neutral |
| `Default` | `AFI.CoreDefaultDefault.default` | `= identity` | – | same |
| `to_edwards` | `AFm.to_edwards` | `r = (x, y, 1, xy)`; `Valid_EP(r) ∧ ⟦r⟧ = ⟦self⟧` | `Valid_AF(self)` (limbs `< 2^52`, so that r meets the EdwardsPoint bound) | R: Valid_AF, Valid_EP |
| `compress` | `AFm.compress` | `r.0.asNat 8 = encode(⟦self⟧) = y.val + 2^255·(x.val % 2)`. (`s[31] ^= sign<<7` is an OR since `to_bytes` is canonical, `< 2^255`) | none for the coordinate form `y.val + 2^255·(x.val%2)`; `Valid_AF` for the `encode ⟦·⟧` form | M: encode, parity |
| `Mul<AffinePoint> for Scalar`, `Mul<&AffinePoint> for Scalar` | `scalar.Scalar.Insts.«CoreOpsArithMulAffinePointx86_64-tables‹EP›».mul`, `scalar.Scalar.Insts.«CoreOpsArithMulShared0AffinePointx86_64-tables‹EP›».mul` | `Valid_EP(r) ∧ ⟦r⟧ = s.asNat • ⟦rhs⟧` | `Valid_AF(rhs)`, `s.asNat < 2^255` | group |

#### 4. `src/window.rs` (crate-internal)

Tables are generic in `T` in Lean (`window.LookupTable.select {T} identityInst selectInst negInst`),
`From` impls are per concrete `T ∈ {ProjectiveNielsPoint, AffineNielsPoint}`.

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `LookupTable{,Radix32,Radix64,Radix128,Radix256}::select` (size `n` = 8,16,32,64,128) | `window.LookupTable.select`, `window.LookupTableRadix32.select`, … `Radix256.select` | specialised to `T = PN` and `T = AN`: if `LUT_n(self, P)` (entry `j` valid with `⟦·⟧ = (j+1)•P`) then `Valid_T(r) ∧ ⟦r⟧ = (x : ℤ) • P` | `−n ≤ x ≤ n` (`massert`s; for radix 256 the upper check is vacuous for `i8`, and `x = −128` works: `|x| = 128 = n`) | M: ℤ-smul; R: LUT predicate, Valid_PN/Valid_AN |
| `select` (generic alternative) | same | structural: `r = (x ≥ 0 ? id : neg)(x = 0 ? identity : self.0[|x|−1])`, given instance behaviour hypotheses (as old `is_identity_spec`) | same | none |
| `Default` (×5) | `window.LookupTable.Insts.CoreDefaultDefault.default`, … | all entries `T::default()` (= identity for both Niels types) — a valid table for `P = 0` only | – | none |
| `From<&EdwardsPoint> for LookupTable…<ProjectiveNielsPoint>` (×5) | `window.«LookupTable{,Radix32,…}ProjectiveNielsPointx86_64-tables».Insts.«CoreConvertFromSharedA‹EP›».from` | `LUT_n(r, ⟦P⟧)` | `Valid_EP(P)` | R: LUT, Valid_PN |
| `From<&EdwardsPoint> for LookupTable…<AffineNielsPoint>` (×5) | `window.«LookupTable{,Radix32,…}AffineNielsPointx86_64-tables».Insts.«CoreConvertFromSharedA‹EP›».from` | `LUT_n(r, ⟦P⟧)` | `Valid_EP(P)` | R: LUT, Valid_AN |
| `NafLookupTable5::select` | `window.NafLookupTable5.select` | `r = self.0[x/2]` (purely structural; with `NAF5(self, A)`: `⟦r⟧ = x • A`) | `x` odd (`massert x & 1 = 1`), `x < 16` | R: NAF table predicate (entry k = (2k+1)•A) |
| `NafLookupTable8::select` | `window.NafLookupTable8.select` | `r = self.0[x/2]` | `x` odd, `x < 128` | same |
| `From<&EdwardsPoint> for NafLookupTable5<PN>` / `<AN>` | `window.«NafLookupTable5{ProjectiveNiels,AffineNiels}Pointx86_64-tables».Insts.«CoreConvertFromSharedA‹EP›».from` | `NAF5(r, ⟦A⟧)`: `∀ k < 8`, entry valid, `⟦·⟧ = (2k+1)•⟦A⟧` | `Valid_EP(A)` | same |
| `From<&EdwardsPoint> for NafLookupTable8<PN>` / `<AN>` | `window.«NafLookupTable8{…}Pointx86_64-tables».Insts.«CoreConvertFromSharedA‹EP›».from` | `NAF8(r, ⟦A⟧)`: `∀ k < 64` | `Valid_EP(A)` | same |

#### 5. `src/backend/serial/scalar_mul/*.rs` and `src/backend.rs` (crate-internal)

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `variable_base::mul` | `backend.serial.scalar_mul.variable_base.mul.«x86_64-tables»` | `Valid_EP(r) ∧ ⟦r⟧ = s.asNat • ⟦point⟧` | `Valid_EP(point)`, `s.asNat < 2^255` | group |
| `vartime_double_base::mul` | `backend.serial.scalar_mul.vartime_double_base.mul.«x86_64-tables»` | `⟦r⟧ = a.asNat • ⟦A⟧ + b.asNat • B` | `Valid_EP(A)`, `a,b < 2^255` | M: B; R: `NAF8(AFFINE_ODD_MULTIPLES_OF_BASEPOINT, B)` |
| `vartime_triple_base::mul_128_128_256` | `backend.serial.scalar_mul.vartime_triple_base.mul_128_128_256.«x86_64-tables»` | `⟦r⟧ = a1•⟦A1⟧ + a2•⟦A2⟧ + b•B` | `Valid_EP(A1,A2)`; halves `< 2^128` by type | M: B, `2^128•B`; R: NAF5 table of `2^128•B`; needs "NAF digits of `x < 2^128` vanish above index 128" (§Q8) |
| `Straus::multiscalar_mul` | `backend.serial.scalar_mul.straus.Straus.Insts.«Curve25519_dalekTraitsMultiscalarMul‹EP›».multiscalar_mul` | `⟦r⟧ = Σ_{i < min(|ss|,|ps|)} ss[i].asNat • ⟦ps[i]⟧` (index loop to the shorter length after patch) | all scalars `< 2^255`, all points valid | group; Yields/Borrow |
| `Straus::optional_multiscalar_mul` | `backend.serial.scalar_mul.straus.Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMul‹EP›».optional_multiscalar_mul` | `none ↔` some point is `none` (all points are read); else sum over `min` length | same | same |
| `Pippenger::optional_multiscalar_mul` | `backend.serial.scalar_mul.pippenger.Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMul‹EP›».optional_multiscalar_mul` | `none ↔` a `none` among the first `min(|ss|,|ps|)` points (zip); else `Σ` over the zipped pairs. Window `w ∈ {6,7,8}`; result independent of `w` | scalars `< 2^255` (`as_radix_2w`), points valid | group |
| `VartimePrecomputedStraus::new` (serial) | `backend.serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-tables».Insts.«…VartimePrecomputedMultiscalarMul‹EP›».new` | `static_lookup_tables[i]` is `NAF8<AN>` of `⟦ps[i]⟧`, length `= |ps|` | points valid | R: NAF8, Represents |
| `…::len`, `…::is_empty` | `….len`, `….is_empty` | `= static_lookup_tables.len`, `= (len = 0)` | – | none |
| `…::optional_mixed_multiscalar_mul` | `….optional_mixed_multiscalar_mul` | as in §2b | as in §2b | same |
| `backend::get_selected_backend` | `backend.get_selected_backend` | `r = Serial` | – | none |
| `backend::variable_base_mul` etc. (dispatchers) | `backend.variable_base_mul.«x86_64-tables»`, `backend.vartime_double_base_mul.«x86_64-tables»`, `backend.vartime_triple_base_mul_128_128_256.«x86_64-tables»`, `backend.straus_multiscalar_mul.«x86_64-tables»`, `backend.straus_optional_multiscalar_mul.«x86_64-tables»`, `backend.pippenger_optional_multiscalar_mul.«x86_64-tables»` | same as the serial function | same | same |
| `backend::VartimePrecomputedStraus::{new,len,is_empty,optional_mixed_multiscalar_mul}` (enum, only `Scalar` variant) | `backend.«VartimePrecomputedStrausx86_64-tables».{new,len,is_empty,optional_mixed_multiscalar_mul}` | same as serial, through the `Scalar` variant | same | same |

#### 6. `src/traits.rs`

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `impl<T: ConstantTimeEq + Identity> IsIdentity for T` | `traits.IsIdentity.Blanket.is_identity` | generic: `b ↔ ct_eq self identity = 1` (conditional on instance specs, like the old project's `is_identity_spec`). Specialisations: EdwardsPoint `b ↔ ⟦self⟧ = 0` (coordinate form `X ≡ 0 ∧ Y ≡ Z`, for `Z ≠ 0`); CompressedEdwardsY `b ↔ bytes = [1,0,…]`; AffinePoint `b ↔ (x,y) ≡ (0,1)` | instance specs; validity for the point form | M: neutral |
| `Identity`, `ValidityCheck`, `BasepointTable`, `MultiscalarMul`, `VartimeMultiscalarMul`, `VartimePrecomputedMultiscalarMul` | trait structures in `Types.lean` | no functions of their own (defaults not translated); their impls are listed above | – | – |

#### 7. Point constants (`constants.rs`, `backend/serial/u64/constants.rs`)

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `ED25519_BASEPOINT_POINT` (pub) | `C64.ED25519_BASEPOINT_POINT.«x86_64-tables»` | `Valid_EP(r) ∧ ⟦r⟧ = B` (limbs `< 2^51`, `Z = 1`) | – | M: B |
| `ED25519_BASEPOINT_128_POINT` (pub) | `C64.ED25519_BASEPOINT_128_POINT.«x86_64-tables»` | `Valid_EP(r) ∧ ⟦r⟧ = 2^128 • B` (Z ≠ 1 here) | – | M: B, smul |
| `ED25519_BASEPOINT_COMPRESSED` (pub) | `constants.ED25519_BASEPOINT_COMPRESSED` | `r.0.asNat 8 = encode(B)` (y = 4/5, sign 0) | – | M: encode, B |
| `EIGHT_TORSION` (pub) + `_INNER_DOC_HIDDEN` | `C64.EIGHT_TORSION.«x86_64-tables»`, `C64.EIGHT_TORSION_INNER_DOC_HIDDEN.«x86_64-tables»` | `∃ T₈ (or a named point), 8•T₈ = 0 ∧ 4•T₈ ≠ 0 ∧ ∀ i < 8, Valid_EP(r[i]) ∧ ⟦r[i]⟧ = i • T₈`. (Doc claim "= E[8], cyclic" would additionally need `#E[8] = 8`; not needed by any other spec) | – | M: torsion point of order 8 (explicit or existential) |
| `BASEPOINT_ORDER` (crate) | `constants.BASEPOINT_ORDER` | `r.asNat = L` (**not canonical**: `L ≥ L`, `as_radix_16` still OK since `L < 2^255`) | – | M: L |
| `ED25519_BASEPOINT_TABLE` (pub) + `_INNER_DOC_HIDDEN` | `C64.ED25519_BASEPOINT_TABLE`, `C64.ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN` | `Table_4(r, B)`: `∀ i<32, j<8`, entry valid AN with `⟦·⟧ = (j+1)·256^i • B` | – | M: B; R: Table_w |
| `AFFINE_ODD_MULTIPLES_OF_BASEPOINT` (crate) | `C64.AFFINE_ODD_MULTIPLES_OF_BASEPOINT` | `NAF8<AN>(r, B)`: `∀ k<64, ⟦r.0[k]⟧ = (2k+1)•B` | – | M: B; R: NAF8 |
| `AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128` (crate) | `C64.AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128` | `NAF5<PN>(r, 2^128•B)` (**`ProjectiveNiels`, despite the name**) | – | M: B; R: NAF5, Valid_PN |
| `EDWARDS_D`, `EDWARDS_D2` | `C64.EDWARDS_D`, `C64.EDWARDS_D2` | already proved (field level) | – | M: d |
| `X25519_BASEPOINT`, `X25519_LOW_ORDER_POINTS`, `RISTRETTO_*` | `constants.*` | Montgomery / Ristretto side — out of this scope | | |

---

#### M. Consolidated MATH notions (curve-level, independent of dalek)

| # | Notion | Needed by |
|---|---|---|
| M1 | `F = ZMod p`, `a = −1`, `d` (exist in `Curve25519/Basic.lean`) | everything |
| M2 | Ed25519 affine curve `−x² + y² = 1 + d x² y²` and the point type `E` (subtype/structure) | every point spec (≈ all items) |
| M3 | Group law on `E` (`+`, `0 = (0,1)`, `−(x,y) = (−x,y)`) with `AddCommGroup` (needed for `n •`, `List.sum`, and for the algorithm proofs: associativity/commutativity) | Add/Sub/Neg (all variants), double, mul_by_pow_2, mul_by_cofactor, all scalar muls, Sum, multiscalar, tables, is_small_order, is_torsion_free, constants |
| M4 | Completeness of the addition law on Ed25519 (denominators `1 ± d x₁x₂y₁y₂ ≠ 0`: `d` non-square, `−1` square mod p) | proofs of every curve_models op (`Z, T ≠ 0` in `Valid_CP`), and decompress (`dy²+1 ≠ 0`) |
| M5 | `ℕ`- and `ℤ`-smul (from M3) | scalar muls, `select` (negative digits → ℤ), tables, constants |
| M6 | Prime `L` (exists) | is_torsion_free, BASEPOINT_ORDER |
| M7 | Basepoint `B` (explicit: `y = 4/5`, `x` the even root) | mul_base, mul_base_clamped, vartime_double/triple, all basepoint constants and tables (7 items + 10 table-mul variants) |
| M8 | Parity / `is_negative` of `ZMod p` (`x.val % 2`) | compress, compress_batch(_alloc), AffinePoint::compress, decompress, BASEPOINT_COMPRESSED |
| M9 | Encoding `encode(P) = P.y.val + 2^255·(P.x.val % 2)` (RFC 8032 §5.1.2) | compress ×3, AffinePoint::compress, CompressedEdwardsY::identity (corollary), BASEPOINT_COMPRESSED |
| M10 | Decoding: *no definition needed* — characterised by `isSome ↔ ∃ x, (x,y) ∈ E` and `y`, `x = 0 ∨ parity(x) = sign`; with `y := (n % 2^255) mod p` (non-canonical y accepted, x=0/sign=1 accepted). If a `decode` function is wanted, it must be *dalek's* lenient decoding, not RFC 8032's strict one | decompress (+ step_1/step_2) |
| M11 | Square roots / `IsSquare` in `F` (existence of `x` with `x²(dy²+1) = y²−1`) | decompress, step_1 |
| M12 | Edwards→Montgomery map `u = (1+y)/(1−y)` (as a formula on `F`, with `/0 = 0` giving the exceptional case). No Montgomery curve model needed for edwards.rs | to_montgomery, to_montgomery_batch |
| M13 | Clamping `clamp(n) = 2^254 + 8·⌊(n mod 2^254)/8⌋` (RFC 7748) — or reuse `clamp_integer`'s spec value | mul_clamped, mul_base_clamped |
| M14 | A point of order 8 (`8•T = 0 ∧ 4•T ≠ 0`) | EIGHT_TORSION only |
| M15 | Small order / torsion-free: *no new notion* — `8 • P = 0`, `L • P = 0` | is_small_order, is_torsion_free |

Not needed by any statement: the group order `#E = 8L`, `L • B = 0`, cyclicity of `E[8]`,
prime-order subgroup as a `Subgroup`, quotient by torsion, the Montgomery curve, projective
space. (`L • B = 0` and `B ≠ 0` are nice sanity lemmas for the constants file only.)

Items specifiable purely in terms of the group (given M2/M3 + representation): all Add/Sub/Neg,
double, mul_by_pow_2, mul_by_cofactor, is_small_order, is_torsion_free (+L), `Mul` by scalar,
Sum, multiscalar_mul, optional_multiscalar_mul, Straus, Pippenger, precomputed Straus, table
select/From/create/mul_base/basepoint/From-conversions. Need further notions: compress-family
(M8, M9), decompress (M8, M10, M11), to_montgomery(_batch) (M12), clamped muls (M13),
basepoint-dependent items (M7), EIGHT_TORSION (M14).

#### R. Consolidated REPRESENTATION notions

Field-level: `fe.val : ZMod p := ↑fe.asNat` (old `toField`; `asNat` exists). All relations below
are equalities in `ZMod p` of the `.val`s.

| # | Notion | Exact algebraic content (from the code) | Limb bound (simplest that all uses allow, §Q2) | Needed by |
|---|---|---|---|---|
| R1 | `Valid_EP` / `EdwardsPoint.toPoint` | `Z ≠ 0`, `X·Y = Z·T`, `(Y²−X²)Z² = Z⁴ + dX²Y²`; `⟦·⟧ = (X/Z, Y/Z)` | all four `< 2^52` | ≈ every item in edwards.rs, scalar_mul, window `From`, tables, constants |
| R2 | `Valid_PP` / toPoint | `Z ≠ 0`, `(Y²−X²)Z² = Z⁴ + dX²Y²`; `⟦·⟧ = (X/Z, Y/Z)` | `< 2^52` | as_projective, double, as_extended, CompletedPoint::as_projective, mul_by_pow_2, vartime loops |
| R3 | `Valid_CP` / toPoint | `Z ≠ 0`, `T ≠ 0`, `−X²T² + Y²Z² = Z²T² + dX²Y²`; `⟦·⟧ = (X/Z, Y/T)` (P¹×P¹) | `< 2^54` (Y reaches `2^53`, Z reaches `2^53+2^52`) | double, the four mixed Add/Sub, as_projective, as_extended |
| R4 | `Valid_PN` / toPoint | `Z ≠ 0`; with `X := (YpX − YmX)/2`, `Y := (YpX + YmX)/2`: curve eq. of R2 on `(X:Y:Z)` and `T2d·Z = 2d·X·Y`; `⟦·⟧ = (X/Z, Y/Z)` | `< 2^54` (outputs `< 2^53`) | as_projective_niels, Add/Sub PN, Neg PN, PN identity/default/select, LookupTable<PN>, NAF5<PN>, NAF8<PN>, AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128 |
| R5 | `Valid_AN` / toPoint | with `x := (ypx − ymx)/2`, `y := (ypx + ymx)/2`: `(x,y) ∈ E`, `xy2d = 2d·x·y`; `⟦·⟧ = (x, y)` | `< 2^54` (outputs `< 2^53`; table constants `< 2^52`) | as_affine_niels, Add/Sub AN, Neg AN, AN eq/identity/default/select, LookupTable<AN>, NAF5/8<AN>, basepoint tables, ED25519_BASEPOINT_TABLE, AFFINE_ODD_MULTIPLES_OF_BASEPOINT, precomputed Straus |
| R6 | `Valid_AF` / toPoint | `(x,y) ∈ E`; `⟦·⟧ = (x,y)` | `< 2^52` | to_affine, AffinePoint::{to_edwards, compress, ct_eq, eq, identity, Mul} |
| R7 | `LUT_n(t, P)` for `T ∈ {PN, AN}`, `n ∈ {8,16,32,64,128}` | `∀ j < n, Valid_T(t.0[j]) ∧ ⟦t.0[j]⟧ = (j+1)•P` | via R4/R5 | LookupTable* select/From/Default, variable_base, Straus, basepoint tables |
| R8 | `NAF_m(t, A)` for `m ∈ {5 (8 entries), 8 (64 entries)}` | `∀ k, Valid_T(t.0[k]) ∧ ⟦t.0[k]⟧ = (2k+1)•A` | via R4/R5 | NafLookupTable5/8 select/From, vartime double/triple, Straus vartime, precomputed Straus, two AFFINE_ODD constants |
| R9 | `Table_w(t, P)` (basepoint table, radix `2^w`) | `∀ i < 32, LUT_{2^(w−1)}(t.0[i], 2^(2wi) • P)` | via R5 | create/basepoint/mul_base/Mul/From-conversions (5 types), ED25519_BASEPOINT_TABLE |
| R10 | `Represents(pre, ps)` for `VartimePrecomputedStraus` (serial), the backend enum, and `VartimeEdwardsPrecomputation` | `pre.static_lookup_tables.length = ps.length ∧ ∀ i, NAF_8⟨AN⟩(tables[i], ps[i])` | via R5 | new/len/is_empty/optional_mixed (3 layers) |
| R11 | Iterator `Yields` (exists in `Defs/Iterator.lean`) + Borrow behaviour hypothesis (as in `Scalar` `sum_spec`) | – | – | Sum, multiscalar_mul, optional_multiscalar_mul, Straus×2, Pippenger, precomputed new/optional_mixed (+ dispatchers) |
| R12 | `Scalar.asNat`, `HalfWidthScalar.asNat`, `Array.asNat 8` (exist) | unreduced integer value | `s.asNat < 2^255` where digits are computed | all scalar muls, clamped, constants |
| R13 | `MontgomeryPoint` bytes: `r.0.asNat 8` (canonical `< p`) | – | – | to_montgomery(_batch) |

#### Q. Open questions / subtle points

1. **Validity vs `is_valid`.** `ValidityCheck::is_valid` (EdwardsPoint, ProjectivePoint) never
   checks `Z ≠ 0`, so it is *weaker* than `Valid_EP`/`Valid_PP` (the all-zero struct passes).
   Its spec must be the equation-level biconditional, with an `OnCurve` corollary under `Z ≠ 0`.
   Do not name the representation predicate `IsValid` if that invites confusion with the Rust
   `is_valid` (maybe `OnCurve` for the algebraic part, plus bounds).
2. **Limb bounds per struct are forced by the code.** Field `add` does not reduce (limbs add),
   `mul`/`square`/`sub`/`neg` need `< 2^54` and give `< 2^52`, `square2` gives `< 2^53`. Tracing:
   - `EdwardsPoint + AffineNiels` computes `Z2 = Z+Z` then `Z2 + Txy2d` and feeds it to a `mul`:
     with `Z < 2^53` (the old project's `EdwardsPoint.IsValid` bound) this reaches
     `2^54 + 2^52 > 2^54`. So **EdwardsPoint needs `Z < 2^52`**; every producer gives `< 2^52`
     (`as_extended` = muls, `decompress` X from negate/sqrt `< 2^52`, Y from `from_bytes` `< 2^51`,
     `Z = ONE`, `neg` `< 2^52`, constants `< 2^51`), so the uniform invariant is **all four limbs
     `< 2^52`**. `X, Y` need `< 2^53` (they are added before a mul/square), `T` `< 2^54`.
   - ProjectivePoint `< 2^52` (double adds `X+Y` before squaring: needs `< 2^53`).
   - CompletedPoint `< 2^54` (its `Y = PP+MM < 2^53`, `Z = ZZ2+TT2d < 2^53+2^52`).
   - ProjectiveNiels / AffineNiels `< 2^54` (only multiplied; `Y+X` up to `2^53`; the
     precomputed table constants have limbs up to ≈ `2^51.7`, i.e. **not** `< 2^51`).
   - AffinePoint `< 2^52` (its coordinates become EdwardsPoint `X, Y` in `to_edwards`).
   Decide whether bounds live inside `Valid_*` (old project) or as separate conjuncts (current
   field-spec style).
3. **`toPoint` totality.** With `Z = 0`, `X/Z` is `0` in Lean, giving `(0,0) ∉ E`; a total
   `toPoint : EdwardsPoint → E` needs a junk value (old project: default to `0`), or `toPoint`
   takes the validity proof (old `toPoint'`). No quotient is needed: the affine point is a
   canonical representative, and all equality-type items (`ct_eq`, `eq`, `is_identity`) are stated
   via `⟦·⟧`.
4. **Equality relations are struct-specific.** `EdwardsPoint::ct_eq` = projective
   `X₁Z₂ = X₂Z₁ ∧ Y₁Z₂ = Y₂Z₁` (ignores T; all `Z = 0` values equal); `AffinePoint::ct_eq` =
   coordinate-wise mod p; `AffineNielsPoint` derived `eq` = coordinate-wise mod p;
   `CompressedEdwardsY::ct_eq/eq` = **byte** equality (distinct encodings of one point are
   unequal). Only the first three coincide with point equality (under validity).
5. **Decompression edge cases.** (a) `y ∈ [p, 2^255)`: accepted, reduced mod p (`from_bytes`
   keeps `asNat = n % 2^255`). (b) `x = 0` (i.e. `y = ±1`) with sign bit 1: accepted, returns
   `x = 0`. Both differ from RFC 8032's strict decoder. Hence `compress ∘ decompress ≠ id` on
   such inputs, while `decompress ∘ compress = id` on valid points. The old project's
   `decompress_edwards_pure` rejects `y ≥ p`, i.e. models RFC 8032, not dalek (its `decompress_spec`
   does not use it). The old spec's characterisation is complete but redundant (`toField` and
   `Nat [MOD p]` forms of the same facts, `y² ≠ 1 →` parity).
6. **Scalars are unreduced integers.** All scalar-mul specs must use `s.asNat • P`, not
   `(s.asNat % L) • P` (equal only on torsion-free points); `is_torsion_free` relies on it
   (`BASEPOINT_ORDER.asNat = L`). Precondition is `s.asNat < 2^255` (for `as_radix_16`,
   `as_radix_2w`, `non_adjacent_form`), **not** canonicity; the old project named it
   `h_scalar_canonical`, which is misleading. `vartime_triple_scalar_mul_basepoint` needs no bound
   on `b` (split into 128-bit halves).
7. **Iterator-based items** need `Yields` + Borrow hypotheses; patched behaviour: equal lengths
   are an `massert` precondition in the `EdwardsPoint` wrappers; Straus/Pippenger themselves
   truncate to the shorter input; Straus-vartime reads *all* points (`None` anywhere ⇒ `None`),
   Pippenger only the zipped prefix; precomputed: `|static scalars| ≤ |static points|` and
   `|dynamic scalars| = |dynamic points|` asserted only after the `None` check.
8. **NAF spec strength for `vartime_triple_base`.** The loop starts at `HEEA_MAX_INDEX = 129`,
   ignoring higher NAF digits; correctness needs "`x < 2^128` ⇒ NAF digits above index 128 are
   0". The current `non_adjacent_form_spec` (value, odd digits, `|d| < 2^(w−1)`,
   non-adjacency) implies it, but only via a nontrivial lemma; consider adding the conjunct to
   the `HalfWidthScalar` NAF spec (frozen statement: sign-off) or proving it in Helpers.
9. **`LookupTable::select` is generic in Lean.** Either a generic structural spec conditional on
   instance specs (identity, `conditional_assign`, `Neg`) plus concrete corollaries, or two
   concrete specs (PN and AN) × five radixes. `select(x)` with `x < 0` returns the *Niels
   negation* of the entry (swap + negate `T2d`/`xy2d`); `x = 0` returns the identity encoding
   `(1,1,1,0)` / `(1,1,0)` (and `−0` limbs after `conditional_negate`, value 0).
10. **Constants and `native_decide`.** The old project proved `L • B = 0`, `4•B ≠ 0`, torsion
    facts with `native_decide` (banned here). The item specs listed only need explicit-coordinate
    checks (`decide` on `ZMod p`/`Nat` with the kernel's GMP), table entries `(j+1)·256^i • B`
    (1024 points for the radix-16 table, 64 for NAF8 — expensive to check by kernel evaluation;
    a computable smul + `decide` per entry, or a generic lemma relating the table to its
    `create`), and `8•T₈ = 0` (3 doublings). Decide how much of this to prove and how.
11. **Group-law source.** No Edwards curves in Mathlib; options: port the old project's
    hand-proved `AddCommGroup` (associativity proof is long), or transfer Mathlib's Weierstrass
    `Point` group through the birational map (also gives M12 for free). Statement-wise only
    `AddCommGroup (E)` is needed.
12. **Old-project comparison.** Good: `EdwardsPoint.OnCurve` (`Z ≠ 0`, `XY = TZ`, homogeneous
    eq.), group-level specs for add/mul/mul_by_pow_2/is_small_order/is_torsion_free/mul_base,
    `EIGHT_TORSION_spec` shape (`[i] = i•P`, `8•P = 0`, `4•P ≠ 0`), `ct_eq` giving both the
    coordinate relation and the point form, generic `is_identity_spec`. Awkward or missing:
    `mul_clamped_spec` only says `∃ clamped_scalar` with properties (should give the exact value
    `clamp(bytes)` — `clamp_integer_spec` exists now); `to_montgomery_spec` stated via an `if` on
    Nat congruences instead of `u = (1+y)/(1−y)`; curve_models specs at coordinate level only, no
    output bounds for `CompletedPoint`; limb bound 2^53 for EdwardsPoint (insufficient for the
    affine-Niels path, Q2); `Field51_as_Nat … ≡ … [MOD p]` style (here: `%`); missing entirely:
    `is_valid` (both), `compress_batch(_alloc)`, `to_montgomery_batch`, `Sum`, `multiscalar_mul`,
    `optional_multiscalar_mul`, Pippenger, precomputed Straus, the five basepoint-table types
    (`create`/`basepoint`/`mul_base`/`From`), `LookupTable<AffineNiels>` and the radix-32…256
    tables, `NafLookupTable5/8`, `vartime_triple_scalar_mul_basepoint`, AffineNiels `eq`,
    `ED25519_BASEPOINT_TABLE`, `AFFINE_ODD_MULTIPLES_*`, `ED25519_BASEPOINT_128_POINT`,
    `ED25519_BASEPOINT_COMPRESSED`. Its `ED25519_BASEPOINT_POINT_spec` mixes in Ristretto-ish
    facts (`Z² − Y² = c²`); the order facts belong in a math lemma, not the constant's spec.

---

## Appendix B: Montgomery and Ristretto, item by item

(Raw analysis; the numbering M1–M14 / R1–R10 here is this appendix's own, consolidated in §2.)

Scope: `src/montgomery.rs`, `src/ristretto.rs`, `src/ristretto/elligator.rs`, the Montgomery/Ristretto
constants in `src/constants.rs`, and `EdwardsPoint::{to_montgomery, to_montgomery_batch}`.
Read-only analysis of the Rust sources, `Funs.lean`, `translation.json` and the translation patches,
compared with the old project (`~/Projects/curve25519-dalek-lean-verify`) and FFEC
(`/mnt/projects/Maths/FEC`).

#### 0. Conventions used below

- `T` = `«x86_64-tables»`. Every target-dependent item also exists as `«x86_64-no-tables»`,
  `«i686-tables»`, `«i686-no-tables»` (the 32-bit ones are out of reach until the u32 field layer is
  verified). Items whose signature contains no target-dependent type also have a **façade** without
  suffix that dispatches on `get_target`. These are listed as "(façade)".
- Types: `montgomery.MontgomeryPoint := Array U8 32#usize`, `ristretto.CompressedRistretto :=
  Array U8 32#usize`, `ristretto.RistrettoPoint.T := edwards.EdwardsPoint.T` (the Rust newtype is
  **erased**: a `def` alias, so any Ristretto invariant has to be a separate predicate),
  `montgomery.ProjectivePoint.T` = structure `{U W : FieldElement51}`.
- Field notation: `⟦x⟧ : ZMod p` = `(x.asNat : ZMod p)` for `x : FieldElement51`.
  `bytesU m := ((m.asNat % 2^255 : ℕ) : ZMod p)` (what `FieldElement::from_bytes` computes: top bit
  masked, then reduced mod p). `enc r` = "`r.asNat < p ∧ (r.asNat : ZMod p) = …`" (what `to_bytes`
  produces: canonical, top bit 0). `0⁻¹ = 0` in `ZMod p`, which matches dalek's `invert`.
- `isNeg z :↔ z.val % 2 = 1` for `z : ZMod p` (RFC 8032/9496 sign; `is_negative` already has spec
  `c.val = self.asNat % p % 2`). `|z|` = CT_ABS: `if isNeg z then -z else z`.
- `f(u) := u³ + A u² + u`, `E_M : v² = f(u)` (Curve25519), `E_M' : 2 v² = f(u)` (its quadratic twist;
  `2` is a non-square mod p), `E` = Ed25519 `-x² + y² = 1 + d x² y²`.
- `u₀ : E_M(F_p) → F_p`, `u₀(∞) = 0`, `u₀(u,v) = u` (dalek/Costello–Smith convention; same on `E_M'`).
- Items not translated (feature-gated or excluded): `montgomery::elligator_encode` (digest, absent
  from `Funs.lean`), `Hash` impls (Charon `exclude`), `RistrettoPoint::{random, try_random}`
  (rand_core), `{from_hash, hash_from_bytes}` (digest), `group::*` impls (`GroupEncoding::from_bytes`
  etc.), serde, `Debug`. Closure wrappers `P.Insts.…call_once` and the tuple-struct
  `…constructor` functions are not specified (guideline: closure wrappers are not covered).

#### 1. `src/montgomery.rs`

Public API: `MontgomeryPoint` and its impls. Private: `ProjectivePoint`, `differential_add_and_double`
(they still get proved specs in their proof files; ideally **purely algebraic** ones, see 1.2).

##### 1.1 Public items

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `ConstantTimeEq::ct_eq` | `montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq.ct_eq` (façade) → `montgomery.ConstantTimeEqMontgomeryPoint.ct_eq.T` | `c.IsValid ∧ (c.val = 1 ↔ bytesU self = bytesU other)`, i.e. `self.asNat % 2^255 % p = other.asNat % 2^255 % p` ("equality mod p", bit 255 ignored; `x` and `x+p` are equal). | none | R: `bytesU` (only ℕ arithmetic needed, no curve) |
| `PartialEq::eq` | `montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint.eq` | `r = true ↔ bytesU self = bytesU other` | none | R: `bytesU` |
| `ConditionallySelectable::conditional_select` | `montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_select` | `r = if choice.val = 1 then b else a` (bytewise) | `choice.IsValid` | none |
| `Identity::identity` | `montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity.identity` | `r = [0;32]` (so `bytesU r = 0 = u₀(∞)`). The Rust doc "identity, which has order 4" is meaningless for an x-only value; do not reflect it. | none | (M: `u₀(∞) = 0` only to explain) |
| `Default::default` (derived) | `montgomery.MontgomeryPoint.Insts.CoreDefaultDefault.default` | `r = [0;32]` | none | none |
| `Zeroize::zeroize` | `montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize` | `r = [0;32]` | none | none |
| `mul_base(&Scalar)` | `montgomery.MontgomeryPoint.mul_base` (façade) → `.mul_base.T` | `enc r (xMul s.asNat 9)`. Equivalent form: `enc r (u₀(φ(s.asNat • B)))`, `B` the Ed25519 basepoint. Note: `s` need not be reduced mod ℓ; the result depends on `s.asNat`, not `s mod ℓ` (B has prime order so in fact only `s mod ℓ` matters, but the statement need not say so). | `s.asNat < 2^255` (inherited from `EdwardsPoint::mul_base`, radix-16 `debug_assert`, which Aeneas turns into `massert`) | M: `xMul`, Ed25519 group, basepoint `B`, birational `φ`, `u₀(φ(B)) = 9`. R: `Scalar.asNat`, `enc` |
| `mul_clamped(self, [u8;32])` | `montgomery.MontgomeryPoint.mul_clamped` (façade) | `enc r (xMul (clamp bytes).asNat (bytesU self))` = **RFC 7748 `X25519(bytes, self)`** exactly (RFC: decodeScalar25519 = clamp, decodeUCoordinate masks bit 255 and accepts non-canonical u, ladder over bits 254..0, encode canonical). `clamp k ∈ [2^254, 2^255)`, `8 ∣ clamp k`. | none | M: `xMul` (curve **and twist**), `clamp` (exists in scalar layer: `clamp_integer` spec). R: `bytesU`, `enc` |
| `mul_base_clamped([u8;32])` | `montgomery.MontgomeryPoint.mul_base_clamped` (façade) | `enc r (xMul (clamp bytes).asNat 9)` = RFC 7748 `X25519(bytes, 9)`. | none (clamped value `< 2^255` meets `mul_base`'s precondition) | as `mul_base` + `clamp` |
| `mul_bits_be(&self, bits)` | `montgomery.MontgomeryPoint.mul_bits_be` (façade, generic over `Iterator T0 Bool` instance) → `.mul_bits_be.T` (+ `_loop`, `_loop.body`) | Given `iterInst.Yields bits bs` (exists: `Defs/Iterator.lean`): `enc r (xMul (Nat.ofDigits 2 bs.reverse) (bytesU self))`, i.e. `n = Σ bs[i]·2^(len-1-i)` (big-endian). Any length; `bs = []` gives `n = 0`, `r = [0;32]`. | `iterInst.Yields bits bs` (without it the loop may diverge or the iterator's `next` may fail) | M: `xMul`. R: `bytesU`, `enc`, `Yields`, big-endian bit list → ℕ |
| `as_bytes` | `montgomery.MontgomeryPoint.as_bytes` | `r = self` | none | none |
| `to_bytes` | `montgomery.MontgomeryPoint.to_bytes` | `r = self` | none | none |
| `to_edwards(&self, sign: u8)` | `montgomery.MontgomeryPoint.to_edwards.T` (no façade: returns `EdwardsPoint.T`) | Let `u = bytesU self`. (i) `r = none ↔ ¬ IsSquare (f u)` (u is on the twist and not on the curve). The explicit `u = −1` early return is subsumed: `f(−1) = A − 2` is a non-square, and the check is **needed**, not an optimisation: without it `(u+1)⁻¹ = 0`, `y = 0`, and decompression would return `(±√−1, 0)`, whose actual `u` is `1`. (ii) `r = some P →` `P.IsValid` (Edwards repr invariant) `∧ y(P) = (u−1)(u+1)⁻¹` (equivalently `u₀(φ(P)) = u`) `∧ (x(P) = 0 ∨ x(P).val % 2 = sign.val % 2)`. `x(P) = 0 ↔ u = 0` (then `P = (0,−1)`, sign ignored). Only `sign % 2` matters: `sign << 7` wraps in `u8` (sign = 2 behaves as 0). Doc says sign ∈ {0,1}; do not add that as a precondition, state `% 2`. | none (`decompress` itself has no precondition on bytes) | M: `f`, `IsSquare`, Ed25519 curve/point, `φ` (or the y-formula), `isNeg`. R: `bytesU`, `EdwardsPoint → E` + validity. Key lemma: `(y²−1)/(dy²+1) = −(A+2)·u/(u²+Au+1)` with `y = (u−1)/(u+1)`, and `−(A+2)` is a square, `u²+Au+1 ≠ 0` |
| `Mul<&Scalar> for &MontgomeryPoint` | `Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul` (façade) → `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul.T` (+ `_loop`; patched to loop over bit indices 254..0, see `montgomery-MontgomeryPoint-mul.patch`) | `enc r (xMul (scalar.asNat % 2^255) (bytesU self))`. Bit 255 is skipped by the code (not by a precondition), so state it with `% 2^255`. | none (the old project's `hP_bound : asNat P < 2^255` is unnecessary: `from_bytes` masks) | M: `xMul`. R: `bytesU`, `enc`, `Scalar.asNat` |
| by-value variants `MontgomeryPoint * &Scalar`, `&MP * Scalar`, `MP * Scalar` | `montgomery.MontgomeryPoint.Insts.CoreOpsArithMulSharedBScalarMontgomeryPoint.mul`, `SharedAMontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint.mul`, `montgomery.MontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint.mul` | same | none | same |
| `Mul<&MontgomeryPoint> for &Scalar` + variants | `Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint.mul`, `scalar.Scalar.Insts.CoreOpsArithMulSharedBMontgomeryPointMontgomeryPoint.mul`, `SharedAScalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint.mul`, `scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint.mul` | same | none | same |
| `MulAssign<&Scalar>`, `MulAssign<Scalar>` | `montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar.mul_assign`, `….CoreOpsArithMulAssignScalar.mul_assign` | new `self` = as `mul` | none | same |

##### 1.2 Private items (proof-file specs only)

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `ProjectivePoint::identity` / `default` | `montgomery.ProjectivePoint.T.Insts.Curve25519_dalekTraitsIdentity.identity`, `….CoreDefaultDefault.default` | `⟦U⟧ = 1 ∧ ⟦W⟧ = 0` (the point `∞ = (1:0)` of P¹) + limb bounds | none | none (R: `(U:W)`) |
| `ProjectivePoint::conditional_select` | `montgomery.ProjectivePoint.T.Insts.SubtleConditionallySelectable.conditional_select` | componentwise select | `choice.IsValid` | none |
| `ProjectivePoint::as_affine` | `montgomery.«ProjectivePointx86_64-tables».as_affine` | `enc r (⟦U⟧ * ⟦W⟧⁻¹)`; `W = 0` gives `0`, including the degenerate `(0:0)`. | limbs `< 2^54` | R: `(U:W) ↦ U·W⁻¹` |
| `differential_add_and_double(P, Q, u_D)` | `montgomery.differential_add_and_double.T` | **Algebraic** (recommended): with `U_P,W_P,U_Q,W_Q,u_D` the `⟦·⟧` values, `U_P' = (U_P²−W_P²)²`, `W_P' = 4U_PW_P(U_P² + A U_P W_P + W_P²)`, `U_Q' = 4(U_PU_Q − W_PW_Q)²`, `W_Q' = 4u_D(U_PW_Q − W_PU_Q)²`; output limbs `< 2^52`. The geometric meaning (xDBL / xADD on the Kummer line, valid when `u_D ∉ {0,∞}`) then lives in `Helpers`, where the ladder proof uses it. | limbs `< 2^54` | none in the statement; in the proof: `uADD`/`uDBL` on `E_M` and `E_M'` |
| `mul_bits_be` / `mul` loops | `…_loop`, `….body` | ladder invariant: after reading prefix with value `k`, `(x0, x1) ≡ (x([k]Q), x([k+1]Q))` in P¹ (projectively), swapped iff `prev_bit` | as above | M: `xMul`-style lifts, P¹ equality `U·W' = U'·W`. Degenerate case: if `u = 0` the xADD step produces `(0:0)`; final output is still `0 = xMul n 0`. Handle `u = 0` separately in the proof. |

##### 1.3 Edge cases visible in the code

- `u = 0` input (bytes `0`, `p`, `2^255`, `2^255 + p`, …): `x1 = (0:1)`; xADD with `u_D = 0` yields
  `(0:0)`; `as_affine` gives `0`. Matches `xMul n 0 = 0` for all `n` (`[n](0,0) ∈ {∞,(0,0)}`).
- `[n]Q = ∞`: `W = 0` → `0`. So `0` represents both ∞ and `(0,0)` (u₀ convention); no spec can
  distinguish them (the old project's `mkPoint`-based spec breaks exactly here, see §6).
- Twist inputs (`¬IsSquare (f u)`): the ladder computes `u₀([n]Q')` with `Q' ∈ E_M'(F_p)`; results stay
  on the twist (or are 0). `to_edwards` rejects them.
- Non-canonical `u` (`≥ p`, or bit 255 set): accepted, reduced (RFC 7748 behaviour). Output always
  canonical (`< p`).
- Scalar bit 255: ignored by `Mul` (bits 254..0); `mul_bits_be` uses exactly the given bits.
- `X25519_LOW_ORDER_POINTS` u-values (see §3): with any clamped scalar the output is `[0;32]`.

#### 2. `edwards.rs` items that cross to Montgomery

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `EdwardsPoint::to_montgomery` | `edwards.«EdwardsPointx86_64-tables».to_montgomery` | `enc r (montU P)` with `montU P := (Z+Y)(Z−Y)⁻¹ = (1+y)(1−y)⁻¹` (y = Y/Z), which is `u₀(φ(P))`: identity `(0,1) ↦ 0` (Rust doc: "sent to the 2-torsion point (0,0)" — as a u-value it is 0, same as ∞), `(0,−1) ↦ 0`, `P` and `−P` give the same value. | `P.IsValid` (Edwards repr: on curve, `Z ≠ 0`, `XY = ZT`, limbs `< 2^54`) | M: Ed25519 point, `φ` (or just the y-formula), `u₀`. R: `EdwardsPoint → E`, `enc` |
| `EdwardsPoint::to_montgomery_batch(&[Self])` | `edwards.«EdwardsPointx86_64-tables».to_montgomery_batch` (+ `_loop0/1`, patched to index loops) | `r.length = eds.length ∧ ∀ i < eds.length, enc r[i] (montU eds[i])` (batch inversion skips zeros, so the identity case matches `to_montgomery`) | `∀ i, eds[i].IsValid` | as above + R: `Vec`/`Slice` length/index |

#### 3. `src/constants.rs` (Montgomery / Ristretto constants)

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `X25519_BASEPOINT` | `constants.X25519_BASEPOINT` | `r.asNat = 9` (the bytes). Meaning (optional theorem, not spec): `9 = u₀(φ(B))`, `IsSquare (f 9)`. | — | R: `Array.asNat`. M (optional): `φ`, `B` |
| `X25519_LOW_ORDER_POINTS` | `constants.X25519_LOW_ORDER_POINTS` | Bytes as given. The decoded set is `{0, 1, −1, u₈, u₈'}` (entries `p`, `p+1` are non-canonical encodings of `0`, `1`; `p−1 = −1`). The Rust comments on orders ("1 (order 1)", "p−1 (order 2)", "0 (order 4)") do not match the math: `u=0` is `(0,0)` (order 2), `u=1` (on the curve, `f(1)=A+2` square) and `u=−1` (on the twist, `f(−1)=A−2` non-square) both have order 4, `u₈, u₈'` order 8. The meaningful statement is a theorem about `mul_clamped`: `∀ i bytes, mul_clamped LOW[i] bytes = [0;32]` (because every entry has order dividing 8 on `E_M` or `E_M'` and clamped scalars are multiples of 8). Optionally `∀ i n, xMul (8*n) (bytesU LOW[i]) = 0`. | — | M: `xMul`, orders (`[8]Q = ∞`) on curve and twist |
| `RISTRETTO_BASEPOINT_COMPRESSED` | `constants.RISTRETTO_BASEPOINT_COMPRESSED` | bytes; theorem: `= ristrettoEncode B` and `decompress` of it ≈ `B` | — | Q: `ristrettoEncode/Decode`, `B` |
| `RISTRETTO_BASEPOINT_POINT` | `constants.RISTRETTO_BASEPOINT_POINT.T` | `= ED25519_BASEPOINT_POINT` (same Edwards repr); `RistrettoPoint.IsValid` (needs `B ∈ 2E`: `B = 2·(L+1)/2·B`, since `B` has odd order ℓ — needs `ℓ•B = 0`, which is the Edwards layer's basepoint-order fact) | — | Q: `IsEven`; Edwards `B`, `ℓ•B = 0` |
| `RISTRETTO_BASEPOINT_TABLE` | `constants.RISTRETTO_BASEPOINT_TABLE.T` (tables configs only; patch: separate copy of `ED25519_BASEPOINT_TABLE`) | the Edwards table predicate "valid table for `B`" | — | Edwards: basepoint-table validity notion |

(`BASEPOINT_ORDER` is `pub(crate)`; `EIGHT_TORSION` is a backend constant, used by `coset4`.)

#### 4. `src/ristretto.rs` and `src/ristretto/elligator.rs`

Representation invariant (needed as precondition of every RistrettoPoint input and postcondition of
every output): `RistrettoPoint.IsValid P :↔ P.IsValid (Edwards) ∧ IsEven P.toPoint` where
`IsEven Q :↔ Q ∈ 2E` (`∃ R, Q = 2•R`). This holds for every value the public API can produce
(field is `pub(crate)`), and `compress` is wrong without it.

Ristretto equality: `P ≈ Q :↔ P.toPoint − Q.toPoint ∈ E[4]`, `E[4] = {(0,1),(0,−1),(√−1,0),(−√−1,0)}`.
The group is `2E/E[4]` (order ℓ; not needed by any statement).

##### 4.1 CompressedRistretto

| Item | Lean name | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `ct_eq` | `ristretto.CompressedRistretto.Insts.SubtleConstantTimeEq.ct_eq` | `c.IsValid ∧ (c.val = 1 ↔ self = other)` (bytewise) | none | none |
| `eq` | `ristretto.CompressedRistretto.Insts.CoreCmpPartialEqCompressedRistretto.eq` | `r = true ↔ self = other`. (Meaning, as a theorem: on valid encodings this is Ristretto equality, since encodings are canonical.) | none | none |
| `to_bytes`, `as_bytes` | `ristretto.CompressedRistretto.to_bytes`, `.as_bytes` | `r = self` | none | none |
| `from_slice(&[u8])` | `ristretto.CompressedRistretto.from_slice` | `(bytes.length = 32 → ∃ c, r = .Ok c ∧ c.val = bytes.val) ∧ (bytes.length ≠ 32 → r = .Err _)` (the old project's statement shape is fine) | none | R: `Slice` length |
| `TryFrom<&[u8]>::try_from` | `ristretto.CompressedRistretto.Insts.CoreConvertTryFromShared0SliceU8TryFromSliceError.try_from` | same as `from_slice` | none | same |
| `identity`, `default` | `ristretto.CompressedRistretto.Insts.Curve25519_dalekTraitsIdentity.identity`, `….CoreDefaultDefault.default` | `r = [0;32]` (theorem: `= ristrettoEncode 0`) | none | none |
| `zeroize` | `ristretto.CompressedRistretto.Insts.ZeroizeZeroize.zeroize` | `r = [0;32]` | none | none |
| `decompress` | `ristretto.CompressedRistretto.decompress.T` | RFC 9496 §4.3.1. Let `s = self.asNat`. `r = none ↔ ¬ (s < p ∧ s % 2 = 0 ∧ (ristrettoDecode (s : ZMod p)).isSome)`, and `r = some P → P.IsValid ∧ IsEven P.toPoint ∧ P.toPoint = (ristrettoDecode s).get` (exact Edwards point: `Z = 1`, `x = |2s·Dx|` etc.). Canonicity: `s < p` on the **full** 256-bit value (bit 255 set ⇒ rejected, because `to_bytes` of `from_bytes` clears it); non-negativity `s` even; then fails iff `v·u2² ` is zero or non-square, `isNeg t`, or `y = 0`. Better meaning (theorems or extra conjuncts): `r = some P ↔ ∃ Q ∈ 2E, self = ristrettoEncode Q` and then `P ≈ Q`. | none | Q: `ristrettoDecode` (RFC formulas: `isNeg`, CT_ABS, `SQRT_RATIO_M1`/`invsqrt` with non-negative root, constant `d`), `IsEven`, `≈`. R: bytes → `s` |
| `decompress::step_1` (private) | `ristretto.decompress.step_1.T` | `(c₁.val = 1 ↔ repr.asNat < p) ∧ (c₂.val = 1 ↔ (repr.asNat % 2^255 % p) % 2 = 1) ∧ ⟦s⟧ = bytesU repr` + bounds | none | R only |
| `decompress::step_2` (private) | `ristretto.decompress.step_2.T` | the RFC 9496 step-2 formulas on `⟦s⟧` (as old `step_2_spec`, which is a good shape): `ok ↔ v·u2² ≠ 0 ∧ IsSquare(v·u2²)`, `c ↔ isNeg ⟦T⟧`, `c' ↔ ⟦Y⟧ = 0`, and when all pass the point equals `ristrettoDecode s` | limbs `< 2^54` | Q: `ristrettoDecode` |

##### 4.2 RistrettoPoint

| Item | Lean name (T) | Draft postcondition | Preconditions | Notions needed |
|---|---|---|---|---|
| `compress` | `ristretto.«RistrettoPointx86_64-tables».compress` | RFC 9496 §4.3.2. `r.asNat < p ∧ r.asNat % 2 = 0 ∧ (r.asNat : ZMod p) = ristrettoEncode P.toPoint`. The meaning (theorems about `ristrettoEncode` on `2E`, possibly also restated as conjuncts): **well defined on cosets** (`P ≈ Q → encode P = encode Q`, also independent of the projective representative), **injective on cosets** (`encode P = encode Q → P ≈ Q`), **round trip** (`ristrettoDecode (encode P) = some P'` with `P' ≈ P`). Alternative statement avoiding a formula-level `encode`: "`r` is canonical and `decompress r = some P'` with `P' ≈ P`" (uniqueness of such `r` is a math theorem). | `P.IsValid ∧ IsEven P.toPoint` (without evenness `invsqrt` gets a non-square and the output is garbage) | Q: `ristrettoEncode`/`Decode`, `IsEven`, `≈`, constants `√−1`, `1/√(a−d)` |
| `double_and_compress_batch(points)` | `ristretto.«RistrettoPointx86_64-tables».double_and_compress_batch` (+ `.states`, `.states_loop`, `_loop0/1`, `BatchCompressState.from`/`efgh`; patched) | Given `iterInst.Yields points ps`: `r.length = ps.length ∧ ∀ i, r[i] = compress (2•ps[i])`, i.e. `r[i].asNat = encode(2•ps[i].toPoint)` (the doc's `assert_eq!(P2_compressed, (P+P).compress())`). Edge cases: `efgh = 0` (when `X=0`, `Y=0` or `X²+Y²=0`; `f,h ≠ 0` by completeness): the zero-skipping batch inversion gives `s = 0`, which is correct since then `2P ∈ E[4]`. | `∀ P ∈ ps, P.IsValid` (Edwards validity is enough: `2P` is always even) | Q: `ristrettoEncode`, Edwards doubling. R: `Yields`, `Vec` |
| `BatchCompressState::from`, `efgh` (private) | `….double_and_compress_batch.BatchCompressState.Insts.«CoreConvertFromSharedARistrettoPointx86_64-tables».from`, `….BatchCompressState.efgh` | algebraic: `e = 2XY, f = Z²+dT², g = Y²+X², h = Z²−dT², eg, fh`; `efgh = eg·fh` | limbs | none |
| `coset4` (private) | `ristretto.«RistrettoPointx86_64-tables».coset4` | `r = [P, P+T₂, P+T₄, P+T₆]` (EIGHT_TORSION entries) and `{r[i].toPoint} = P.toPoint + E[4]` | `P.IsValid` | Q: `E[4]`; Edwards add, `EIGHT_TORSION` |
| `from_uniform_bytes(&[u8;64])` | `ristretto.«RistrettoPointx86_64-tables».from_uniform_bytes` | RFC 9496 §4.3.4 one-way map: `r.toPoint = ristrettoMap (bytesU b[0..32]) + ristrettoMap (bytesU b[32..64])` (each half: low 255 bits mod p) `∧ RistrettoPoint.IsValid r` | none | Q: `ristrettoMap`, `IsEven`. R: `bytesU` on sub-arrays |
| `elligator_ristretto_flavor(&FieldElement)` (pub(crate)) | `ristretto.elligator.«RistrettoPointx86_64-tables».elligator_ristretto_flavor` | `r.toPoint = ristrettoMap ⟦r_0⟧ ∧ RistrettoPoint.IsValid r` | limbs `< 2^54` | Q: `ristrettoMap` (RFC MAP formulas, `SQRT_RATIO_M1` both branches, constants `1−d²`, `(d−1)²`, `√(ad−1)`, `√−1`), on-curve and `w1·w3 ≠ 0` (so `Z ≠ 0` after `as_extended`), image ⊆ `2E` |
| `map_to_curve([u8;32])` (pub) | `ristretto.elligator.«RistrettoPointx86_64-tables».map_to_curve` | `r.toPoint = ristrettoMap (bytesU bytes) ∧ RistrettoPoint.IsValid r` (RFC MAP; bit 255 cleared by `from_bytes`) | none | as above |
| `identity`, `default` | `ristretto.RistrettoPoint.T.Insts.Curve25519_dalekTraitsIdentity.identity`, `….CoreDefaultDefault.default` | `r.toPoint = 0` (`(0:1:1:0)`), valid, even | none | Edwards identity |
| `eq` | `ristretto.RistrettoPoint.T.Insts.«CoreCmpPartialEqRistrettoPointx86_64-tables».eq` | `r = true ↔ self ≈ other` | both Edwards-valid | Q: `≈`, `E[4]` |
| `ct_eq` | `ristretto.RistrettoPoint.T.Insts.SubtleConstantTimeEq.ct_eq` | `c.IsValid ∧ (c.val = 1 ↔ self.toPoint − other.toPoint ∈ E[4])`. Derivation: `X1Y2 = Y1X2 ⇔ (x2:y2) = (x1:y1) ⇔ P2 ∈ {P1, P1+(0,−1)}` and `X1X2 = Y1Y2 ⇔ (x2:y2) = (y1:x1) ⇔ P2 ∈ {P1+(±√−1,0)}` (using: d non-square, −1 square, so `c = ±1` resp. `c = ±√−1` are the only scalings staying on the curve). Holds for **all** valid Edwards points; evenness is not needed for this statement (it is what makes `≈` the equality of the prime-order group). | both Edwards-valid (`Z ≠ 0`) | Q: `E[4]` (explicit 4 points suffice), Edwards subtraction (or the explicit coset `{P, (−x,−y), (iy,ix), (−iy,−ix)}` to avoid needing the group law in the statement) |
| `conditional_select` | `ristretto.RistrettoPoint.T.Insts.SubtleConditionallySelectable.conditional_select` | `r = if choice.val = 1 then b else a` | `choice.IsValid` | none |
| `zeroize` | `ristretto.RistrettoPoint.T.Insts.ZeroizeZeroize.zeroize` | `r` = Edwards identity (X=0,Y=1,Z=1,T=0 — per Edwards zeroize), valid and even | none | Edwards |
| `Add` (4 forms: `&+&`, `&+v`, `v+&`, `v+v`) | `ristretto.RistrettoPoint.T.Insts.«CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».add`, `«Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithAddSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables».add`, `ristretto.RistrettoPoint.T.Insts.«CoreOpsArithAddSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».add`, `«SharedARistrettoPointx86_64-tables».Insts.«CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».add` | `r.toPoint = self.toPoint + other.toPoint` (exact Edwards equality; stronger than `≈`) `∧ RistrettoPoint.IsValid r` | both `RistrettoPoint.IsValid` | Edwards add; `2E` closed under `+` (trivial with `IsEven := ∃R, Q = 2R`) |
| `AddAssign` (2) | `….Insts.«CoreOpsArithAddAssignRistrettoPointx86_64-tables».add_assign`, `….«CoreOpsArithAddAssignShared0RistrettoPointx86_64-tables».add_assign` | as `add` | same | same |
| `Sub` (4), `SubAssign` (2) | `…CoreOpsArithSub…sub`, `…SubAssign…sub_assign` (names parallel to Add) | `r.toPoint = self.toPoint − other.toPoint ∧ valid` | same | Edwards sub |
| `Neg` (2) | `ristretto.RistrettoPoint.T.Insts.«CoreOpsArithNegRistrettoPointx86_64-tables».neg`, `«Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithNegRistrettoPointx86_64-tables».neg` | `r.toPoint = −self.toPoint ∧ valid` | `valid` | Edwards neg |
| `Mul` point·scalar and scalar·point (8 forms) + `MulAssign` (2) | `ristretto.RistrettoPoint.T.Insts.«CoreOpsArithMulScalarRistrettoPointx86_64-tables».mul`, `….«CoreOpsArithMulSharedBScalar…».mul`, `«Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalar…».mul`, `«SharedARistrettoPointx86_64-tables».Insts.«CoreOpsArithMulScalar…».mul`, `scalar.Scalar.Insts.«CoreOpsArithMulRistrettoPoint…».mul`, `scalar.Scalar.Insts.«CoreOpsArithMulSharedBRistrettoPoint…».mul`, `Shared0Scalar.Insts.«CoreOpsArithMulSharedARistrettoPoint…».mul`, `SharedAScalar.Insts.«CoreOpsArithMulRistrettoPoint…».mul`, `….CoreOpsArithMulAssignScalar.mul_assign`, `….CoreOpsArithMulAssignSharedAScalar.mul_assign` | `r.toPoint = s.asNat • P.toPoint ∧ valid` (not `s mod ℓ`: `P` may carry E[4]-torsion; in the quotient it is the same) | `P` valid; `s.asNat < 2^255` (Edwards variable-base mul, radix-16 `debug_assert` → `massert`) | Edwards `•` |
| `mul_base(&Scalar)` | `ristretto.«RistrettoPointx86_64-tables».mul_base` | `r.toPoint = s.asNat • B ∧ valid` | `s.asNat < 2^255` | Edwards `B` |
| `Sum<T: Borrow<RistrettoPoint>>` | `ristretto.RistrettoPoint.T.Insts.CoreIterTraitsAccumSum.sum` (+ `sum_loop`; patched to `while let`) | given `iterInst.Yields iter xs` and `borrowInst` returns the point: `r.toPoint = (xs.map toPoint).sum ∧ valid` | `Yields`, all `xs` valid, borrow-behaviour hypothesis (as for Scalar `Sum`/`Product`) | Edwards `+`, R: `Yields` |
| `MultiscalarMul::multiscalar_mul` | `ristretto.RistrettoPoint.T.Insts.«Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-tables».multiscalar_mul` (+ `extended_points[_loop]`; patched) | `r.toPoint = Σ sᵢ.asNat • Pᵢ.toPoint ∧ valid` | `Yields` for both iterators, equal lengths (whatever the Edwards `multiscalar_mul` spec needs: its size-hint asserts), `sᵢ.asNat < 2^255`, all `Pᵢ` valid | Edwards multiscalar spec |
| `VartimeMultiscalarMul::optional_multiscalar_mul` | `ristretto.RistrettoPoint.T.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointx86_64-tables».optional_multiscalar_mul` | `r = none ↔ ∃ i, Pᵢ = none`; else `Σ sᵢ•Pᵢ` + valid (patch: all points read even after a `None`) | as above | same |
| `VartimeRistrettoPrecomputation::{new, len, is_empty, optional_mixed_multiscalar_mul}` | `ristretto.VartimeRistrettoPrecomputation.T.Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointx86_64-tables».{new,len,is_empty,optional_mixed_multiscalar_mul}` | `new`: precomputation valid for the list of static points (Edwards `VartimePrecomputedStraus` predicate); `len` = number of static points; `is_empty ↔ len = 0`; mixed: `none ↔ some dynamic point none`, else `Σ aᵢ•Sᵢ + Σ bⱼ•Dⱼ` | `Yields`, lengths, scalar bounds, validity | Edwards precomputed-Straus notions |
| `vartime_double_scalar_mul_basepoint(a, A, b)` | `ristretto.«RistrettoPointx86_64-tables».vartime_double_scalar_mul_basepoint` (tables configs only in `Funs.lean`) | `r.toPoint = a.asNat•A + b.asNat•B ∧ valid` | `A` valid, scalar bounds of the Edwards spec | Edwards |
| `RistrettoBasepointTable::{create, basepoint}`, `&Table * &Scalar`, `&Scalar * &Table` | `ristretto.«RistrettoBasepointTablex86_64-tables».create`, `.basepoint`, `«Shared0RistrettoBasepointTablex86_64-tables».Insts.«CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables».mul`, `Shared0Scalar.Insts.«CoreOpsArithMulSharedARistrettoBasepointTablex86_64-tablesRistrettoPointx86_64-tables».mul` (tables only) | `create`: table valid for `P`; `basepoint`: returns the table's point (valid, even if the input was); `mul`: `s.asNat • base` | `P` valid (+ even for the output to be valid); `s.asNat < 2^255` | Edwards table predicate |

#### 5. Consolidated notion lists

##### 5.1 MATH (curve level, dalek-independent; belongs in `Curve25519/**` or an FFEC import)

| # | Notion | Needed by |
|---|---|---|
| M1 | Montgomery curve `B v² = u³ + A u² + u` over `ZMod p` with its group (FFEC `MontgomeryModel` has general `B` and a group by Weierstrass transport) | everything Montgomery |
| M2 | Curve25519 `E_M` (`B = 1`) **and its quadratic twist `E_M'`** (`B = 2`, any non-square works) | `xMul` (all ladder items), `to_edwards` (characterising `none`), `X25519_LOW_ORDER_POINTS` |
| M3 | `u₀ : E.Point → F`, `∞ ↦ 0` (FFEC `xCoord`) | `xMul`, `to_montgomery`, `mul_base` |
| M4 | `xMul : ℕ → ZMod p → ZMod p`, `xMul n u := u₀([n]Q)` for any `Q ∈ E_M(F_p) ∪ E_M'(F_p)` with `u₀(Q) = u` (choose `E_M` iff `IsSquare (f u)`), with lemma: independent of the lift (`±v`, and `u = 0` lies on both). Then `x25519 k u := xMul (clamp k).asNat u` | `mul`(×8), `mul_assign`(×2), `mul_bits_be`, `mul_clamped`, `mul_base`, `mul_base_clamped`, LOW_ORDER theorem |
| M5 | Quadratic-character facts: `A²−4`, `A−2`, `d` non-squares; `A+2`, `−1`, `1+d`, `−(A+2)` squares; `u²+Au+1 ≠ 0` | proofs of `to_edwards`, `ct_eq`, ladder edge cases, Ristretto (FFEC has `A±2`, `A²−4`, `d`) |
| M6 | Ed25519 twisted Edwards curve and group (from the Edwards analysis; FFEC `TwistedEdwardsModel` with transported group) | `to_edwards`, `to_montgomery*`, `mul_base`, all Ristretto |
| M7 | Birational group iso `φ : E ≅ E_M`, `u₀(φ(x,y)) = (1+y)/(1−y)` (0 at y = 1). FFEC's `TwistedEdwardsModel.toMontgomery` lands in the model `B = 4/(a−d) = −486664 = −(A+2)`, **not** `B = 1`; compose with the iso `v ↦ √(−(A+2))·v` (exists since `−(A+2)` is a square). The u-coordinate is unaffected. | `to_montgomery*` (u-formula only), `mul_base` (hom property), `to_edwards`, `X25519_BASEPOINT` |
| M8 | Basepoints: Ed25519 `B`, `u₀(φ(B)) = 9`, `ℓ • B = 0` | `mul_base*`, Ristretto basepoint constants, `RISTRETTO_BASEPOINT_POINT` evenness |
| M9 | Sign / root conventions in `ZMod p`: `isNeg`, `|·|`, `SQRT_RATIO_M1(u,v)` (non-negative root; returns `√(i·u/v)` in the non-square branch), `invsqrt` | `to_edwards` (sign), Ristretto encode/decode/map |
| M10 | `E[4]` (the four points `(0,±1)`, `(±√−1, 0)`), relation `P ≈ Q :↔ P − Q ∈ E[4]` | Ristretto `ct_eq`, `eq`, `compress` (coset invariance), `decompress`, `coset4` |
| M11 | `2E` (doubling image, `IsEven`), closed under the group ops; **2-descent characterisation** `P ∈ 2E ↔ IsSquare (1 − y²)` (old project: `IsEven_iff_in_doubling_image_right` is `sorry`) | invariant of every RistrettoPoint item; proofs of decompress/elligator outputs (one direction) and of arithmetic closure (other direction, if `IsEven` is defined by squares) |
| M12 | Ristretto decode (RFC 9496 §4.3.1) `ZMod p → Option E`, encode (§4.3.2) `E → ZMod p`, with theorems: decode lands in `2E`; encode constant on `≈`-classes and on projective representatives; injective modulo `≈` on `2E`; `decode ∘ encode ≈ id` on `2E`; `encode ∘ decode = id` on valid `s` | `compress`, `decompress`, `step_1/2`, `double_and_compress_batch`, `RISTRETTO_BASEPOINT_COMPRESSED`, CompressedRistretto `eq` meaning |
| M13 | Ristretto Elligator `MAP` (RFC 9496 §4.3.4) `ZMod p → E`, with on-curve (old project: `sorry`), denominators `≠ 0`, image ⊆ `2E` | `elligator_ristretto_flavor`, `map_to_curve`, `from_uniform_bytes` |
| M14 | Ristretto constants as field facts: `√−1` (exists: `sqrtM1`), `INVSQRT_A_MINUS_D = 1/√(a−d)` (spec exists: `r² (a−d) = 1`), `SQRT_AD_MINUS_ONE`, `ONE_MINUS_EDWARDS_D_SQUARED`, `EDWARDS_D_MINUS_ONE_SQUARED` (sign of the roots matters for byte-exact RFC agreement: RFC fixes the non-negative ones) | M12, M13 |
| (opt) | Ristretto group `2E ⧸ E[4]` of order ℓ (needs `#E = 8ℓ`, point counting) | no statement needs it; only documentation of "prime order" |

##### 5.2 REPRESENTATION (dalek-specific; belongs in `Defs/**`)

| # | Notion | Needed by |
|---|---|---|
| R1 | `FieldElement51 → ZMod p` (`⟦x⟧ := (x.asNat : ZMod p)`). The field layer states everything in `ℕ % p`; point specs need `ZMod p` to talk about curves | all point items |
| R2 | `MontgomeryPoint.u : ZMod p := ((m.asNat % 2^255 : ℕ) : ZMod p)` (top bit masked, then mod p; `Array.asNat 8` exists) | all Montgomery inputs |
| R3 | Canonical output encoding: `r.asNat < p ∧ (r.asNat : ZMod p) = u` (for MontgomeryPoint and CompressedRistretto outputs) | all byte outputs |
| R4 | Montgomery `ProjectivePoint (U:W) ↦ U·W⁻¹` (0 if `W = 0`) and P¹-equality for the ladder invariant | `as_affine`, ladder loops (private) |
| R5 | `EdwardsPoint.toPoint : … → E.Point` and `EdwardsPoint.IsValid` (on curve, `Z ≠ 0`, `XY = ZT`, limb bounds) — from the Edwards analysis | `to_edwards`, `to_montgomery*`, all Ristretto |
| R6 | `RistrettoPoint.IsValid P := P.IsValid ∧ IsEven P.toPoint` (RistrettoPoint is literally `EdwardsPoint`) | every RistrettoPoint input/output |
| R7 | `CompressedRistretto` bytes `↦ s = bytes.asNat` with canonicity `s < p` (full 256 bits) and sign `s % 2` | `decompress`, `step_1`, `compress` |
| R8 | `Iterator.Yields` (exists), big-endian bits → ℕ (`Nat.ofDigits 2 bs.reverse`) | `mul_bits_be`, `double_and_compress_batch`, `Sum`, multiscalar |
| R9 | `Scalar.asNat` (exists), `clamp` (exists via `clamp_integer`) | `Mul`, `mul_clamped`, `mul_base*` |
| R10 | Edwards basepoint-table / precomputed-Straus validity predicates (from the Edwards analysis) | Ristretto tables, `VartimeRistrettoPrecomputation`, `RISTRETTO_BASEPOINT_TABLE` |

#### 6. Comparison with the old project and FFEC

**Good statement shapes to keep**
- `from_slice_spec` (two implications on the slice length), `step_2_spec` (flags ↔ field conditions,
  plus `∀ P, decompress_step2 s = some P ↔ flags ∧ pt.toPoint = P`), `ct_eq_spec` for
  MontgomeryPoint (`≡ mod p` of the 255-bit values; restate with `%`), `as_affine_spec`
  (`bytes = U/W`), arithmetic specs `result.toPoint = self.toPoint + other.toPoint ∧ result.IsValid`
  (exact Edwards equality, plus invariant).
- `RistrettoPoint.IsValid = EdwardsPoint.IsValid ∧ even` is the right invariant.
- `from_uniform_bytes_spec = elligator(lower) + elligator(upper)` is the right shape.

**Wrong or unprovable statements**
- `Montgomery mul_spec`: `mkPoint result = m • mkPoint P` is **false** in general: (1) `mkPoint`
  picks `v` via `sqrt_checked`, so the two sides can differ by the sign of `v`; (2) `mkPoint` sends
  `u = 0` to `T_point`, so whenever `m•P = ∞` (e.g. low-order inputs, clamped scalars) the LHS is
  `T_point ≠ 0`; (3) twist inputs are mapped to `T_point` junk. It rests on `mul_loop_spec`
  (three `sorry`s). `mul_clamped_spec` and the scalar-left `mul_spec`s inherit this. `mul_base_spec`
  patches (1)/(2) with `abs_montgomery` and an `ep.y = 1` case split (awkward). Fix: state everything
  through `u₀` / `xMul`, never through a full Montgomery point recovered from `u`.
- `hP_bound : U8x32_as_Nat P < 2^255` on Montgomery `mul`: not needed (masking).
- `differential_add_and_double_spec`: quantifies over curve points only (no twist), and the
  ladder-state predicate excludes `u = 0` and `P = Q`, so it cannot carry the full ladder.
- `to_edwards_spec`: only `some ep → y(u+1) = u−1`; says nothing about when `none` happens or about
  the sign. Too weak to be useful.
- `MontgomeryPoint.IsValid` = "lifts to Edwards", `MontgomeryPoint.toPoint` returns `0` when invalid,
  `CompressedRistretto.toPoint` returns `0` on failure: junk values that make statements silently
  wrong on invalid inputs. Prefer `Option` or explicit `↔` characterisations.
- Ristretto `ct_eq_spec` just restates the code (`X1Y2 ≡ Y1X2 ∨ X1X2 ≡ Y1Y2`): no mathematical
  meaning. Replace with `P − Q ∈ E[4]`.
- `compress_spec` / `decompress_spec` are relative to `compress_pure` / `decompress_pure`, which mirror
  the code formula by formula. Missing: coset invariance, injectivity, round trip. (FFEC notes
  confirm: "dalek proves only that decompression succeeds on even points, not the full round-trip".)
- `sorry`s in the math layer: `IsEven_iff_in_doubling_image_right` (2-descent), `on_curve` of
  `elligator_ristretto_flavor_pure`, `mul_loop_spec`.

**FFEC**
- Useful: `MontgomeryModel` with general `B` (so the twist is free), `map` (base change), group by
  transport (no `sorry`), `xCoord`, `uADD`/`uDBL` stated for general `B`, `pointEquivMont`, `A±2`,
  `A²−4` facts, `edwardsD_not_square`.
- Caveats: `TwistedEdwardsModel.toMontgomery` gives `B = −486664`, not Curve25519's `B = 1` (needs the
  scaling iso, see M7). `Examples/Curve25519.lean` has `instance : Fact (Nat.Prime p) := sorry`
  (line 51; the `prime_cert%` proof is commented out) although its docstring says "no sorry" — this
  project already has its own primality proof (`Curve25519/Prime.lean`). `notes/future-work.md` §3
  says "the even subgroup 2·E itself has order 2ℓ (index 4)": wrong. `E(F_p) ≅ Z/8 × Z/ℓ` has a
  single rational 2-torsion point, so `[E : 2E] = 2`, `|2E| = 4ℓ`, and the Ristretto group
  `2E/E[4]` has order ℓ (≅ `E/E[8]` via doubling). MODELS.md's "quotient of Ed25519 by its
  cofactor-8 subgroup" is isomorphic but is **not** the representation dalek uses: dalek's
  representatives are even points and equality is modulo `E[4]`; with `E/E[8]` semantics `ct_eq`
  would be wrong on non-even points.
- FFEC's `uADD`/`uDBL` are affine identities with `x₁ ≠ x₂` / `y ≠ 0` side conditions; the ladder
  proof needs projective versions that also cover `∞` and `(0,0)` inputs (xDBL is total on P¹; xADD
  is correct whenever `u_D ∉ {0, ∞}`).

#### 7. Open design questions

##### (a) X25519 on the twist

Options:
1. *Restrict to curve inputs* (`IsSquare (f u)` precondition). Cheapest, but the spec says nothing
   about what the code does on twist points, which is exactly the attacker-controlled case X25519 is
   designed for (twist security). Not faithful.
2. *Model the twist*: Montgomery curves with general `B` (FFEC already has them, with the group);
   `E_M` (`B=1`) and `E_M'` (`B=2`); `xMul n u := u₀([n]Q)` with `Q` on whichever of the two contains a
   point with `u₀ = u`. Well-definedness: `u₀([n](−Q)) = u₀([n]Q)`, and for `u = 0` both give `0`.
3. *x-only semantics on P¹(F_p)*: either via base change to `F_{p²}` (one curve, every `u ∈ F_p`
   lifts; Bernstein's Theorem 2.1 shape) or via the Kummer-line maps / division polynomials.
   Faithful too, but needs `GaloisField p 2`, points over it and a proof that the result lies in
   `F_p`; defining `[n]` on P¹ directly by recursion just restates the ladder and has no meaning.

**Recommendation: option 2.** It is the minimum that is faithful for **all** 2^256 inputs (with
`bytesU`, `xMul` total, and `0` covering both `∞` and `(0,0)`), it costs no new group theory
(general-`B` Montgomery curves come with FFEC's transported group), and `to_edwards`'s `none` case is
then simply "`u` comes from the twist only". State public specs only via `xMul`/`x25519`; keep
`differential_add_and_double` algebraic so the curve/twist case split lives in `Helpers`.

##### (b) Ristretto: quotient type vs representatives

Minimal structure that makes all specs statable and meaningful:
- the Ed25519 group (Edwards layer);
- `E[4]` (explicit four points, or `{Q | 4•Q = 0}`) and `≈`;
- `IsEven` / `2E` as an `AddSubgroup` (doubling image);
- RFC 9496 `ristrettoDecode`, `ristrettoEncode`, `ristrettoMap` as pure `ZMod p` functions, plus
  the theorems of M12/M13.

Statements then speak about Edwards representatives: arithmetic gives **exact** Edwards equalities
(stronger than coset equality, and trivially implies it), `ct_eq`/`eq` give `≈`, `compress` gives
`encode` (with coset invariance as a theorem), `decompress` gives `decode` (with the round trip).
A quotient type `2E ⧸ E[4]` adds nothing a statement needs. It would only be needed to *state* "prime
order", which in turn needs `#E = 8ℓ` (point counting, not available). **Recommendation:** no quotient
type for now. Define `IsEven Q :↔ ∃ R, Q = 2•R` (closure under `+`, `−`, `•` is then free, so the
arithmetic layer needs no descent), and prove "`decode` lands in `2E`" and "`MAP` lands in `2E`" by
exhibiting halves or via the 2-descent lemma `IsSquare (1 − y²) → ∈ 2E` (M11; the open `sorry` of the
old project). If wanted later, `QuotientAddGroup.mk` on `E ⧸ E[4]` can be added as a thin layer
without changing any statement.

##### (c) Can the Ristretto layer be deferred?

Yes. Its arithmetic items are thin wrappers over Edwards (`add`, `sub`, `neg`, `mul`, `mul_base`,
`multiscalar`, tables), so their specs follow the Edwards specs almost verbatim once M10/M11 exist.
Its genuinely new content (encode/decode/MAP, the descent lemma, RFC constants with sign
conventions) is self-contained and only needed by Ristretto. The Montgomery layer depends on Edwards
only through `to_edwards`, `to_montgomery*` and `mul_base*`. The x-only ladder part (`mul`,
`mul_bits_be`, `mul_clamped`, `differential_add_and_double`, `as_affine`) needs only M1–M4 and can go
first, even before the Edwards group is in place. Suggested order: Montgomery ladder → Edwards →
Montgomery↔Edwards (`to_edwards`, `to_montgomery*`, `mul_base*`) → Ristretto arithmetic (with
`IsEven := ∃ R, Q = 2R`, `E[4]`) → Ristretto encoding/elligator (M12–M14).

##### Smaller open points

- `mul_base` precondition: `s.asNat < 2^255` comes from the Edwards spec; check whether
  `EdwardsPoint::mul_base` (tables: `as_radix_16`, no-tables: variable-base mul) really fails
  otherwise (`debug_assert` → `massert`) before freezing it.
- For `to_edwards`, decide between `y(P) = (u−1)/(u+1)` (formula, no `φ` needed) and
  `u₀(φ(P)) = u` (needs M7 in the statement). The formula version is smaller.
- `ristrettoEncode` as a formula-level definition vs a relational `compress` spec ("canonical, even,
  and `decode r ≈ P`"). The relational one avoids a second formula-level definition but needs the
  existence and uniqueness theorems to be meaningful. Either needs the M12 theorems for meaning.
- i686 variants: same statements over `FieldElement2625`; blocked on the u32 field layer.
