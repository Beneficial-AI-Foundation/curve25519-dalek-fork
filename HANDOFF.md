# Handoff: state of the verification work (paused 2026-10-20)

For the next person or agent continuing the Lean verification of curve25519-dalek. Read this
first, then the documents it points to. Everything below is committed (up to `8419ef3`), except
this file, `experiments/`, `scripts/memwatch.sh` and the latest `notes.md` edits.

## 1. Documents to read, in this order

1. `AGENTS.md` (PRs to the curve25519-dalek repo must be written by humans).
2. `verif-guidelines.md`: all conventions (libraries, hidden definitions, `_def` lemmas, layout,
   spec summary format with `recall` + `#guard_msgs` axiom guards, statement conventions, proof
   quality, **memory rules**, CI, and the "Curves" section).
3. `curve-api.md`: the reference for the elliptic-curve libraries `EllipticCurve` and
   `Curve25519` (terminology curve / model / coordinates, principles, every API, all decisions
   in §10, and "Implementation notes" under each section recording what was actually built).
4. `curve-requirements.md`: what each point-related Rust item needs, item by item (Appendix A:
   Edwards side; Appendix B: Montgomery and Ristretto), with draft postconditions, limb bounds
   forced by the code, and edge cases. Use it as the brief for the remaining files.
5. `notes.md`: to-do list, decisions taken, campaign status, and the open decision on the
   precomputed tables (with measurements).
6. `extraction.md` (how the translation and its patches are produced), `step-star-performance.md`
   (why long `step*` chains are slow, and how to split them).

## 2. What is done

**Translation, field and scalar layers** (earlier work, committed): see `notes.md` "Spec campaign
status". `src/scalar.rs` has a full spec summary (`Specs/Scalar.lean`) for 64-bit targets.

**Curve framework** (all built):
- `EllipticCurve` (generic, Mathlib-bound): abstract `Curve F` (hidden quotient of Weierstrass
  models by isomorphism), Montgomery and twisted Edwards models with their own point types and
  groups, Edwards↔Montgomery equivalence, five coordinate systems with dalek's formulas, x-only
  ladder and `xMul` on curve and twist, even quotient (Decaf/Ristretto), RFC 8032 encoding,
  `ZMod.isNeg`/`abs`, point-group isomorphism along a variable change, twist point counts.
- `Curve25519`: models, basepoint (`addOrderOf = L`), `card = 8L`, torsion, `x25519` (RFC 7748
  vectors), Ed25519 encoding, `Ristretto` (order `L`, 2-descent, RFC 9496 encode/decode/map with
  vectors). No `sorry`, no `native_decide`, standard axioms only.

**Dalek layer** (built with `lake build Proofs Specs --wfail`, linters clean):
- `Defs/{FieldElement51 (toField), CurveModels, Edwards, Montgomery, Ristretto, Window,
  ScalarMul, Iterator}.lean`: meaning of every point struct (`toX` coordinates, `OnCurve`,
  `Bounded`, `toPoint`), byte encodings, the lenient decoder `decodeLenient`, table predicates.
- `Proofs/Helpers/{ToField, Coords, Edwards, EdwardsMontgomery, Window, Naf, BasepointTable,
  Iterator, Vec, Collect, Cmp}.lean`: bridges from the field specs (`asNat % p`) to `toField`, and
  shared lemmas.
- `backend/serial/curve_models.rs`: all items, both x86_64 variants
  (`Proofs/Backend/Serial/CurveModels/`, 21 files; no summary, the module is not public).
- `window.rs`: all `select`/`From` items (`Proofs/Window/`; no summary, `pub(crate)`).
- `scalar_mul/*` and `backend/mod.rs` dispatchers: variable base, vartime double base, Straus,
  Pippenger, precomputed Straus.
- `edwards.rs`, `edwards/affine.rs`: complete except the items in §3, both variants
  (`Proofs/Edwards/`, summary `Specs/Edwards.lean`, 149 statements).
- `traits.rs`: generic `is_identity` (`Proofs/Traits/IsIdentity.lean`, `Specs/Traits.lean`).
- Point constants: `ED25519_BASEPOINT_POINT`, `EIGHT_TORSION`, `BASEPOINT_ORDER`,
  `ED25519_BASEPOINT_COMPRESSED`, `X25519_BASEPOINT` (`Specs/Constants.lean`).
- All x86_64 items are stated for both `«x86_64-tables»` and `«x86_64-no-tables»`; i686 variants
  wait for the u32 backend.

## 3. Open decisions (for the owner) and known gaps

1. **Precomputed tables** (`notes.md`, table of options a–e with measurements; experiments in
   `experiments/`). Currently the with-tables `mul_base`, `mul_base_clamped` and
   `vartime_double_scalar_mul_basepoint` are proved as `_of_table` theorems with an explicit
   hypothesis that the constant represents the basepoint, and are not in the spec summaries.
2. **`_of_table` theorems in the summaries:** include them with their hypothesis, or wait.
3. **`VartimePrecomputedMultiscalarMul::is_empty`:** blocked; `alloc.vec.Vec.is_empty` is opaque
   without a spec. Needs a decision: a spec axiom in `FunsExternal.lean` (as was decided for
   `core.result.Result.map_spec`), a body, or leaving the item out.
4. **`vartime_triple_scalar_mul_basepoint`:** not done; needs the `_128` odd-multiples table
   (decision 1) and a lemma "NAF digits above index 128 are zero for `x < 2^128`".
5. **Aeneas-generated axioms in guard lists:** `…_native.decide.ax_*` (from `toStr` on panic
   messages) and `core.fmt.Formatter` now appear in the multiscalar/table guards; acceptable for
   now? (already a to-do in `notes.md`).
6. **Iterator lengths:** lists from iterators need `length ≤ Usize.max` hypotheses; acceptable?
7. **Long lines:** 40 commands in generated proof files disable the long-line linter although
   some names exceed 100 characters only with indentation (the guideline allows the option only
   for single tokens over 100). Shorten via `open`/local abbreviations, or accept.
8. Minor: `PrecomputedStraus/OptionalMixedMultiscalarMul.lean` takes 18–23 s (over the 20 s flag;
   split the two variants into two files); window tables' `Default`/`Clone`/`Zeroize` not specified
   (low value); naming ambiguity `encode`/`decode`/`basepoint` between `curve25519` and
   `curve25519.Ristretto` under a double `open`; `twistL` and `ZMod.abs` names unconfirmed.

Decisions already taken in this campaign are recorded in `curve-api.md` §10 and `notes.md`
("Spec campaign status"): keep `Result.map_spec` as an axiom; `is_identity` summarised once,
generically, in `Specs/Traits.lean`; table decision deferred until the data is in (it now is).

## 4. Next steps (the plan)

1. Owner decisions on §3.1–3.3, then the corresponding work (and `vartime_triple…`).
2. `montgomery.rs`: brief in `curve-requirements.md` Appendix B §1–2; library support in
   `Curve25519/{X25519,Montgomery}.lean` (`x25519`, `xMul`, `ladder_eq_xMul`, `x25519_eq_u_nsmul`,
   `x25519_basepoint_edwards`, `edwardsToMontgomery`, `montgomeryTwist`) and `Defs/Montgomery.lean`
   (`MontgomeryPoint.u`, `ProjectivePoint.toXZ`, `Bounded`). Note `mul_clamped` is exactly RFC 7748
   X25519 (byte-exact via `x25519`), `Mul` uses `scalar.asNat % 2^255` with no precondition, and
   the old project's Montgomery `mul_spec` was false (do not port it).
3. `ristretto.rs` (+ `elligator.rs`): Appendix B §4; library support in `Curve25519/Ristretto/*`
   (`Rel`, `rel_iff_formula` = meaning of `ct_eq`, `even_iff_isSquare`, `decodeRep`/`encodeRep`,
   `sqrtRatioM1` with the uniqueness lemmas to match `sqrt_ratio_i_spec` via
   `Proofs/Helpers/ToField.lean`'s `sqrtRatioM1_eq_of_spec`, `mapRep`, `fromUniformRep`). The
   private `conditional_negate_spec` duplicated in `Proofs/Field/SqrtRatioI.lean` and
   `Proofs/Edwards/Decompress.lean` should move to `Proofs/Helpers` first.
4. Remaining files (`constants.rs` Ristretto constants, `lizard` is untranslated, …), then the u32
   backend (i686 variants), then the j-invariant backend for `Curve F` (`curve-api.md` §3).

## 5. How the work was done (method that worked)

- One Rust file (or batch of ~40 items) per agent task, run **sequentially**: the machine has
  31 GB and has crashed; ONE Lean process at a time, `LEAN_NUM_THREADS=8`, no lean-lsp MCP tools
  in agents, single-module builds while iterating, a memory watchdog (kill the largest `lean`
  under 3 GB free; `scripts/memwatch.sh`, run it in the background).
- Each brief listed: documents to read, the items (from `Funs.lean` / `translation.json` / the
  requirements appendix), the statement shapes, the checks (`lake build Proofs Specs --wfail`,
  `lake exe runLinter Proofs`/`Specs`, `#print axioms` of every new spec, per-file times, no
  `sorry`, **no new axioms without asking**), and the report format.
- Statement shapes: coordinate-level exact `@[step]` specs with `Bounded` hypotheses
  (`r.toCompleted = self.toProjective.double ∧ r.Bounded`), plus `_spec_point` corollaries
  (`r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.Bounded`); iterated operations (scalar
  multiplication) have point-level main specs. Hypotheses `hself`, `hother`, `hon`/`hself_on`,
  `hscalar`; scalars unreduced (`s.asNat • P`, precondition `s.asNat < 2^255`).
- Both x86_64 variants are written once as a template and duplicated by textual replacement of
  the suffix (`x86_64-tables` → `x86_64-no-tables`); the generator scripts were session-local.
- Spec summaries: `recall` in Rust item order, point-level forms, guards filled by
  `scripts/fill-guards.py` (`--strip`, then `lake env lean Specs/X.lean > out`, then fill).
- Pitfalls: destructure a `Bounded` hypothesis only after the `step` whose callee needs it;
  `@[local step]` is namespace-scoped (use `step with` for private loop/inner specs); a
  non-`module` scratch file sees hidden bodies, so test hiding from a `module`; `ZMod p` inversion
  does not reduce in the kernel (use the inversion-free `Extended.nsmul`/`IsZero` for
  certificates); `p`, `L` unfold only in modules that `import all Curve25519.Basic`.
