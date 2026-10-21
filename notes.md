# Notes

Working notes for the Lean verification of curve25519-dalek: the conventions, the state of the
work, the plan and the open decisions. Temporary: this file is removed from the repository at the
end, together with the references to it.

Read `AGENTS.md` first (PRs to the curve25519-dalek repo must be written by humans).

# Part I: Conventions

## Translation

```
./scripts/aeneas-install.sh     # charon + aeneas for the release pinned in lakefile.toml
./scripts/aeneas-translate.sh   # patch a copy of the workspace (.llbc/work/), run charon + aeneas
```

- **No post-translation tweaks.** `curve25519-dalek/lean/Curve25519Dalek/{Types,Funs}.lean` and
  `translation.json` are exactly what Aeneas emits. CI (`lean-translation.yml`) re-translates and
  fails if they differ from the committed files.
- **Configurations.** One translation covers four configurations, merged by Charon's
  multi-target mode: {64-bit, 32-bit} × {with, without `precomputed-tables`}. Items that differ
  get a suffix `«x86_64-tables»`, `«x86_64-no-tables»`, `«i686-tables»` or
  `«i686-no-tables»`; a façade dispatches on `get_target`.
- **Charon settings** live in `[package.metadata.charon]` in `curve25519-dalek/Cargo.toml`.
  - `exclude`: only items we will never verify (Debug, Hash, derived `Eq`).
  - `opaque`: only items we don't want to translate (currently none).
  - Everything else is translated; constructs Aeneas cannot handle are patched.
- **Namespace:** the translation lives in namespace `Curve25519Dalek` (Aeneas `-namespace`), in
  Lean style; the Rust crate path `curve25519_dalek::…` appears only in doc comments and
  `rust_fun` strings.
- **Rust changes only as translation patches.** `curve25519-dalek/src/` stays upstream.
  - **One file per function,** `curve25519-dalek/translation-patches/<file-stem>-<function>.patch`. Add `-<Type>` before `<function>` only when the name alone is ambiguous.
  - **Header:** a short free-text header (Change / Why / Behaviour, plus "Relies on" if needed) before the `git diff -W` body.
  - **Applying:** patches are applied in file-name order to a copy of the workspace (`.llbc/work/`); `src/` is never modified. Each patch applies on top of the previous ones, with `git apply` (no fuzz). If two patches touch neighbouring functions, trim the context at the boundary.
  - **Behaviour:** must stay identical. Patches that differ say so in their header (the multiscalar `size_hint` patches, `constants-RISTRETTO_BASEPOINT_TABLE`).
- **External files are hand-written.** `FunsExternal.lean` and `TypesExternal.lean` are never
  overwritten. After each translation, compare them against the gitignored
  `*External_Template.lean` files Aeneas emits, and update them by hand.
- **External function signatures are `opaque`** wherever possible (the template prints `axiom`;
  replace it), so that they add no axiom. Their behaviour is then given by spec axioms, which are
  the only trusted additions and are listed by `#print axioms`.

## Libraries

| lean_lib | Namespace | Content | Audited |
|---|---|---|---|
| `EllipticCurve` | top level (`Curve`, `MontgomeryModel`, …) | Elliptic-curve models over a field, independent of any curve; Mathlib-bound | yes, except `EllipticCurve/Proofs/**` and `Curve/Impl.lean` |
| `Curve25519` | `curve25519` | Curve25519 in general (`p`, `L`, `a`, `d`, `A`, its models and facts), independent of dalek | yes |
| `Curve25519Dalek` | `Curve25519Dalek` | Generated translation + hand-written External files | External files |
| `Subtle`, `Zeroize` | as generated | Models of external crates | `Subtle/Types.lean`, `Basic.lean` |
| `Defs` | `Curve25519Dalek` (extensions of Aeneas types: their namespace) | Definitions needed to state the specs | yes |
| `Specs` | `Curve25519Dalek` | Spec summaries, one per Rust file | yes |
| `Proofs` | `Curve25519Dalek` | Proofs, one file per Rust item, and `Proofs/Helpers` | no |

All hand-written files use the Lean module system: `module` and `public section`.

**Exposing and hiding definitions:** a public definition is hidden unless marked `@[expose]`:
importing modules cannot unfold it at all (neither `unfold`, `simp`, `rfl`, `decide` nor the
kernel), only use the lemmas its own module proves about it. Mark `@[expose]` on each definition
that proofs in other modules must unfold (`OnX86_64`, for `dispatch_spec`), never on a whole
section, and hide everything else.

- **Defining equation:** each hidden definition `X` has `X_def : X = <body>`, proved by tactic in
  its own module (`by unfold X; rfl`; a term-mode `:= rfl` is rejected, because it would be a
  definitional lemma about a hidden body). Lean's own equation lemmas (`X.eq_def`) stay private to
  the module, so `X_def` is needed. Proofs rewrite with it (`rw [Scalar.asNat_def]`,
  `simpa only [… _def] using …`) instead of unfolding.
- **Further characterisations** are named after what they state, in Mathlib style
  (`p_eq_numeral`, `p_add_nineteen`, `p_lt_two_pow_255`, `d_eq_natCast`, `Array.asNat_eq_sum`).
  Several forms of one fact are welcome; proofs use whichever fits.
- **`noncomputable`:** a hidden definition whose type depends on another hidden value
  (`a : ZMod p`) is `noncomputable`.
- A non-`module` scratch file sees hidden bodies, so test hiding from a `module`.

**Public vs private imports:** `public import` only what the file's public statements and definitions
mention (types, `Defs`, `Curve25519.Basic`, …); it is re-exported downstream. Import what only proofs
use (callees' proof files, `Proofs.Helpers`, tactics such as `Mathlib.Tactic.LinearCombination`)
with plain `import`. `lake shake Subtle Zeroize Curve25519 Defs Specs Proofs` reports both unused
imports and public
imports that can be private; it misses namespaces used only in `open`, and `@[step]` specs that
`step` finds through an import, so check its suggestions with `lake build`. (Not on
`Curve25519Dalek`: its generated files are rewritten by every translation.)

**Licence and copyright headers:** the Lean development is Apache 2.0
(`curve25519-dalek/lean/LICENSE`); the Rust crate stays BSD-3-Clause. Every hand-written Lean
file starts with the header below, then `module`. A file ported from the previous project
(curve25519-dalek-lean-verify) keeps that file's header (year and authors) verbatim; a merged file
lists the union of its sources' authors; a new file has no `Authors:` line. Root aggregation
files (`Specs.lean`, `Proofs.lean`, `Subtle.lean`, …) and the Aeneas-generated files have no header, as in
Mathlib. (Mathlib's header linter is disabled in `lakefile.toml`: it never runs with our `srcDir`.)
```
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
```

**External-crate libraries (`Subtle`, `Zeroize`):**
- **Trusted part:** `<Lib>/Types.lean` (types only) and `<Lib>/Basic.lean`. Basic holds `opaque` signatures with the template names, plus one `@[step]` spec axiom per function. Each spec axiom is conditional on any trait-instance behaviour it relies on. Verbatim bodies appear only where `impl_def` must unfold them (`@[trait_default]`).
- **Derived part:** `<Lib>/Lemmas.lean` (generic), `<Lib>/Instances.lean` (about instances in `Funs.lean`) and `Zeroize/Consistency.lean`. They add no axioms.
- **Imports:** `FunsExternal.lean` imports only `<Lib>.Basic`.

## Curves (`EllipticCurve`, `Curve25519`)

Conventions specific to these two libraries:

- **Topic = definitions module + properties module.** `…/Defs.lean` holds structures, hidden
  definitions and instances; `…/Lemmas.lean` does `import all …/Defs` and proves the
  characterising lemmas (the audited statements). Heavy proofs go in `…/Proofs/*.lean` (not
  audited), which also `import all` the definitions; the audited module re-exports their results.
- **Constructions meant to be swappable** (`Curve`, `Curve.Point`, the group instances,
  `toPoint`, `toCurve`, `pointEquiv`, the model-to-model equivalences, `xMul`, `decode*`) have no
  `_def` lemma, only characterising lemmas; `Weierstrass` names never appear in an API signature
  (`Curve/Impl.lean` and `Weierstrass/PointEquiv.lean` are imported privately).
- **Exposed are formulas only** (`Equation`, `OnCurve`, `ProjEq`, `isNeg`, `abs`, the coordinate
  formulas, `nsmul`/`ladder`/`clamp`/`x25519`, `encode`), so that `decide` can evaluate them.
  Instances on hidden types carry `@[no_expose]`; everything on them is `noncomputable`.
- **Certificates** (`Curve25519/Proofs/**`): `import all Curve25519.Basic` so the kernel can
  unfold `p`, `L`; use the inversion-free `Extended.nsmul`/`IsZero` (`decide +kernel`), never a
  field inverse (`ZMod` inversion is well-founded recursion and does not reduce); numeric facts by
  `rw [p_eq_numeral]; norm_num; reduce_mod_char` or the `norm_num` Legendre-symbol extension.
  `native_decide` is banned. RFC test vectors live in `Proofs/*/TestVector.lean`, imported
  privately by the root so CI checks them.
- **Hypotheses:** `IsNonsingular`/`IsComplete` include `(2 : F) ≠ 0`; oddness of `p` is an explicit
  `(hp : p % 2 = 1)` in generic sign lemmas; `[Finite F]` where a square/non-square dichotomy is
  used.

## Layout

The hand-written Lean about dalek's items is in:

```
Specs/Foo/Bar.lean                 spec summary of src/foo/bar.rs (audited)
Proofs/Foo/Bar/Reduce.lean         proof of fn `reduce` in src/foo/bar.rs
Proofs/Helpers/<Topic>.lean        further theorems used by the proofs (never inspected)
Defs/<Topic>.lean                  definitions needed to state the specs (audited)
```

- **`Specs/`** mirrors the Rust `src/` tree, with UpperCamelCase names: one file per Rust file with
  items in the crate's public API, holding that file's spec summary (below). Files with no public
  item (`field.rs`, `backend/**`) have no spec summary: their specs are proved in `Proofs/` and
  matter only through the public ones.
- **`Proofs/`** mirrors it too, with a folder per Rust file and one proof file per Rust item
  (function, trait method, inner `fn`, const), named after it. A proof file also holds that item's
  loops, loop bodies, inner functions and closure helpers. Items that are essentially the same
  function share its file: e.g. the by-value variants of an operator generated by
  `define_*_variants!`, which forward to the borrowed impl, are in that impl's file (`Mul.lean`
  holds `&Scalar * &Scalar` and the three by-value forms). Two items with the same name are
  otherwise told apart by a prefix for the type when it is not the file's main type
  (`HalfWidthEq.lean`, `Scalar52Pack.lean`).
- **`Proofs/Helpers/`** holds every further theorem the proofs use, and any auxiliary definitions
  they share. Nobody needs to inspect it.
- **`Defs/`** holds the definitions needed to write the spec statements, in the minimal possible
  way: only what a statement uses, plus the unfolding lemma of a hidden definition
  (`montgomeryRadix_def`). Other characterisations go in `Helpers`.
- **Imports:** a spec summary imports its Rust file's proof files; a proof file imports its callees'
  proof files, `Defs`, `Helpers` and libraries, never `Specs`. The root `Specs.lean` imports every
  spec summary.
  - Public: what a file's statements mention (`Curve25519Dalek.Funs`, `Defs`, `Curve25519`,
    external libraries). Private: proof files (a spec summary's own, or a proof file's callees')
    and `Helpers`.
  - A spec summary also imports the modules declaring the axioms in its `#guard_msgs` lists.
- (`Aux` is a reserved file name on Windows, which Lean rejects.)

## Spec summary format

- **Proof file:** holds the canonical `@[step]` theorem, used by `step`.
- **Spec summary:** restates the statement verbatim with `recall` (Mathlib), which checks that it
  is the statement of the proved theorem, followed by its axioms:

```lean
/-- `square`: `r = self²` mod `p`; limbs `< 2^54` in, `< 2^52` out. -/
recall square_spec (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    square self ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ 2 % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms square_spec
```

  The axiom list is matched as a substring, with whitespace collapsed (Lean wraps the list when the
  name is long). A list over 100 characters is wrapped at the commas.

- **Order:** the statements appear in the order of the items in the Rust file.
- **Same statement:** `recall` fails unless the restated statement agrees with the proved one, up to
  definitional equality. It adds no declaration.
- **Pinned axioms:** `#guard_msgs` fixes the axioms each statement rests on.
  - `sorryAx` while the proof is pending (only on a working branch: CI rejects `sorry`).
  - Any `Subtle`/`Zeroize` spec axioms or std externals (`FunsExternal.lean`) that the proof uses.
  - For dispatched functions: `get_target` and the `…_native.decide.ax_*` axioms of Aeneas's
    `toStr` (the string literals of the dispatchers and of `OnX86_64`). Accepted: they only assert
    that each literal's byte length fits a `u32` (see "`native_decide` from Aeneas's `toStr`").
  - Update the list when a proof lands.
  - `#print axioms` prints an axiom by its shortest name that resolves in the spec summary, so
    the module declaring it must be visible there. A proof file importing it privately is not
    enough: the spec summary then imports it itself.
- **Filling the guards:** `scripts/fill-guards.py` (`--strip`, then `lake env lean Specs/X.lean >
  out`, then fill; usage in its docstring).
- **Auditing:** an auditor reads `Curve25519/**`, `Defs/**`, `Specs/**`, the External files
  (`Curve25519Dalek/{Types,Funs}External.lean`), `Subtle/{Types,Basic}.lean` and
  `Zeroize/Basic.lean`. Nothing else.

## Statement conventions

- **Coverage:** a spec summary states only items of its Rust file in the crate's public API
  (function, method, trait method, constant): the items reachable from the crate root, i.e. what
  rustdoc documents. Every such item has at least one statement; an item may have several (e.g. for
  different preconditions). Items outside the public API still get proved specs in their proof
  files. The by-value operator variants generated by `define_*_variants!` are public items and
  have statements. Not covered: closure `call_mut`/`call_once` wrappers, derived `Clone`/`Copy`,
  `Debug`, local consts inside a function body; their helper specs may exist in proof files.
- **Names:**
  - theorems are `<function>_spec`, in the function's namespace;
  - argument names are exactly the identifiers of the specified Lean/Rust function (`self`, `_rhs`, `limbs`, …);
    trait-instance arguments, which have no Rust name, are short (`borrowInst`, `iterInst`);
  - hypothesis names follow Mathlib: `h` + the argument (`hself`, `hrhs`, `hk`);
  - spec definitions follow Mathlib conventions: lowerCamelCase for data (`asNat`), UpperCamelCase for `Prop`s. Use dot notation (`self.asNat`). When the argument has the raw underlying type (`Array U64 5#usize`, as in `reduce`), write `FieldElement51.asNat limbs`.
- **Form:**
  - `@[step]` on its own line, then `f args ⦃ (r : T) => post₁ ∧ post₂ ⦄`;
  - the result type is always annotated, and tuples are decomposed in the binder (`⦃ (a' : T) (b' : T) => … ⦄`);
  - indentation: 0 for the theorem line, 4 for arguments, 6 for postconditions, 2 for the proof.
- **Content:**
  - no "succeeds" conjunct and no no-panic remark: the triple always proves it;
  - modular equalities use `%` (`r.asNat % p = self.asNat ^ 2 % p`), not `≡ [MOD p]`;
  - limb bounds are inline (`∀ i < 5, r[i]!.val < 2 ^ 52`), one `∀` per fact;
  - **bounds are as simple as all uses allow**, not as tight as the code allows: powers of two
    with `<`. For the u64 field, every operation takes limbs `< 2^54` (the crate's lazy-reduction
    invariant) and outputs `< 2^52` (`< 2^53` for `square2`, `< 2^51` for canonical values);
  - **no natural-number subtraction or division that could truncate**: move terms to the other
    side (`r.asNat + 1 = p`, `(r.asNat + _rhs.asNat) % p = self.asNat % p`, `r.asNat * 4 = A + 2`);
  - lines stay within 100 characters (wrap conjuncts).
- **Point statements:** coordinate-level exact `@[step]` specs with `Bounded` hypotheses
  (`r.toCompleted = self.toProjective.double ∧ r.Bounded`), plus `_spec_point` corollaries
  (`r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.Bounded`); iterated operations (scalar
  multiplication) have point-level main specs, and the spec summaries use the point-level forms.
  Hypotheses `hself`, `hother`, `hon`/`hself_on`, `hscalar`; scalars unreduced (`s.asNat • P`,
  precondition `s.asNat < 2^255`).
- **Line length (all hand-written files):** the 100-character linter is never switched off for a
  whole file. A long `namespace X.Y` is split into two consecutive `namespace` commands (closed by
  two `end`s); long strings use string gaps (`\` at the end of the line). Only a single token over
  100 characters justifies `set_option linter.style.longLine false in` on that one command.
- **`Choice` validity:** the `subtle` crate maintains the invariant that a `Choice` is `0` or `1`
  (`subtle.Choice.IsValid`, defined in `Subtle/Basic.lean`). Every spec (and `Subtle` spec
  axiom) with a `Choice` argument `c` assumes `(hc : c.IsValid)`, and every spec returning a
  `Choice` `c` states `c.IsValid` as its first conjunct.
- **Docstrings:** short. The function name (with its trait or type only when needed), then the
  content in a phrase (`limbs < 2^54 in, < 2^52 out`). No full Rust paths.
- **No explanatory comments** on linter options or `nolint` attributes.

## Proof quality

- **`step*` as far as it goes.** Proofs start `unfold f` then `step*`, and only close what `step*`
  leaves. When `step*` stops early, find out why (missing `@[step]` lemma, missing simp lemma) and
  fix that, instead of stepping by hand.
- **Fast.** Each proof file elaborates in seconds. Raise `maxHeartbeats` only with a reason, before
  the theorem (`set_option maxHeartbeats N in`), never inside a proof.
- **Logical parts.** A long function is split into parts with `#decompose` or into helper lemmas,
  one logical fact each, rather than one long tactic script.
- **Where helper lemmas go.** A lemma used by only one proof stays in that proof's file and is
  `private`. A lemma with wider use moves to `Proofs/Helpers/<Topic>.lean`; facts about curve25519
  constants go in `Curve25519/Basic.lean`. Shared lemmas are
  stated in their natural generality (e.g. for any radix or array length, not just the instance at
  hand).
- **Large powers (`exponent … exceeds the threshold 256`).** Lean core declines to evaluate
  `b ^ n` when the exponent `n` exceeds `exponentiation.threshold` (256) and warns, whenever
  unification, `simp` or `omega`/`scalar_tac` merely meet such a term. Name large powers as
  hidden (non-exposed) definitions (`p`, `L`, `montgomeryRadix` for `2^260`), with an unfolding
  lemma that is exactly the definition (`montgomeryRadix_def`); state specs with the name.
- **Export only the key specs.** A step lemma needed only inside its own file (loop specs,
  `#decompose` parts, closure `call_mut` specs, inner constants, variants with extra
  postconditions) is `@[local step] private theorem`. It is then neither visible nor registered
  for `step` outside the file (and does not leak a public `mvcgen_spec`). Public `@[step]`
  theorems are the audited specs and the few helper specs other files genuinely use.
  `@[local step]` is namespace-scoped: use `step with` for private loop and inner specs.
- **No auto-generated names.** Never refer to names a tactic invented (`h_1`, `x✝`, `a_post1`,
  `i1`). Name what you use (`step as ⟨r, hr⟩`, `obtain ⟨…⟩`, `intro`).
- **The curve constants cannot be unfolded.** `p`, `L`, `a`, `d`, `A` and `sqrtM1` are hidden
  definitions. Use their characterisation lemmas in `Curve25519/Basic.lean` (`p_eq_numeral`,
  `L_eq_numeral` give them as numerals; add new lemmas there). Only modules that
  `import all Curve25519.Basic` can unfold them.
- **No** `sorry`, `native_decide` or `admit`. `bv_decide` is allowed; its certificate axioms then
  appear in the spec summary's axiom list.
- **Tactics Aeneas's `aeneas-lean-core` guidance bans** (`omega`, `linarith`, `nlinarith`,
  `congr N`, …) are banned only in proofs about the generated code: spec theorems, loop specs and
  their helpers, where the goals involve Aeneas scalars and containers. In pure mathematical
  lemmas (e.g. about `Nat`, `ZMod p`, `Nat.ofDigits`), use whichever tactic is right, including
  these.
- **Statements are frozen.** A proof file never changes the statement text of its theorem.
- **Pitfalls:** destructure a `Bounded` hypothesis only after the `step` whose callee needs it;
  `ZMod p` inversion does not reduce in the kernel (certificates use the inversion-free
  `Extended.nsmul`/`IsZero`).
- **`Result` is a coinductive ITree** in this Aeneas (`Aeneas/Std/Primitives.lean`,
  `Data/Coinductive/ITree.lean`): `bind` is a fixed point and never reduces, so no `rfl`,
  `decide +kernel` or `with_unfolding_all` evaluates translated code across a bind, and rewriting
  a long bind chain step by step (`simp`, `rw`, an `Eq.trans` chain) keeps O(N²) copies of the
  chain alive (768 binds exhausted 15 GB and rebooted the machine, 2026-10-21). Translated
  constants are reduced by reflection instead: `Proofs/Helpers/TableCertificate.lean` (`bindList`,
  `bindList_eq`, `collect_limbs`, `kernel_rfl`), O(N) and a few seconds.

## Workflow per Rust file

1. **Inventory:** list the Rust items and their Lean names (`Funs.lean` doc comments,
   `translation.json`).
2. **Statements:** write the `Defs` additions, the proof files (theorems proved by `sorry`) and the spec summary. Fill the `#guard_msgs` lines with `scripts/fill-guards.py`.
3. **Review gate:** the owner reviews the spec summary and `Defs`. Statements are then frozen; any change needs sign-off.
4. **Proofs:** fill in the proofs following "Proof quality" (and the Aeneas `aeneas-lean-core`
   workflow), and update the `#guard_msgs` lines as they land.
5. **Done:** no `sorryAx` left in the spec summary. Only then does the work go to `main`: CI
   rejects any `sorry`, so steps 2–4 happen on a branch.

**With agents** (the method that worked): one Rust file, or a batch of about 40 items, per agent
task, run sequentially. Each brief lists the documents to read, the items, the statement shapes,
the checks (`lake build Proofs Specs --wfail`, `lake exe runLinter Proofs`/`Specs`,
`#print axioms` of every new spec, per-file times, no `sorry`, **no new axioms without asking**)
and the report format. Both x86_64 variants are written once as a template and duplicated by
replacing the suffix (`x86_64-tables` → `x86_64-no-tables`).

## Building locally (memory)

The machine has 15 GB and 22 cores; each Lean process uses 1–5 GB, so memory, not cores, limits
parallelism. `LEAN_NUM_THREADS` caps the number of Lean processes Lake runs at once, and `taskset`
keeps them (and their own threads) on a subset of the cores. Full builds:

```
LEAN_NUM_THREADS=4 taskset -c 0-3 nice -n 10 lake build
```

When several agents or builds run at once: check single files with `lake env lean <file>`, build
one module target per `lake build` command, run at most one Lean process per agent, and avoid
language-server tools in agents. `lake exe runLinter Specs` loads every library (the spec
summaries import everything); run the linter on one library per command when memory is tight.
`scripts/memwatch.sh`, run in the background, kills the largest `lean` process when free memory
gets low. Experiments that may blow up run in a capped scope, which kills only that process:
`systemd-run --user --scope -p MemoryMax=9G -p MemorySwapMax=0 lake env lean <file>`.

## CI

- **`lean-translation.yml`:** the translation is current.
- **`lean-build.yml`:**
  - `lake build --wfail` on every default target: any warning, including `sorry`, fails the build;
  - `runLinter` on `Subtle`, `Zeroize`, `EllipticCurve`, `Curve25519`, `Defs`, `Specs` and
    `Proofs`, one step each
    (`runLinter` stops at the first failing module).
- **`workspace.yml`:** the `typos` spell check skips `*.lean` (`.typos.toml`) but reads Markdown,
  so Lean identifiers in this file can trip it.

# Part II: State of the work

## Done

**Translation, field and scalar layers:**
- `src/scalar.rs`: all public items specified and proved, for 64-bit targets (`OnX86_64`); spec
  summary `Specs/Scalar.lean`.
- Proved but not public (no spec summary): `src/backend/serial/u64/field.rs`, `scalar.rs`,
  `constants.rs` and `src/field.rs`.
- Primality of `p`, `L`: Lucas certificates, Mathlib only.

**Curve framework** (2026-10-16 to 2026-10-20). Two libraries, both audited except their
`Proofs/**` and `Curve/Impl.lean`:

- **`EllipticCurve`** (generic, Mathlib-bound): the abstract `Curve F` (hidden quotient of
  Weierstrass models by isomorphism; `C.Point` a group), `MontgomeryModel`/`TwistedEdwardsModel`
  with their own point types and groups pinned by coordinate lemmas, the Edwards↔Montgomery
  equivalence, the five coordinate systems with dalek's formulas proved correct, the x-only
  ladder with `xMul` on curve and twist, the even quotient (Decaf/Ristretto construction), the
  RFC 8032 encoding, `ZMod.isNeg`/`abs`, the point-group isomorphism along a variable change
  (`Weierstrass/PointEquiv`, missing from Mathlib), point counts of a model and its twist.
- **`Curve25519`**: `edwards`, `montgomery`, `curve`, `basepoint` with `addOrderOf = L`,
  `card = 8L` (no point counting), the ℤ/8 × ℤ/L decomposition, the eight torsion points,
  `montgomeryBasepoint` (`u = 9`), `edwardsToMontgomery`, the twist (`4·twistL` points),
  RFC 7748 `x25519` with its test vectors, the Ed25519 encoding with `encode basepoint`, the
  `Ristretto` group (`card = L`), the 2-descent `even_iff_isSquare`, the RFC 9496 encoding,
  decoding and one-way map with the RFC test vectors.
- Trust: no `sorry`, no `native_decide`; every certificate is `decide +kernel` on the
  inversion-free `Extended.nsmul`/`IsZero` (253-step chains take ~0.2 s) or a `norm_num`
  Legendre-symbol computation; `#print axioms` is the standard three everywhere checked.
- Found along the way: Mathlib lacks the action of `VariableChange` on points (built here);
  the twist of curve25519 has `4·L'` points for a different prime `L'` (`twistL`), not `4L`;
  RFC 7748's `a24` is `(A−2)/4`; the descent map is `B·u` modulo squares.

**Dalek point layer** (2026-10-20):
- `Defs/{FieldElement51 (toField), CurveModels, Edwards, Montgomery, Ristretto, Window,
  ScalarMul, Iterator}.lean`: meaning of every point struct (`toX` coordinates, `OnCurve`,
  `Bounded`, `toPoint`), byte encodings, the lenient decoder `decodeLenient`, table predicates.
- `Proofs/Helpers/{ToField, Coords, Edwards, EdwardsMontgomery, Window, Naf, BasepointTable,
  Iterator, Vec, Collect, Cmp}.lean`: bridges from the field specs (`asNat % p`) to `toField`, and
  shared lemmas.
- `backend/serial/curve_models.rs`: all items (`Proofs/Backend/Serial/CurveModels/`; no
  summary, the module is not public).
- `window.rs`: all `select`/`From` items (`Proofs/Window/`; no summary, `pub(crate)`).
- `scalar_mul/*` and `backend/mod.rs` dispatchers: variable base, vartime double base, Straus,
  Pippenger, precomputed Straus.
- `edwards.rs`, `edwards/affine.rs`: complete except the gaps under "Open decisions"
  (`Proofs/Edwards/`, summary `Specs/Edwards.lean`, 149 statements).
- `traits.rs`: generic `is_identity` (`Proofs/Traits/IsIdentity.lean`, `Specs/Traits.lean`).
- Point constants: `ED25519_BASEPOINT_POINT`, `EIGHT_TORSION`, `BASEPOINT_ORDER`,
  `ED25519_BASEPOINT_COMPRESSED`, `X25519_BASEPOINT` (`Specs/Constants.lean`).
- Precomputed tables (2026-10-21): `ED25519_BASEPOINT_TABLE`, `AFFINE_ODD_MULTIPLES_OF_BASEPOINT`
  and `AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128` are certified unconditionally
  (`Proofs/Backend/Serial/U64/Constants/{Ed25519BasepointTable, AffineOddMultiplesOfBasepoint,
  AffineOddMultiplesOfBasepoint128}.lean` on `Proofs/Helpers/TableCertificate.lean`; standard
  axioms only, 3–11 s per file). `mul_base`, `mul_base_clamped` and
  `vartime_double_scalar_mul_basepoint` of `x86_64-tables` are therefore unconditional and in
  `Specs/Edwards.lean` (152 statements; the three new statements await the owner's review).
- All x86_64 items are stated for both `«x86_64-tables»` and `«x86_64-no-tables»`; the i686
  variants wait for the u32 backend.

## Decisions taken

- `core.result.Result.map_spec` (used by `CompressedEdwardsY::from_slice`) stays a spec axiom in
  `FunsExternal.lean`, consistent with `core.array.from_fn_spec` (2026-10-20).
- `IsIdentity::is_identity` (blanket impl in `traits.rs`, used by `EdwardsPoint`,
  `CompressedEdwardsY`, `MontgomeryPoint`, `RistrettoPoint`, `CompressedRistretto`) is summarised
  once, generically, in `Specs/Traits.lean`, conditional on the type's `ct_eq`/`identity`
  behaviour; the per-type summaries do not repeat it (2026-10-20).
- Spec summaries cover the crate's public API only; the coverage is checked by review, not by a
  committed script or CI step.

## Open decisions (for the owner) and known gaps

1. **`VartimePrecomputedMultiscalarMul::is_empty`:** blocked; `alloc.vec.Vec.is_empty` is opaque
   without a spec. Options: a spec axiom in `FunsExternal.lean` (as for
   `core.result.Result.map_spec`), a body, or leaving the item out.
2. **`vartime_triple_scalar_mul_basepoint`:** not done; the `_128` table is certified, what is
   left is a lemma "NAF digits above index 128 are zero for `x < 2^128`" and the proof.
3. **The three new `x86_64-tables` statements** in `Specs/Edwards.lean` (`mul_base`,
   `mul_base_clamped`, `vartime_double_scalar_mul_basepoint`): review (same shape as the
   `x86_64-no-tables` ones).
4. **Aeneas-generated axioms in guard lists:** `…_native.decide.ax_*` (from `toStr` on panic
   messages) and `core.fmt.Formatter` appear in the multiscalar/table guards; acceptable?
5. **Iterator lengths:** lists from iterators need `length ≤ Usize.max` hypotheses; acceptable?
6. **Long lines:** 40 commands in generated proof files disable the long-line linter although
   some names exceed 100 characters only with indentation (the convention allows the option only
   for single tokens over 100). Shorten via `open`/local abbreviations, or accept.
7. **Location of `Subtle` and `Zeroize`**, now that the hand-written Lean is split into `Defs/`,
   `Specs/` and `Proofs/` (see also "Project-defined traits" below).
8. Minor: `PrecomputedStraus/OptionalMixedMultiscalarMul.lean` takes 18–23 s (split the two
   variants into two files); window tables' `Default`/`Clone`/`Zeroize` not specified (low
   value); naming ambiguity `encode`/`decode`/`basepoint` between `curve25519` and
   `curve25519.Ristretto` under a double `open`; `twistL` and `ZMod.abs` names unconfirmed.

### Certifying the precomputed tables (done 2026-10-21)

Two parts, both kernel-checked, no literal written in the sources:

- **Extraction.** A translated constant is a chain of `from_limbs` binds ending in `ok (value)`;
  `bind` never reduces (ITree, see Pitfalls). `collect_limbs xs from c` (a command elaborator)
  reads the limb arrays off the chain without instantiating anything, `bindList xs k` is the
  generic shape with `bindList_eq : bindList xs k = k xs` by induction, and
  `c = bindList xs (fun fes => ok (mk fes))` is an `Eq.refl` checked by the kernel only
  (`kernel_rfl`; the elaborator's own defeq check would triple the time). `mk` rebuilds the
  structure from the flat list by `List.ofFn` indexing, so `c = ok (mk xs)` follows.
  Measured on the 768-bind table: 7 s, 2.7 GB (versus 47 s / 7.7 GB and a timeout for the old
  `simp [bind_ok]` route, and a reboot for an `Eq.trans` chain).
- **Content.** `Bool` checkers over the flat list, evaluated by `decide +kernel` after
  `rw [edwards_eq_numerals]`: `checkRow S Q l` (entries `Q, Q + S, Q + 2 S, …`, by running
  additions in extended coordinates and three cross-multiplication equalities per entry, so no
  inversion), `checkRowProj` (projective Niels entries), `checkTable P fes n` (rows
  `P, 2^8 P, …` by 8 doublings each). Soundness is proved once, generically
  (`checkRow_sound`, `checkTable_sound`); the big table's 256 entries check in ~2 s. Checkers
  walk the list linearly: indexing through `mk` in the certificate itself cost 24 s / 4.9 GB.
  Negative controls (a corrupted limb, a duplicated row) fail as they should.

Rejected: per-entry `nsmul` certificates (30 s, 3.4 GB per file, measured 2026-10-20), equality
with the translated `create` (loops are `divergent`, not kernel-evaluable), an upstream change to
emit constants as literals (no longer needed).

## Plan

1. Owner decisions on the open decisions 1–3; `vartime_triple_scalar_mul_basepoint` (the
   `_128` table is certified; needs the NAF-digit lemma).
2. `montgomery.rs`: library support in `Curve25519/{X25519,Montgomery}.lean` (`x25519`, `xMul`,
   `ladder_eq_xMul`, `x25519_eq_u_nsmul`, `x25519_basepoint_edwards`, `edwardsToMontgomery`,
   `montgomeryTwist`) and `Defs/Montgomery.lean` (`MontgomeryPoint.u`, `ProjectivePoint.toXZ`,
   `Bounded`). `mul_clamped` is exactly RFC 7748 X25519 (byte-exact via `x25519`), `Mul` uses
   `scalar.asNat % 2^255` with no precondition, and the old project's Montgomery `mul_spec` was
   false (do not port it).
3. `ristretto.rs` (+ `elligator.rs`): library support in `Curve25519/Ristretto/*` (`Rel`,
   `rel_iff_formula` = meaning of `ct_eq`, `even_iff_isSquare`, `decodeRep`/`encodeRep`,
   `sqrtRatioM1` with the uniqueness lemmas to match `sqrt_ratio_i_spec` via
   `Proofs/Helpers/ToField.lean`'s `sqrtRatioM1_eq_of_spec`, `mapRep`, `fromUniformRep`). First
   move the private `conditional_negate_spec`, duplicated in `Proofs/Field/SqrtRatioI.lean` and
   `Proofs/Edwards/Decompress.lean`, to `Proofs/Helpers`.
4. Remaining files (`constants.rs` Ristretto constants; `lizard` is untranslated; …).
5. The u32 backend (below).
6. Improve the hidden construction of `Curve F` (quotient of Weierstrass models today) to the
   j-invariant / twist-datum description; nothing outside `EllipticCurve/Curve/*` and the
   `Proofs` modules changes.
7. Add std lib models to Aeneas.
8. One axiom per external crate (below).

### One axiom per external crate

Today `Subtle/Basic.lean` and `Zeroize/Basic.lean` state one `@[step]` spec axiom per function,
so the guard lists name each of them. Refactor each library to a single named axiom covering the
whole crate (e.g. `subtle_spec`, a conjunction of all its function specs, and `zeroize_spec`
likewise), and derive the per-function `@[step]` specs from it as theorems. A guard list then
names at most one axiom per external crate. The `#guard_msgs` lists of the spec summaries change
accordingly.

### u32 backend

`OnX86_64` stands in for the 32-bit branches of every `get_target` dispatcher. Specifying and
proving `src/backend/serial/u32/scalar.rs` (`Scalar29`), its constants, and the `i686` variants of
the `scalar.rs` functions lets the hypothesis be dropped from the `scalar.rs` statements (a change
of frozen statements: sign-off needed), and allows `Scalar29::pack`, `Scalar29::invert` and
`Scalar29::montgomery_invert` to be specified.

### Primality certificates

`Curve25519/Prime.lean` proves `p` and `L` prime with Lucas certificates (Pratt trees, 22
certificates) using only Mathlib. Replace them by the much shorter Pocklington certificates of
`PrimeCert` (https://github.com/b-mehta/PrimeCert) once it builds with our toolchain: as of
2026-10-14 its newest release (v4.33.0) fails against the Mathlib that Aeneas pins for Lean
v4.35.0-rc4 (`PrimeCert/PowMod.lean`, `PrimeCert/ForMathlib.lean`). Add it to `lakefile.toml`
after Aeneas, and check that `lake update` does not move Mathlib to PrimeCert's pin (adding the
manifest entry by hand avoids that). Certificates for both numbers are in the old project
(`curve25519-dalek-lean-verify/Curve25519Dalek/Math/PrimeCerts.lean`).

# Part III: Upstream issues and tooling

## Target names (unquoted names blocked)

The four translation targets are named `x86_64-tables`, `x86_64-no-tables`, `i686-tables`,
`i686-no-tables` (JSON target specs in `scripts/aeneas-translate.sh`). Names that are valid Lean
identifiers (`x86_64`, `x86_64_no_tables`, …), which would avoid the `«…»` quoting, make the
translation fail: Aeneas names a trait impl after the last path component of the implementing
type, which for per-target types is the target name, so e.g. `Mul<&Scalar>` for
`&EdwardsBasepointTable.x86_64` and for `&EdwardsBasepointTableRadix32.x86_64` both become
`SharedAx86_64.Insts.CoreOpsArithMulSharedBScalarx86_64` (324 clashes). With a hyphenated target
name Aeneas includes the type name, so the clash does not arise. Fix upstream: build impl names
from the type name plus the target component.

## Project-defined traits for external-crate libraries

Aeneas generates every external trait used by the crate (`subtle::ConditionallySelectable`,
`zeroize::Zeroize`, ...) into `Curve25519Dalek/Types.lean`, in namespace `Curve25519Dalek`. Only
traits in Aeneas's built-in table are skipped, and that table is compiled into the `aeneas` binary
from Aeneas's own Lean library (the `@[rust_trait "..."]` attribute); there is no option to add a
project's own declarations. So `Subtle` (its 5 trait-generic functions) and `Zeroize` (all of it)
depend on the generated types and are specific to this translation.

- Add upstream: let a project register its own `rust_trait` declarations as built-ins, so the
  trait structures can live in `Subtle`/`Zeroize` themselves and those libraries become
  independent of the curve25519-dalek translation.
- Until then, leave `Subtle` and `Zeroize` as they are. Afterwards: move the trait structures
  into the libraries, and drop their `Curve25519Dalek.Types` imports.

## `native_decide` from Aeneas's `toStr`

Aeneas's `toStr` discharges its length bound with `decide +native` (marked TODO in
`Aeneas/Std/String.lean`: the kernel cannot reduce `String.toByteArray` of a literal). Every
string literal in the generated dispatchers, and in `OnX86_64`, therefore adds
`…_native.decide.ax_*` axioms to the statements of `scalar.rs`. Ask upstream for a kernel-checked
bound (or a `Str` literal that carries none).

## Tooling

- **Prebuilt Aeneas oleans after a version bump.** Lake downloads the Aeneas release's build
  archive only when `.lake/packages/aeneas/backends/lean/.lake/build` does not exist, so after
  `lake update aeneas` it compiles Aeneas from source. Make `scripts/aeneas-install.sh` delete
  `.lake/packages/aeneas/backends/lean/.lake` (or run `lake build aeneas:release`).
- **Large exponents in the kernel.** Lean v4.35 refuses to evaluate `Nat.pow` with an exponent that
  does not fit in 32 bits (`invert_spec` hit this with `0 ^ ((2^250-1)*2^5+11)`). `generalize` does
  not hide such a term from the kernel; `obtain ⟨N, hN⟩ : ∃ N, … = N + 1` or an `irreducible_def`
  does. If it recurs, name the field exponents of `invert` and `pow_p58` with `irreducible_def`.
- **Public imports.** `lake shake` misses `open`-only namespaces and `step` specs, so some files
  keep public imports they may not need; trim them by hand when touching a file.

## Performance findings (2026-10-10)

- Slowest proof files: long straight-line functions (`to_bytes`, `mul`, `montgomery_reduce`),
  8–13 s each. The remaining cost is Aeneas's `step*` itself: before every step it tries all
  hypotheses as specs (quadratic in the context size), it ends with a failing `grind` attempt
  (0.5–1 s), and it repeatedly searches for `Lean.Grind.NoNatZeroDivisors (BitVec n)`. Worth
  reporting upstream to Aeneas. Long `step*` chains are therefore slow; split them
  (`#decompose`, helper lemmas).
- Interpreted vs native tactics: `step`, `step*`, `scalar_tac` (library `Aeneas`) and Mathlib's
  tactic code run interpreted; `AeneasMeta` ships a native plugin, loaded by `lake build`.
  Making everything native (hand-linked shared library, since `precompileModules` fails on a
  `Batteries` ↔ `BatteriesRecycling` import cycle) saved only 2–5% wall time on the slowest
  files. Not worth pursuing; the lever is `step*`'s algorithm.

## Performance measurement tooling

Locally we only need approximate data, and nothing that needs privileges (no `perf`, no sudo).

**Approaches, by granularity:**
- **Whole build:** `lakeprof` (https://github.com/Kha/lakeprof, installed via `uv tool` at
  `~/.local/bin/lakeprof`): `lakeprof record -- lake build …` timestamps Lake's output;
  `lakeprof report` gives per-module times (from Lake's "Built X (n s)" lines), the critical
  path (`-p`), the rebuild critical path (`-r`), simulated times by processor count (`-s`) and a
  chrome trace (`-c`); `lakeprof diff BASE CURR` compares two logs. Only rebuilt modules appear:
  force the same rebuild set in both runs (e.g. `touch` the files).
- **Per module, real build setup:** the trick used by the org's radar benchmarks
  (https://github.com/Beneficial-AI-Foundation/lean-bench-scripts, `scripts/bench/build/`):
  `LAKE_OVERRIDE_LEAN=true LEAN=<wrapper> lake build …` makes Lake call `<wrapper>` instead of
  `lean` for every module (with the usual `--setup <json>`, so plugins such as `AeneasMeta`
  load). The wrapper answers `--print-prefix`/`--githash` by delegating, then runs the real
  `lean --profile -Dprofiler.threshold=9999999 <args>` and parses the cumulative profiler lines
  (`\t<category> <n>(m)s`: `simp`, `grind`, `typeclass inference`, `interpretation`, …).
  Their wrapper measures with `perf stat` (instructions); a local variant can use
  `/usr/bin/time -f "%e %M"` instead (wall time, peak memory per module), no privileges needed.
- **Per file, quick:** `/usr/bin/time -f "%e %M" lake env lean <file>`. Caveat: `lake env lean`
  does not load the `AeneasMeta` native plugin that `lake build` loads, so `step*`-heavy files
  come out 1–2 s slower. Compare timings only under one setup.
- **Per proof / per tactic:** `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=N
  <file>` (per declaration with `N` ≈ 300; nested per tactic and `step*` phase with `N` = 1,
  aggregating self time per trace node); the cumulative breakdown with `-Dprofiler=true`. The
  lean-lsp MCP's `lean_profile_proof` does the same for one theorem (copies it into a temporary
  file; may fail for proofs relying on private helpers or local `#decompose` definitions). Full
  tracing adds overhead and can push heavy proofs over their heartbeats.

**Radar** (https://github.com/leanprover/radar) runs those scripts per repository and keeps the
history; its numbers (instructions, profile categories summed over modules, build-wide `maxrss`
of the largest process, lakeprof critical paths, `.lean`/`.olean` sizes) are the long-term record
if this repository is added there. Memory per module is not among them.

**Radar API** (tested 2026-10-10 on the org instance https://radar.18.118.100.156.nip.io, repo
`curve25519-dalek-lean-verify`; no login needed for reads). JSON under `<host>/api`:
`/repos/` (tracked repos), `/repos/{repo}/metrics/` (metric names and units),
`/repos/{repo}/graph/?n=<commits>&m=<metric>&m=…` (commits oldest first, and per metric one value
per commit, `null` if not benchmarked), `/repos/{repo}/history/`, `/commits/{repo}/{hash}/`,
`/commits/{repo}/{hash}/runs/{run}/` (logs), `/compare/{repo}/{a}/{b}/`. To download everything:
list the metrics, then query `graph` with `n=100000` in batches of about 50 metrics (400 names
per request gives HTTP 414, URI too long). For that repo: 801 metrics, 331 commits, 23
benchmarked; 17 requests, ~14 s, ~2 MB JSON. (`/api/metrics.prom` is only server health.)

**Memory safety when measuring:** limit parallelism (`LEAN_NUM_THREADS`, see "Building
locally") or measure files one at a time, and run nothing else meanwhile.

# Contributors to the earlier project (future co-authors)

Many proofs here are adapted from https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify. Its contributors, to be credited as
co-authors of this work:

- `oliver-butterley`
- `MarkusFerdinandDablander`
- `truonghoangle`
- `Zhang-Liao`
- `a-dangelo`
- `astefano`
- `TheodoreEhrenborg`
- `mpenciak`
- `jinxinglim`
- `alok`
- `faenuccio`
- `Kukovec`
- `rozbb`
- `semaraugusto`
- `ChristianoBraga`
