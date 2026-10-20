# Guidelines

How the Lean verification of curve25519-dalek is arranged. The plan and the open to-dos are in
`notes.md`.

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
| `EllipticCurve` | top level (`Curve`, `MontgomeryModel`, …) | Elliptic-curve models over a field, independent of any curve; Mathlib-bound. API in `curve-api.md` | yes, except `EllipticCurve/Proofs/**` and `Curve/Impl.lean` |
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

The API, the terminology (curve / model / coordinates) and all design decisions are in
`curve-api.md`; follow it. Conventions specific to these two libraries:

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
    that each literal's byte length fits a `u32` (see `notes.md`).
  - Update the list when a proof lands.
  - `#print axioms` prints an axiom by its shortest name that resolves in the spec summary, so
    the module declaring it must be visible there. A proof file importing it privately is not
    enough: the spec summary then imports it itself.
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
- **No auto-generated names.** Never refer to names a tactic invented (`h_1`, `x✝`, `a_post1`,
  `i1`). Name what you use (`step as ⟨r, hr⟩`, `obtain ⟨…⟩`, `intro`).
- **The curve constants cannot be unfolded.** `p`, `L`, `a`, `d`, `A` and `sqrtM1` are hidden
  definitions. Use their characterisation lemmas in `Curve25519/Basic.lean` (`p_eq_numeral`,
  `L_eq_numeral` give them as numerals; add new lemmas there).
- **No** `sorry`, `native_decide` or `admit`. `bv_decide` is allowed; its certificate axioms then
  appear in the spec summary's axiom list.
- **Tactics Aeneas's `aeneas-lean-core` guidance bans** (`omega`, `linarith`, `nlinarith`,
  `congr N`, …) are banned only in proofs about the generated code: spec theorems, loop specs and
  their helpers, where the goals involve Aeneas scalars and containers. In pure mathematical
  lemmas (e.g. about `Nat`, `ZMod p`, `Nat.ofDigits`), use whichever tactic is right, including
  these.
- **Statements are frozen.** A proof file never changes the statement text of its theorem.

## Workflow per Rust file

1. **Inventory:** list the Rust items and their Lean names (`Funs.lean` doc comments).
2. **Statements:** write the `Defs` additions, the proof files (theorems proved by `sorry`) and the spec summary. Fill the `#guard_msgs` lines with `scripts/fill-guards.py` (usage in its docstring).
3. **Review gate:** the owner reviews the spec summary and `Defs`. Statements are then frozen; any change needs sign-off.
4. **Proofs:** fill in the proofs following "Proof quality" (and the Aeneas `aeneas-lean-core`
   workflow), and update the `#guard_msgs` lines as they land.
5. **Done:** no `sorryAx` left in the spec summary. Only then does the work go to `main`: CI
   rejects any `sorry`, so steps 2–4 happen on a branch.

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

## CI

- **`lean-translation.yml`:** the translation is current.
- **`lean-build.yml`:**
  - `lake build --wfail` on every default target: any warning, including `sorry`, fails the build;
  - `runLinter` on `Subtle`, `Zeroize`, `EllipticCurve`, `Curve25519`, `Defs`, `Specs` and
    `Proofs`, one step each
    (`runLinter` stops at the first failing module).
