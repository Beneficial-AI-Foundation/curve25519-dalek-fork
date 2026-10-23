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

- **Updating Aeneas:** set `rev` in `lakefile.toml` to the new release tag; delete
  `.lake/packages/aeneas/backends/lean/.lake`; `lake update aeneas` (check that Mathlib moves only
  to Aeneas's pin); `lake build aeneas:release`; `./scripts/aeneas-install.sh` (copies Aeneas's
  `lean-toolchain`); `./scripts/aeneas-translate.sh`; compare the `*External_Template.lean` files
  with the External files; then the full strict build, `scripts/fill-guards.py` on every spec
  summary, the linters and `typos`. Last done 2026-10-22 (nightly-2026.10.13 → nightly-2026.10.22,
  Lean v4.35.0-rc4 → v4.35.0): `get_target` returns a `String` (`OnX86_64`, `dispatch_spec`), the
  `Vec` models moved to `Aeneas.Std.Alloc`, integer comparisons are `Bool` functions under
  `liftFun2` (four iterator proofs), type parameters are `Type _` (the External files keep
  `Type`, which still elaborates).

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
  replace it), so that they add no axiom. Their behaviour is then given by one predicate
  `<function>.Contract : Prop` each and one axiom per crate (`RustAx.core`, `RustAx.alloc`, in
  `FunsExternal.lean`) stating all of them, the only trusted additions; the theorems
  `<function>_spec` are projections, so `#print axioms` names the crate axioms.

## Libraries

| lean_lib | Namespace | Content | Audited |
|---|---|---|---|
| `EllipticCurve` | top level (`Curve`, `MontgomeryModel`, …) | Elliptic-curve models over a field, independent of any curve; Mathlib-bound | yes, except `EllipticCurve/Proofs/**` and `Curve/Impl.lean` |
| `Curve25519` | `curve25519` | Curve25519 in general (`p`, `L`, `a`, `d`, `A`, its models and facts), independent of dalek | yes |
| `Curve25519Dalek` | `Curve25519Dalek` | Generated translation + hand-written External files | External files |
| `Subtle`, `Zeroize` | as generated | Models of external crates; at the repository root (`Subtle.lean` + `Subtle/`, `Zeroize.lean` + `Zeroize/`) | `Subtle/Types.lean`, `Basic.lean` |
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
- **Trusted part:** `<Lib>/Types.lean` (types only) and `<Lib>/Basic.lean`. Basic holds `opaque` signatures with the template names, one predicate `<function>.Contract : Prop` per function (its contract, conditional on any trait-instance behaviour it relies on), a structure `<crate>.Contract` with one field per predicate, and the single axiom `RustAx.<crate> : <crate>.Contract`. The `@[step]` theorems `<function>_spec` are its projections, so a guard list names at most `RustAx.subtle` and `RustAx.zeroize`. (`Contract`, not `Spec`: Mathlib's `Spec` is the spectrum of a ring.) Verbatim bodies appear only where `impl_def` must unfold them (`@[trait_default]`).
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
  - `RustAx.subtle`/`RustAx.zeroize` (the one axiom of each external crate) or std externals
    (`FunsExternal.lean`) that the proof uses.
  - For dispatched functions: `get_target` (the dispatchers compare it with string literals).
  - `core.fmt.Formatter`, a type Aeneas declares as an axiom, where a proof goes through the
    translation of a panic message.
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
  - argument names are the Rust identifiers with any leading underscores dropped (`self`, `rhs`
    for Rust's `_rhs`, `limbs`, …): in Lean a leading `_` means "unused". Where an argument then
    shadows the specified function (`index self index`), the function is written with its last
    namespace component (`CoreOpsIndexIndexUsizeU8.index`);
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
- **Point statements:** coordinate-level exact `@[step]` specs with `LimbsLt` hypotheses
  (`r.toCompleted = self.toProjective.double ∧ r.LimbsLt 54`), plus `_spec_point` corollaries
  (`r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.LimbsLt 52`); iterated operations (scalar
  multiplication) have point-level main specs, and the spec summaries use the point-level forms.
  Hypotheses `hself`, `hother`, `hon`/`hself_on`, `hscalar`; scalars unreduced (`s.asNat • P`,
  precondition `s.asNat < 2^255`).
- **Line length (all hand-written files):** no line over 100 characters; only the files Aeneas
  generates may have long lines. A long `namespace X.Y` is split into two consecutive `namespace`
  commands (closed by two `end`s); long strings use string gaps (`\` at the end of the line); a
  long qualified name is shortened with `open P in` before the declaration (two chained
  `open … in` when one is too long, `open P renaming f → g in` when the short name would be
  shadowed). Only a single name component too long for any line (with `namespace`, `open` or
  `end` in front) justifies switching the linter off, for that one line
  (`set_option linter.style.longLine false` / `… true` around it); 9 such lines remain (2026-10-22).
- **Limb bounds:** `FieldElement51.LimbsLt n a` and `Scalar52.LimbsLt n a` ("every limb
  `< 2^n`", an `abbrev` so that `step`, `scalar_tac` and `agrind` see the `∀ i < 5` form; write
  `FieldElement51.LimbsLt k a` (or `Scalar52.…`) when `a` is typed `Array U64 5#usize`, and
  `unfold` it before `rw [Nat.forall_lt_five]`), and every point structure and table has
  `LimbsLt (n : ℕ) (self) : Prop` (the conjunction over its coordinates; tables: over every
  entry), stated with the bound: `r.LimbsLt 52` for `EdwardsPoint`, `AffinePoint` and the
  projective points, `r.LimbsLt 54` for `CompletedPoint` and
  the Niels forms and their tables. Names of `Prop`s follow Mathlib: `Is` + adjective (`IsValid`),
  no `Is` for relations and point conditions (`Represents`, `ProjEq`, `OnCurve`, like Mathlib's
  `Equation`/`Nonsingular`).
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
- **Pitfalls:** destructure a `LimbsLt` hypothesis only after the `step` whose callee needs it;
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
- `src/scalar.rs`: all public items specified and proved for all four targets (2026-10-23: the
  i686 variants added and `OnX86_64` dropped from the statements, signed off by the owner); spec
  summary `Specs/Scalar.lean`. Dispatchers via `dispatch_all_spec` (`Proofs/Helpers/Target.lean`),
  which uses the Aeneas axiom `get_target.spec` (now in the axiom lists). `Scalar29::pack`,
  `invert`, `montgomery_invert` in `Proofs/Scalar/Scalar29*.lean`.
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
  `LimbsLt`, `toPoint`), byte encodings, the lenient decoder `decodeLenient`, table predicates.
- `Proofs/Helpers/{ToField, Coords, Edwards, EdwardsMontgomery, Window, Naf, BasepointTable,
  Iterator, Vec, Collect, Cmp}.lean`: bridges from the field specs (`asNat % p`) to `toField`, and
  shared lemmas.
- `backend/serial/curve_models.rs`: all items (`Proofs/Backend/Serial/CurveModels/`; no
  summary, the module is not public).
- `window.rs`: all `select`/`From` items (`Proofs/Window/`; no summary, `pub(crate)`).
- `scalar_mul/*` and `backend/mod.rs` dispatchers: variable base, vartime double base, Straus,
  Pippenger, precomputed Straus.
- `edwards.rs`, `edwards/affine.rs`: complete, both x86_64 variants (`Proofs/Edwards/`, summary
  `Specs/Edwards.lean`, 156 statements). `vartime_triple_scalar_mul_basepoint` (2026-10-21) rests on
  `naf5_digits_eq_zero_of_lt` (`Proofs/Helpers/Naf.lean`: a width-5 NAF of `x < 2^n` has no digit
  above index `n`), reverse iteration over `RangeInclusive` (`Proofs/Helpers/Iterator.lean`) and the
  certified constant `ED25519_BASEPOINT_128_POINT` (`TableCertificate.checkPoint`).
- `montgomery.rs` (2026-10-21): complete (`Proofs/Montgomery/`, summary `Specs/Montgomery.lean`,
  24 statements). `Mul`/`MulAssign` are `encodeU (ladder 255 (s.asNat % 2^255) u)` with no
  precondition; `mul_clamped`/`mul_base_clamped` are `x25519` byte for byte; `mul_base` needs
  `scalar.asNat < 2^255`; `mul_bits_be` is stated with the new `MontgomeryModel.ladderBits` (ladder
  over a bit list, most significant first) and `ladderBits_eq_xMul`
  (`EllipticCurve/Montgomery/XOnly/`); `to_edwards` is stated per variant with `decodeLenient`.
  The private `ProjectivePoint` and `differential_add_and_double` specs are in the proof files.
  Statements approved by the owner (2026-10-21).
- `ristretto.rs`, `ristretto/elligator.rs` (2026-10-22): complete, both x86_64 variants
  (`Proofs/Ristretto/`, summary `Specs/Ristretto.lean`, 101 statements; the Ristretto constants
  and `ED25519_BASEPOINT_TABLE` added to `Specs/Constants.lean`). Group operations are exact on
  representatives (as for `EdwardsPoint`); `ct_eq`/`eq` decide `edwards.Rel`; `compress` is
  `Ristretto.encodeRep` for any representative (`Proofs/Helpers/RistrettoCompress.lean`:
  `compressProj_eq_encodeRep`, the RFC formula on `(X : Y : Z : T)` changes by a sign under
  scaling); `decompress` is `decodeRep`; `double_and_compress_batch` encodes `2 P`
  (`doubleCompress_eq_encodeRep`: on the curve `h² - g² = (a - d) e²`, so the inverse square root
  is rational); `elligator_ristretto_flavor`/`map_to_curve` are `mapRep` exactly
  (`SQRT_AD_MINUS_ONE` is the RFC root, `SQRT_AD_MINUS_ONE_spec_eq`); `from_uniform_bytes` is
  `fromUniformRep`. New helpers: `conditional_negate_spec`
  (`Proofs/Backend/Serial/U64/Field/ConditionalNegate.lean`), `eq_ite_of_choice` (`ToField`),
  `index_rangeFull_spec` (`Array`), `asNat_append_eq` (`AsNat`), `collectApplyBody` with
  `collectApplyLoop_spec`/`collectApplyLoopP_spec` and `optionMap_id_spec` (`Collect`).
- `backend/serial/u32/field.rs` (2026-10-22): all items, ported from the proofs of András Némedy
  Varga (BAIF `curve25519-dalek-u32`, branch `nva/scratch`; his `Authors:` lines kept), in
  `Proofs/Backend/Serial/U32/Field/` (no summary, the module is not public). Value
  `Defs/FieldElement2625.lean`: `Array.asNat2625 a = ∑ a[i] · 2 ^ (i * 51 ⌈/⌉ 2)`, the formula of
  the Rust comment (on any ten limbs, since `reduce` takes `[u64; 10]`); forms of the sum in
  `Proofs/Helpers/FieldElement2625.lean` (`limbWeight`, `limbRadix`, `asNat2625_eq_sum`,
  `asNat2625_expand`). Bounds, uniform `LimbsLt n` where possible: outputs `LimbsLt 26`; inputs
  `add` 31, `sub`/`negate`/`neg` 28, `square`/`square2`/`pow2k` 27; `mul`/`mul_assign` take the
  explicit `< 3 * 2 ^ 26` (sums of three reduced elements, as in Edwards addition; `LimbsLt 28`
  overflows `19 * y[i]`, the Rust `b < 1.75`). `reduce` also states the parity bound
  `< 2 ^ (26 - i % 2) + (i % 2) · 2 ^ 18` used by `to_bytes`. Their 4 axioms are covered by our
  contracts. `zeroize` is in `Zeroize/Instances.lean`.
- `backend/serial/u32/scalar.rs` and its constants (2026-10-23): all items, in
  `Proofs/Backend/Serial/U32/{Scalar,Constants}/`, statements as for u64 (`Defs/Scalar29.lean`:
  `asNat`, `LimbsLt`, `montgomeryRadix = 2 ^ 261`). Mostly converted from the u64 proofs; the
  Karatsuba `mul_internal` and `square_internal` follow the BAIF proofs. Long functions are
  decomposed (`mul_internal` 5 blocks, `montgomery_reduce` 17 rows, `from_bytes_wide` 2 halves).
- `traits.rs`: generic `is_identity` (`Proofs/Traits/IsIdentity.lean`, `Specs/Traits.lean`).
- Point constants: `ED25519_BASEPOINT_POINT`, `EIGHT_TORSION`, `BASEPOINT_ORDER`,
  `ED25519_BASEPOINT_COMPRESSED`, `X25519_BASEPOINT` (`Specs/Constants.lean`).
- `X25519_LOW_ORDER_POINTS` (2026-10-22): `x25519 k P.asNat = 0` for each of the seven points and
  every `k` (`Proofs/Constants/X25519LowOrderPoints.lean`): a kernel check that the 4-bit ladder on
  `8` ends at infinity, `xMul_mul` (`EllipticCurve/Montgomery/XOnly/Lemmas.lean`) and
  `x25519_eq_zero_of_xMul_eight` (`Curve25519/X25519.lean`, clamped scalars are multiples of `8`).
  With it every public item of the crate outside `lizard` and the u32 backend is specified.
- Precomputed tables (2026-10-21): `ED25519_BASEPOINT_TABLE`, `AFFINE_ODD_MULTIPLES_OF_BASEPOINT`
  and `AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128` are certified unconditionally
  (`Proofs/Backend/Serial/U64/Constants/{Ed25519BasepointTable, AffineOddMultiplesOfBasepoint,
  AffineOddMultiplesOfBasepoint128}.lean` on `Proofs/Helpers/TableCertificate.lean`; standard
  axioms only, 3–6 s per file including imports, < 2 GB). `mul_base`, `mul_base_clamped` and
  `vartime_double_scalar_mul_basepoint` of `x86_64-tables` are therefore unconditional and in
  `Specs/Edwards.lean`.
- All x86_64 items are stated for both `«x86_64-tables»` and `«x86_64-no-tables»`; the i686
  variants outside `scalar.rs` wait for the rest of the u32 backend.

## Decisions taken

- `core.result.Result.map_spec` (used by `CompressedEdwardsY::from_slice`) stays a spec axiom in
  `FunsExternal.lean`, consistent with `core.array.from_fn_spec` (2026-10-20).
- `IsIdentity::is_identity` (blanket impl in `traits.rs`, used by `EdwardsPoint`,
  `CompressedEdwardsY`, `MontgomeryPoint`, `RistrettoPoint`, `CompressedRistretto`) is summarised
  once, generically, in `Specs/Traits.lean`, conditional on the type's `ct_eq`/`identity`
  behaviour; the per-type summaries do not repeat it (2026-10-20).
- Spec summaries cover the crate's public API only; the coverage is checked by review, not by a
  committed script or CI step.
- Limb bounds as `LimbsLt n` (2026-10-21), replacing the per-type `Bounded`, down to the field
  elements (`FieldElement51.LimbsLt`, 227 field-level bounds converted; the only raw form left is
  `reduce`'s `< 2^51 + 2^18`), and the scalar limbs (`Scalar52.LimbsLt`, 76 bounds; the 9-limb
  wide products stay raw).
- One axiom per external crate (2026-10-21): `RustAx.subtle`, `RustAx.zeroize`,
  `RustAx.core` and `RustAx.alloc` state all the per-function predicates; the per-function `@[step]` theorems are
  projections. Guard lists name only these (plus `get_target` and `core.fmt.Formatter`).
- Axiom names (2026-10-22): `RustAx.<crate>` (`RustAx.core`, `RustAx.alloc`, `RustAx.subtle`,
  `RustAx.zeroize`): the crate name verbatim, Rust named, one prefix to grep for every trusted
  assumption beyond Lean's; the structures stay `<crate>.Contract` next to their functions.
- `Vec::is_empty` has a contract (`alloc.vec.Vec.is_empty.Contract`: `b = decide (v.length = 0)`, no
  precondition), decided 2026-10-21, like the other std opaques.

- `lizard` (2026-10-22): not translated for now (behind the `lizard` Cargo feature, which pulls in
  `digest`); may be added later.
- `Subtle` and `Zeroize` (2026-10-22): separate `lean_lib`s in folders at the repository root.
- Long lines (2026-10-22): none in hand-written files (see "Line length").

## Open decisions (for the owner) and known gaps

1. **`core.fmt.Formatter` in guard lists:** Aeneas declares this type as an axiom
   (`Aeneas/Std/Core/Fmt.lean`). The one place it enters is the formatted panic message of
   `scalar::read_le_u64_into` (`assert!(…, "src.len() = {}, dst.len() = {}", …)`, translated with
   `Argument.new_display` on `usize`'s `Display`, whose `fmt` mentions `Formatter`); it reaches
   every spec whose proof goes through `as_radix_2w` (basepoint tables, `mul_base`,
   `mul_base_clamped`, Pippenger) or `non_adjacent_form`. It only asserts that some type exists;
   acceptable? (The `…_native.decide.ax_*` axioms of Aeneas's
   `toStr` are gone since Aeneas nightly-2026.10.22, which proves the bound with `decide +kernel`
   and no longer uses `toStr` in the dispatchers.)
2. **Iterator lengths:** the multiscalar and precomputation statements (and
   `double_and_compress_batch`) assume `length ≤ Usize.max` for the lists the iterators yield.
   The patched code collects each iterator into a `Vec` by `push`, and Aeneas's `Vec.push` fails
   (panics) once the length would exceed `Usize.max`, so without the hypothesis the statements are
   false for (unrealisable) longer inputs. Decided 2026-10-22: keep the hypothesis.
3. **New std contract `core.borrow.Borrow.Blanket.borrow`** (2026-10-22, in `RustAx.core`):
   `<T as Borrow<T>>::borrow` returns its argument. Needed by the Ristretto `multiscalar_mul` and
   `VartimeRistrettoPrecomputation::new`, which pass this instance to the Edwards functions;
   approved 2026-10-22 (field `borrow_blanket` of `core.Contract`, following the
   one-axiom-per-crate convention).
4. Minor: `PrecomputedStraus/OptionalMixedMultiscalarMul.lean` takes 18–23 s (split the two
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
  structure from the flat list **sequentially** (`entries`, `rows`: three or four limb arrays
  per entry, eight entries per row), so `c = ok (mk xs)` follows. Measured on the 768-bind
  table: well under a second (versus 47 s / 7.7 GB and a timeout for the old `simp [bind_ok]`
  route, and a reboot for an `Eq.trans` chain). A first version of `mk` indexed the list
  (`fes[24 i + 3 j]!` under `List.ofFn`): the kernel then walked O(N²) list cells, 8 s for this
  table; `bindList` via `brecOn` versus `List.rec` made no difference.
- **Content.** `Bool` checkers over the flat list, evaluated by `decide +kernel` after
  `rw [edwards_eq_numerals]`: `checkRow S Q l` (entries `Q, Q + S, Q + 2 S, …`, by running
  additions in extended coordinates and three cross-multiplication equalities per entry, so no
  inversion), `checkRowProj` (projective Niels entries), `checkTable P fes n` (rows
  `P, 2^8 P, …` by 8 doublings each). Soundness is proved once, generically
  (`checkRow_sound`, `checkTable_sound`); the big table's 256 entries check in ~2 s, the limb
  bounds in ~1 s. Rule for anything the kernel evaluates: walk lists linearly, never index them
  (indexing through `mk` in the bounds check alone cost 24 s / 4.9 GB).
  Negative controls (a corrupted limb, a duplicated row) fail as they should.

Rejected: per-entry `nsmul` certificates (30 s, 3.4 GB per file, measured 2026-10-20), equality
with the translated `create` (loops are `divergent`, not kernel-evaluable), an upstream change to
emit constants as literals (no longer needed).

## Plan

1. The u32 backend (below): `field.rs` and `scalar.rs` done (with the i686 `scalar.rs` variants);
   next the remaining files.
2. Improve the hidden construction of `Curve F` (quotient of Weierstrass models today) to the
   j-invariant / twist-datum description; nothing outside `EllipticCurve/Curve/*` and the
   `Proofs` modules changes.
3. Add std lib models to Aeneas.

### u32 backend

`OnX86_64` stands in for the 32-bit branches of the `get_target` dispatchers outside
`scalar.rs` (dropped there 2026-10-23). Each further file follows the same pattern: prove the i686
variants, switch the dispatcher to `dispatch_all_spec`, drop the hypothesis (sign-off needed).
The i686 table constants (`backend.serial.u32.constants.ED25519_BASEPOINT_TABLE`, the two
`AFFINE_ODD_MULTIPLES_OF_BASEPOINT` tables) are chains of `FieldElement2625.from_limbs` binds
over `Array U32 10`; `Proofs/Helpers/TableCertificate.lean` is written for `FieldElement51`
(`collect_limbs`, `bindList`, `limbsNat`, the `«x86_64-tables»` checkers), so parametrise it over
the limb type when the u32 `Defs` (`FieldElement2625.toField`) exist. Mechanical; the method and
costs carry over.

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

## Tooling

- **Prebuilt Aeneas oleans after a version bump.** Lake downloads the Aeneas release's build
  archive only when `.lake/packages/aeneas/backends/lean/.lake/build` does not exist, so after
  `lake update aeneas` it compiles Aeneas from source. Delete
  `.lake/packages/aeneas/backends/lean/.lake` before the update and run `lake build aeneas:release`
  after it (worked on 2026-10-22); `scripts/aeneas-install.sh` could do both.
- **Large exponents in the kernel.** Lean v4.35 refuses to evaluate `Nat.pow` with an exponent that
  does not fit in 32 bits (`invert_spec` hit this with `0 ^ ((2^250-1)*2^5+11)`). `generalize` does
  not hide such a term from the kernel; `obtain ⟨N, hN⟩ : ∃ N, … = N + 1` or an `irreducible_def`
  does. If it recurs, name the field exponents of `invert` and `pow_p58` with `irreducible_def`.
- **Public imports.** `lake shake` misses `open`-only namespaces and `step` specs, so some files
  keep public imports they may not need; trim them by hand when touching a file.

## Performance plan (2026-10-22)

Out of scope for now: Aeneas `step*` improvements (in the Aeneas pipeline), CI (separate later
work: caching Aeneas and `.lake/build`, parallel lint jobs), keeping it fast (Radar, budgets;
another occasion).

0. **Baseline.** Full rebuild of our modules under `lakeprof` (limited `LEAN_NUM_THREADS`, memory
   cap): per-module times, critical path. A `LEAN=` wrapper with `/usr/bin/time` for wall time
   and peak memory per module, and `--profile` categories. The fixed cost of an empty file
   importing `Curve25519Dalek.Funs` (64k lines, 16 MB olean, imported by 328 proof files). Keep
   the logs to compare with `lakeprof diff`. Old data (2026-10-21, old Aeneas, parallel load):
   `PrecomputedStraus/OptionalMixedMultiscalarMul` 62 s, `Pippenger/OptionalMultiscalarMul`
   43 s, U64 `Field/ToBytes` 30 s, `Straus/OptionalMultiscalarMul` 28 s, U64 `Scalar/ToBytes`
   24 s, `VartimeDoubleBase.Mul` 23 s, `VartimeTripleBase` 22 s, ~30 more at 8–21 s.
1. **Memory safety.** Start the lean-lsp MCP under `systemd-run -p MemoryMax=6G` (its workers
   otherwise live in VS Code's scope; OOM on 2026-10-22). List modules peaking above ~3 GB (from
   0) for step 3. Document a safe `LEAN_NUM_THREADS`/`-j` for 15 GB in "Building locally".
2. **Imports.** `Proofs` has 1082 `public import`s against 1222 plain ones. Demote every
   `public import` that no statement of the file needs (helpers and other proof files are proof
   dependencies), so that a change to a proof body does not rebuild downstream modules; drop
   unused imports. Tool: Lean's `shake` if it works here, else a demote-and-rebuild script.
   Measure the rebuild set after touching a helper, before and after.
3. **Heavy proofs** (worst first, by time and memory from 0). Split oversized declarations with
   `#decompose` or helper lemmas: U32 `ToBytes` (`calcCanonical_spec`, `toArray_spec`; removes
   both `maxHeartbeats 1000000`), both `ToBytes`, `Mul`, `MontgomeryReduce`, the scalar-mul
   loops. One file per `«x86_64-tables»`/`«x86_64-no-tables»` variant where both are in one file
   (`OptionalMixedMultiscalarMul` first), so they build in parallel. Keep `step*` contexts small;
   replace `step* N`/`‹_›` chains (ported `ToBytes`/`FromBytes`) by named steps. Avoid the
   `whnf` traps met in the u32 port: unifying literal `#usize` indices or long `set` chains with
   `exact`, unfolding hidden definitions; work at the list level (`Array.set_val_eq`,
   `Array.repeat_val`) instead.
4. **Build structure.** From the critical path (`lakeprof -p`), break long sequential chains
   (shared helpers, `Specs/*` importing all of `Proofs`).

**Baseline (2026-10-22)**, full rebuild of our libraries (`LEAN_NUM_THREADS=4`, 4 cores, Lean
v4.35.0, Aeneas nightly-2026.10.22). Tooling in `.scratch/perf/`: `sysroot/` is a copy of the
toolchain (symlinks) whose `bin/lean` logs wall time and peak RSS per module (Lake only reads
the prefix from `LEAN`, then calls `<prefix>/bin/lean`, so a plain `LEAN=` wrapper is not
enough; `/usr/bin/time` is not installed). Run: `PERF_LOG=… LAKE_OVERRIDE_LEAN=true
LEAN=.scratch/perf/sysroot/bin/lean lakeprof record -o … -- lake build` (lakeprof report from the
repository root).
- 432 modules, 4059 s of work, 1093 s wall; simulated: 2 cores 2032 s, 8 cores 670 s, 16 cores
  506 s, critical path 468 s (`Funs` 214 s → U32 `Reduce` 74 s → U32 `ToBytes` 158 s). With few
  cores the total work, not the critical path, decides the wall time.
- Fixed cost per module (loading imports, mostly Aeneas and its Mathlib part; `Funs` adds
  ~0.3 s): ~2.2 s, i.e. ~1000 s of the 4059 s. Median module 4.3 s; 71 modules ≥ 10 s.
- Memory: every module ≤ 1.8 GB except `Funs` (5.2 GB). The OOM of 2026-10-22 came from the
  uncapped language-server workers, not from builds.
- Slowest: `Funs` 214, U32 `ToBytes` 158, `PrecomputedStraus/OptionalMixedMultiscalarMul` 136,
  `Pippenger/OptionalMultiscalarMul` 109, `Ristretto/DoubleAndCompressBatch` 85, U32 `Reduce` 75,
  U32 `FromBytes` 70, U32 `Mul` 67, `Ristretto/Elligator` 63, `Straus/OptionalMultiscalarMul` 56,
  U64 `Field/ToBytes` 50, `VartimeDoubleBase/Mul` 49, U32 `SquareInner` 47,
  `MontgomeryReduce` 45, `Ristretto/Compress` 43 (seconds).

**Imports (step 2) findings.** Lake's early cutoff works: a comment-only change to
`Proofs/Helpers/ToField.lean` rebuilds that module only. Adding a lemma (interface change)
rebuilt 49 modules = the module + its 48 direct importers: no transitive spread through
`public import`, so demoting public imports does not shrink such cascades. `lake shake` is not
usable here: it drops imports needed only inside proofs or for `open` (e.g. `Proofs.Helpers.Array`
for `Array.set_getElem_five`, `Curve25519.Basic` for `open curve25519`) and adds unrelated
Mathlib modules (`Nat.Totient`, `Rat.Floor`, …); its changes were reverted. Remaining value is
small: drop genuinely unused imports by hand when touching a file, and fix the structural edges
`EllipticCurve/*/Defs` → `*/Lemmas` (Defs should import Defs only).

**Heavy proofs (step 3) findings.** Standalone `lake env lean` times (all cores) per declaration
via `-Dtrace.profiler=true -Dtrace.profiler.threshold=1000`, list in `.scratch/perf/top-decls.txt`.
- The cost of a `step` grows with the context along a long chain (0.3 s → 1.4 s per step in
  `elligator_ristretto_flavor_spec`), and the final `scalar_tac`s in a big context cost ~2.6 s
  each. Moving a long straight-line chain out of a loop proof into its own lemma with a small
  context (`#decompose … afterLets (branch 0 (letRange a n)) => helper`, `afterLets` skips the
  leading pure `let`s, `dsimp only` before `rw [body_eq]` under the loop's `match`) halved
  `DoubleAndCompressBatch.loop1_spec` (21.7 s → 8.2 + 2.1 s per variant; file 24 s → 11 s).
- U32 `ToBytes`: `calcCanonical` split into `roundsLow`/`roundsHigh` (rounds 0–4, 5–8; interface
  the predicate `RoundInv`), `toArray` into `packLow`/`packHigh` (bytes 0–15, 16–31). Module
  74 s → 36 s (`lake build`, all cores), proof time ~87 s → 54 s, longest declaration
  44 s → 11 s; both `maxHeartbeats 1000000` removed. (`lake env lean` cannot check this file: the
  `#decompose` of `to_bytes` hits `maxRecDepth` without the native `AeneasMeta` plugin, so
  profile it inside `lake build` with `set_option trace.profiler true` at the top.)
- Generated `#decompose` definitions need `add_decl_doc` (docBlame linter).
- Next candidates: U64 `ToBytes.pack_spec` (`step*` 15 s over 32 byte writes whose boundaries
  do not match the 51-bit limbs: needs a prefix-sum invariant as in U32 `toArray`),
  `Elligator` (2 × ~20 s, one long chain), U32 `Reduce` (`carry_spec` 12 s), U32 `FromBytes`
  (`from_bytes_spec` 14 s, `load4_at_spec` 11.5 s), Pippenger `loop1_loop1` (2 × ~9 s).
- Not effective: `step*` options (`-grind`, `-grind +scalarTac`, `-threadGrindState`: slower or
  failing on `pack_spec`); clearing the `% p` equations after each step (−14% only).
- Cheap local waste: `simp (disch := scalar_tac)` with many discharges in a big context (3.9 s in
  `load4_at_spec`); prefer explicit bounds or `omega`.
- Two x86_64 variants are proved twice (same proof text): everything costs double.


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
