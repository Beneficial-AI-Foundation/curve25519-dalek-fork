# Guidelines

How the Lean verification of curve25519-dalek is arranged. The plan and the open to-dos are in
`notes.md`.

## Translation

```
./scripts/aeneas-install.sh     # charon + aeneas for the release pinned in lakefile.toml
./scripts/aeneas-translate.sh   # apply translation-patches/, run charon + aeneas, revert patches
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
  - **Applying:** patches are applied one by one and reverted in reverse order, so each must apply on its own. If two patches touch neighbouring functions, trim the context at the boundary.
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
| `Curve25519` | `curve25519` | Curve25519 in general (`p`, `L`, `a`, `d`, `A`, later the curve models), independent of dalek | yes |
| `Curve25519Dalek` | `Curve25519Dalek` | Generated translation + hand-written External files | External files |
| `Subtle`, `Zeroize` | as generated | Models of external crates | `Types.lean`, `Basic.lean` |
| `Specs` | `Curve25519Dalek` | Spec definitions, audit files (one per Rust file), proofs | `Defs.lean`, audit files |

All hand-written files use the Lean module system: `module`, `public import`, and
`@[expose] public section` for definitions that proofs must unfold.

**Licence and copyright headers:** the Lean development is Apache 2.0
(`curve25519-dalek/lean/LICENSE`); the Rust crate stays BSD-3-Clause. Every hand-written Lean
file starts with the header below, then `module`. A file ported from the previous project
(curve25519-dalek-lean-verify) keeps that file's header (year and authors) verbatim; a merged file
lists the union of its sources' authors; a new file has no `Authors:` line. Root aggregation
files (`Specs.lean`, `Subtle.lean`, …) and the Aeneas-generated files have no header, as in
Mathlib. (Mathlib's header linter is disabled in `lakefile.toml`: it never runs with our `srcDir`.)
```
/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
```

**External-crate libraries (`Subtle`, `Zeroize`):**
- **Trusted part:** `<Lib>/Types.lean` (types only) and `<Lib>/Basic.lean`. Basic holds `opaque` signatures with the template names, plus one `@[step]` spec axiom per function. Each spec axiom is conditional on any trait-instance behaviour it relies on. Verbatim bodies appear only where `impl_def` must unfold them (`@[trait_default]`).
- **Derived part:** `<Lib>/Lemmas.lean` (generic) and `<Lib>/Instances.lean` (about instances in `Funs.lean`). They add no axioms.
- **Imports:** `FunsExternal.lean` imports only `<Lib>.Basic`.

## Specs: layout

The `Specs` tree mirrors the Rust tree under `curve25519-dalek/src/`, with UpperCamelCase module
names:

```
Specs/Defs.lean                              spec definitions used crate-wide (audited)
Specs/Backend/Serial/U64/Defs.lean           spec definitions for this directory (audited)
Specs/Backend/Serial/U64/Field.lean          AUDIT FILE for src/backend/serial/u64/field.rs
Specs/Backend/Serial/U64/Field/Reduce.lean   proof of fn `reduce`
Specs/Backend/Serial/U64/Field/Lemmas.lean   lemmas shared by several proof files of field.rs
Specs/Lemmas/AsNat.lean                      lemmas shared crate-wide (here: about `Array.asNat`)
```

- **Per Rust file:** one audit file `<File>.lean` and a folder `<File>/` with one proof file per Rust item.
- **File naming:** a file named after a function means that function is in that Rust file. Two items with the same name are distinguished by a detail (`Mul.lean` / `MulAssign.lean`).
- **What goes in a function's file:** its loops and loop bodies, inner `fn`s, local consts and closure helpers.
- **Other files:** `Defs.lean` (definitions used in statements, audited) and `Lemmas.lean` or
  `Lemmas/<Topic>.lean` (shared proof lemmas, not audited). No other names. (`Aux` is a reserved
  file name on Windows, which Lean rejects.)
- **Imports:**
  - audit file → its folder's proof files;
  - proof file → callees' proof files, `Defs`, `Curve25519`, external libraries.

  Proof files never import audit files.
- **`Specs.lean`** imports every audit file.

## Specs: audit file format

- **Proof file:** holds the canonical `@[step]` theorem, used by `step`.
- **Audit file:** repeats the statement verbatim as `<name>'`, proved by that theorem, followed by its axioms:

```lean
/-- `square`: `r = self²` mod `p`; limbs `< 2^54` in, `< 2^52` out. -/
theorem square_spec' (self : FieldElement51) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    square self ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ 2 % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  square_spec self hself

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms square_spec'
```

  The axiom list is matched as a substring, with whitespace collapsed (Lean wraps the list when the
  name is long). A list over 100 characters is wrapped at the commas.

- **Order:** the statements appear in the order of the items in the Rust file.
- **Same statement:** the proof term type-checks only if both statements agree, up to definitional equality.
- **Pinned axioms:** `#guard_msgs` fixes the axioms each statement rests on.
  - `sorryAx` while the proof is pending.
  - Any `Subtle`/`Zeroize` spec axioms or std externals (`FunsExternal.lean`) that the proof uses.
  - Update the list when a proof lands.
- **Not `@[step]`:** the primed theorems don't carry the attribute.
- **Auditing:** an auditor reads `Curve25519/**`, `Specs/**/Defs.lean` and the audit files. Nothing else.

## Specs: statement conventions

- **Coverage:** one statement per Rust item (function, trait method, inner `fn`, const). Not
  covered: closure `call_mut`/`call_once` wrappers, derived `Clone`/`Copy`, `Debug`, and local consts
  inside a function body. Their helper specs may exist in proof files.
- **Names:**
  - theorems are `<function>_spec`, in the function's namespace;
  - argument names are exactly the identifiers of the specified Lean/Rust function (`self`, `_rhs`, `limbs`, …);
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
  `private`. A lemma with wider use moves to a central `Lemmas` file: the Rust folder's
  `Lemmas.lean` / `Lemmas/<Topic>.lean`, or `Specs/Lemmas/<Topic>.lean` if it is not specific to
  that folder; facts about curve25519 constants go in `Curve25519/Basic.lean`. Shared lemmas are
  stated in their natural generality (e.g. for any radix or array length, not just the instance at
  hand).
- **Large powers (`exponent … exceeds the threshold 256`).** Lean core declines to evaluate
  `b ^ n` when the exponent `n` exceeds `exponentiation.threshold` (256) and warns, whenever
  unification, `simp` or `omega`/`scalar_tac` merely meet such a term. Keep large powers
  irreducible: name them like `p` and `L` (e.g. `montgomeryRadix` for `2^260`), with an
  unfolding lemma that is exactly the definition (`montgomeryRadix_eq`) and characterisation
  lemmas proved before `attribute [irreducible]`; state specs with the name.
- **Export only the key specs.** A step lemma needed only inside its own file (loop specs,
  `#decompose` parts, closure `call_mut` specs, inner constants, variants with extra
  postconditions) is `@[local step] private theorem`. It is then neither visible nor registered
  for `step` outside the file (and does not leak a public `mvcgen_spec`). Public `@[step]`
  theorems are the audited specs and the few helper specs other files genuinely use.
- **No auto-generated names.** Never refer to names a tactic invented (`h_1`, `x✝`, `a_post1`,
  `i1`). Name what you use (`step as ⟨r, hr⟩`, `obtain ⟨…⟩`, `intro`).
- **`p` and `L` stay irreducible.** Use their characterisation lemmas in `Curve25519/Basic.lean`
  (add new ones there, before the `attribute [irreducible]` line) instead of unfolding them.
- **No** `sorry`, `native_decide` or `admit`. `bv_decide` is allowed; its certificate axioms then
  appear in the audit file's axiom list.
- **Tactics Aeneas's `aeneas-lean-core` guidance bans** (`omega`, `linarith`, `nlinarith`,
  `congr N`, …) are banned only in proofs about the generated code: spec theorems, loop specs and
  their helpers, where the goals involve Aeneas scalars and containers. In pure mathematical
  lemmas (e.g. about `Nat`, `ZMod p`, `Nat.ofDigits`), use whichever tactic is right, including
  these.
- **Statements are frozen.** A proof file never changes the statement text of its theorem.

## Specs: workflow per Rust file

1. **Inventory:** list the Rust items and their Lean names (`Funs.lean` doc comments).
2. **Statements:** write the `Defs` additions, the proof files (theorems proved by `sorry`) and the audit file. Fill the `#guard_msgs` lines from the output of `lake env lean <audit file>`.
3. **Review gate:** the owner reviews the audit file and `Defs`. Statements are then frozen; any change needs sign-off.
4. **Proofs:** fill in the proofs following "Proof quality" (and the Aeneas `aeneas-lean-core`
   workflow), and update the `#guard_msgs` lines as they land.
5. **Done:** no `sorryAx` left in the audit file. Add the audit module to the strict CI build.

## Building locally (memory)

The machine has 31 GB and 20 cores; `lake build` runs one Lean process per module in parallel, each
using 1–5 GB. When several agents or builds run at once: check single files with
`lake env lean <file>`, build one module target per `lake build` command, run at most one Lean
process per agent, and avoid language-server tools in agents. Do full builds only when nothing else
is running.

## CI

- **`lean-translation.yml`:** the translation is current.
- **`lean-build.yml`:**
  - `lake build --wfail` for `Curve25519Dalek`, `Subtle`, `Zeroize`, `Curve25519` and completed audit modules;
  - `lake build Specs`, lenient (sorry warnings allowed);
  - `runLinter` on `Subtle`, `Zeroize`, `Curve25519` and `Specs`.
