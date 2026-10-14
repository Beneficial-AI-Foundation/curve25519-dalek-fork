# To do

1. Add std lib models to Aeneas
2. Incorporate all proofs
  - Serial 64 backend (field.rs, scalar.rs)
  - primality of p, L: currently axioms (see below)
  - src/field.rs
  - src/scalar.rs
  - Serial 32 backend
  - Elliptic curves
  - All the other files
3. Make it so Aeneas supports project-defined traits for external-crate (see below)
4. Incorporate the new formalisation of elliptic curve models

## Contributors to the earlier project (future co-authors)

Many proofs here are adapted from https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify. Its contributors, to be credited as
co-authors of this work. 

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

## Performance findings (2026-10-10)

- Slowest proof files: long straight-line functions (`to_bytes`, `mul`, `montgomery_reduce`),
  8–13 s each. The remaining cost is Aeneas's `step*` itself: before every step it tries all
  hypotheses as specs (quadratic in the context size), it ends with a failing `grind` attempt
  (0.5–1 s), and it repeatedly searches for `Lean.Grind.NoNatZeroDivisors (BitVec n)`. Worth
  reporting upstream to Aeneas.
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
  aggregating self time per trace node, as done for `step-star-performance.md`); the
  cumulative breakdown with `-Dprofiler=true`. The lean-lsp MCP's `lean_profile_proof` does the
  same for one theorem (copies it into a temporary file; may fail for proofs relying on private
  helpers or local `#decompose` definitions). Full tracing adds overhead and can push heavy
  proofs over their heartbeats.

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

**Memory safety when measuring:** builds run one Lean process per module in parallel (20 cores);
limit parallelism (e.g. `LEAN_NUM_THREADS`, observed to cap Lake's jobs) or measure files one
at a time, and run nothing else meanwhile.

## Conventions

The repository layout, translation rules, external-crate libraries and the spec/proof
conventions are in `verif-guidelines.md`.

## Target names (done; unquoted names blocked)

The four translation targets are named `x86_64-tables`, `x86_64-no-tables`, `i686-tables`,
`i686-no-tables` (JSON target specs in `scripts/aeneas-translate.sh`). Names that are valid Lean
identifiers (`x86_64`, `x86_64_no_tables`, …), which would avoid the `«…»` quoting, make the
translation fail: Aeneas names a trait impl after the last path component of the implementing
type, which for per-target types is the target name, so e.g. `Mul<&Scalar>` for
`&EdwardsBasepointTable.x86_64` and for `&EdwardsBasepointTableRadix32.x86_64` both become
`SharedAx86_64.Insts.CoreOpsArithMulSharedBScalarx86_64` (324 clashes). With a hyphenated target
name Aeneas includes the type name, so the clash does not arise. Fix upstream: build impl names
from the type name plus the target component.

## To do: project-defined traits for external-crate libraries

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

## Spec campaign status

- `src/backend/serial/u64/field.rs`, `scalar.rs`, `constants.rs`: all statements proved (no
  `sorryAx`); audit modules in the strict CI build. The `EdwardsPoint` constants and tables wait
  for the curve model.
- `src/field.rs` (u64 backend, `FieldElement51`): all statements proved; in the strict CI build.
  `invert`, `sqrt_ratio_i`, `invsqrt` and the batch inversions use `p_prime` (a theorem).
- Next: `src/scalar.rs` (the `Scalar` type).
