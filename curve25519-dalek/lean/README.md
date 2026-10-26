# Lean verification of curve25519-dalek

Specifications of curve25519-dalek's public API in Lean 4, proved against an
[Aeneas](https://github.com/AeneasVerif/aeneas) translation of the Rust code.

| Library | Content |
|---|---|
| `Curve25519Dalek` | The Aeneas translation (`Funs.lean`, `Types.lean`, generated) and the hand-written external functions and types (`FunsExternal.lean`, `TypesExternal.lean`). |
| `Specs` | One spec summary per Rust file: each public item's statement and the axioms it depends on. |
| `Defs` | The definitions the statements use. |
| `Proofs` | The proofs, one file per Rust item. |
| `EllipticCurve`, `Curve25519` | Curve models and the curve's facts, independent of dalek (repository root). |
| `Subtle`, `Zeroize` | Models of the `subtle` and `zeroize` crates (repository root). |

To trust the result, read `Specs`, `Defs`, `EllipticCurve`, `Curve25519`,
`Curve25519Dalek/{Types,Funs}External.lean`, `Subtle/{Types,Contract}.lean` and
`Zeroize/Contract.lean`; the proofs need not be read.

Build from the repository root with `lake exe cache get && lake build`. To regenerate the
translation: `scripts/aeneas-install.sh`, then `scripts/aeneas-translate.sh`.
