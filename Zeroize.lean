module
public import Zeroize.Basic
public import Zeroize.Lemmas
public import Zeroize.Instances
public import Zeroize.Consistency

/-! # The `zeroize` crate (zeroize-1.8.2)

* `Zeroize/Basic.lean`: TRUSTED. Opaque signatures and spec axioms.
  `Curve25519Dalek/FunsExternal.lean` imports only this file.
* `Zeroize/Lemmas.lean`: derived generic results (no axioms).
* `Zeroize/Instances.lean`: derived results about the instances generated in
  `Curve25519Dalek/Funs.lean`.
* `Zeroize/Consistency.lean`: models satisfying every spec axiom, which shows the axioms are
  consistent.

The trait structures (`zeroize.Zeroize`, `zeroize.DefaultIsZeroes`) are generated in
`Curve25519Dalek/Types.lean`, so this library depends on, and is specific to, the
`Curve25519Dalek` translation.
-/
