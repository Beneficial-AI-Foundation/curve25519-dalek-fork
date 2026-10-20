# Experiments (not built, not audited)

Material kept so that pending decisions can be taken without redoing the measurements. Nothing
here is imported by any `lean_lib`; the Lean files are not compiled by `lake build`.

- `precomputed-tables/`: the experiments behind the table-certification options recorded in
  `notes.md` ("To decide: certifying the precomputed tables"). Option (a), per-entry kernel
  certificates for `ED25519_BASEPOINT_TABLE` and `AFFINE_ODD_MULTIPLES_OF_BASEPOINT(_128)`: the
  mathematical side (`Curve25519/Proofs/Edwards/*`: the expected multiples as numerals and their
  `decide +kernel` checks, split in chunks) and the limb-extraction side (`Proofs/*`: reading the
  limbs out of the translated constants). To rerun, copy a file into the matching place under
  `curve25519-dalek/lean/` and build that single module (watch memory: the 768-bind table
  extraction peaked at 7.7 GB and timed out).
- `python/tables.py`: independent check that the three tables hold the expected multiples of the
  basepoint (all correct). `python/consts.py`: decimal values of dalek's limb constants.
  `python/x25519.py`: a reference Montgomery ladder and affine arithmetic used to cross-check
  the Lean `ladder` and the RFC 7748 vectors.
