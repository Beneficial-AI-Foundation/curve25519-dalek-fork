# Curve API

Working note (2026-10-17; decisions closed 2026-10-19; all eight implementation steps delivered 2026-10-20, see the "Implementation notes" under each section). It fixes the Lean
interface for curves, models, points, coordinate systems, conversions, encodings and group facts.
Proofs behind the interface may start as certificates and be replaced later; nothing that imports
the API should notice.

**Two developments, not one.** This milestone builds:
1. **`EllipticCurve`** (new `lean_lib`): a formalisation of elliptic-curve models over a field,
   independent of any particular curve, written to Mathlib's standards and intended to end up
   there (or to merge with FEC). It never mentions `p`, `L`, `25519` or dalek.
2. **`Curve25519`** (existing `lean_lib`): the small application, i.e. the specific models of
   curve25519 and their facts (parameters, basepoint, orders, torsion, X25519, ristretto255),
   built on `EllipticCurve`. This is what the dalek specs (`Defs`, `Specs`) import.

Dependency order: `EllipticCurve` ← `Curve25519` ← `Defs` ← `Proofs`/`Specs`. Nothing in
`EllipticCurve` may import `Curve25519`.

Companion: `curve-requirements.md` (what the dalek specs need, item by item).

## 0. Terminology

Three levels, used literally throughout the code and the notes:

- **Curve**: the inherent object, the `𝔽_p`-isomorphism class (j-invariant plus twist datum).
  It has a group of points but no equation. A quadratic *twist* is a different curve. The type
  is `Curve F` (§3), present from the start; only its hidden construction will improve.
- **Model**: an explicit equation with coefficients whose solution set, with its group law,
  realises a curve: `TwistedEdwardsModel (a, d)`, `MontgomeryModel (A, B)`, Mathlib's
  `WeierstrassCurve` (a model despite its name). Each model has one canonical point type
  (`E.Point`: affine points, plus `∞` where the model needs it). Two models of one curve are
  related by an `≃+` that changes the point set.
- **Coordinates**: a redundant way to write points of *one* model: projective, extended,
  completed, the two Niels forms. No new curve, no new group. Each coordinate system has an
  `OnCurve` predicate and a many-to-one `toPoint` into the model's point type; its operations
  are formulas proved correct with respect to `toPoint`. Changing coordinates is the identity on
  points; changing model is not.

Also: an **encoding** is a map between points and bytes/naturals with a canonicity condition;
a **representative** (Ristretto only) is a model point standing for a coset; the dalek Rust
types are **implementations** of a coordinate system on limbs (`EdwardsPoint` implements
extended coordinates of the Edwards model of curve25519).

## 1. Principles

1. **Statements see signatures and lemmas, never bodies.** Every definition is hidden (module
   system default). Importers get a `_def` lemma where the body is itself the specification
   (`p_def`, `Equation_def`), and characterisation lemmas otherwise (`add_x`, `add_y`, …).
   Exceptions marked `@[expose]`: `Prop`-valued definitions that specs unfold, and the small
   computable formula functions that kernel `decide` must evaluate (see §8).
2. **Swappable implementations.** Each topic is a pair of modules: a definitions module
   (`…/Defs.lean`: structures, hidden definitions, instances) and a properties module that
   `import all`s it (`…/Lemmas.lean`, or several), where the characterising lemmas are proved by
   unfolding the hidden bodies. Downstream modules import the properties module (`public import`)
   and see the statements but never the bodies. Heavy certificate proofs may sit in further
   non-audited `…/Proofs/*.lean` modules that also `import all` the definitions, with the audited
   properties module re-exporting their results. Replacing a proof module never changes a
   definitions module. Where a definition's *construction* may change (e.g. the group law via
   transport today, a direct proof tomorrow), the properties module states only characterising
   lemmas, and no `_def` lemma is provided, so no importer can depend on the construction.
3. **Generic and specific are separate libraries.** `EllipticCurve` holds twisted Edwards and
   Montgomery models over any field, in Mathlib style (`WeierstrassCurve`-like structures,
   `E.Point`, `E.Equation`), with top-level names (`TwistedEdwardsModel`, `MontgomeryModel`).
   `Curve25519` holds only instances and curve-specific facts, in namespace `curve25519`. A
   generic lemma that turns out to be needed only for curve25519 still goes in `EllipticCurve`
   if it is generic; curve-specific constants, certificates and encodings never go there.
4. **Coordinate systems are mathematical objects.** Extended, projective, completed and Niels
   coordinates exist at the field level, with their own validity predicates, conversion
   functions and formulas. The dalek layer (`Defs`) only maps limbs to field elements and reuses
   these. So a Rust spec factors into "the code computes the formula" (limb arithmetic) and "the
   formula is correct" (curve mathematics, proved once here).
5. **Two separate validity notions everywhere:** `OnCurve` (algebra, here) and limb bounds (in
   `Defs`, dalek-specific). Never bundled.
6. **Total maps, explicit relations.** `toPoint` is total (junk = `0` off-curve); every lemma about
   it carries an `OnCurve` hypothesis. For statements about Rust outputs, specs say
   `r.OnCurve ∧ r.toPoint = …`.
7. **No `sorry`, no new axioms, no `native_decide`.** `decide +kernel` certificates are fine.
8. **Models are not the curve.** `TwistedEdwardsModel F` and `MontgomeryModel F`
   are coefficient data of an equation, and `E.Point` is its solution set. The curve itself is
   `Curve F` (§3), a hidden type; each model has `toCurve` and a pinned group isomorphism
   `pointEquiv : E.Point ≃+ E.toCurve.Point`, and the group on `E.Point` is *defined* by
   transport along it. Today `Curve F` is built from Weierstrass models; later it becomes the
   isomorphism class `(j, twist datum)` (FEC's `IsomCl`), and nothing outside the hidden
   construction changes. To keep that freedom:
   - no API module mentions `WeierstrassCurve`; the Weierstrass model is one more model, with its
     own equivalence file (§5.4);
   - every model-to-model equivalence (`toMontgomeryEquiv`, `rescale`, `toWeierstrassEquiv`) is
     pinned by coordinate lemmas in both directions, so that any backend must produce the *same*
     map, not one differing by an automorphism;
   - point types are our own inductives/structures, never abbreviations of another library's
     point type.

## 2. Module layout

Each entry is a topic: a definitions module plus a properties module (`import all`), and where
needed a non-audited `Proofs/` module (principle 2, §8).

### 2.1 `EllipticCurve` lib (generic; new `lean_lib`, `srcDir = curve25519-dalek/lean`)

```
EllipticCurve.lean                        root
EllipticCurve/Field/Sign                  ZMod.isNeg (parity of the canonical representative), abs, lemmas
EllipticCurve/Curve/Basic                 Curve F (hidden quotient), C.Point, AddCommGroup, Fintype
EllipticCurve/Weierstrass/PointEquiv      point-group isomorphism along a VariableChange (generic, audited)
EllipticCurve/TwistedEdwards/Basic        structure, Equation, Point, IsComplete
EllipticCurve/TwistedEdwards/Group        AddCommGroup E.Point, formula lemmas, nsmulBinary
EllipticCurve/TwistedEdwards/Coords       Extended/Projective/Completed/Niels coordinate systems
EllipticCurve/TwistedEdwards/Formulas     doubling/addition formulas in each coordinate system
EllipticCurve/TwistedEdwards/Encoding     isNeg, encode, decode (RFC 8032 shape, generic in p, bits)
EllipticCurve/TwistedEdwards/Even         4-torsion, Rel, EvenQuotient over Mathlib's `AddSubgroup.even` (Decaf/Ristretto construction)
EllipticCurve/Montgomery/Basic            structure, Equation, Point (own inductive), group, u, v
EllipticCurve/Montgomery/ToCurve          M.toCurve, M.pointEquiv (the group on M.Point comes from here)
EllipticCurve/Montgomery/XOnly            twist, xMul, xDBL/xADD on (U:W), ladder
EllipticCurve/TwistedEdwards/ToCurve      E.toCurve, E.pointEquiv (via E.toMontgomery)
EllipticCurve/Equiv/EdwardsMontgomery     E ≃+ E.toMontgomery, u/v-formulas, rescaling, toCurve_toMontgomery
EllipticCurve/Equiv/MontgomeryWeierstrass M ≃+ Mathlib Weierstrass model (derived)
EllipticCurve/Proofs/**                   heavy proofs, not audited
```

Future, same library: the improved construction of `Curve F` (quotient by isomorphism, then the
j-invariant / twist-datum description, FEC's `IsomCl`), `Curve.j`, and **admissibility
predicates on the curve** (`Curve.HasMontgomeryModel`, `Curve.HasCompleteEdwardsModel`; FEC's
`AdmissibleIsomCl`), each with a constructor producing a model of that curve and a theorem
characterising when it holds. Not every curve has every model; at the model level the
corresponding conditions are `IsNonsingular`/`IsComplete` and the hypotheses of the
model-to-model equivalences (§6.2). Also: Weierstrass as a model in its own right, Decaf for
cofactor 4.

### 2.2 `Curve25519` lib (the application)

```
Curve25519.lean                         root
Curve25519/Basic                        p, L, a, d, A, sqrtM1 (exists)
Curve25519/Prime                        p, L prime (exists)
Curve25519/Edwards/Basic                edwards : TwistedEdwardsModel, montgomery : MontgomeryModel, curve : Curve, instances, square/non-square facts
Curve25519/Edwards/Basepoint            basepoint, coordinates, addOrderOf = L
Curve25519/Edwards/Order                card = 8L, (8L) • P = 0, decomposition ℤ/8 × ℤ/L
Curve25519/Edwards/Torsion              torsion8, the eight torsion points
Curve25519/Edwards/Encoding             RFC 8032 encode/decode instance, basepoint encoding
Curve25519/Montgomery                   edwardsToMontgomery ≃+, montgomeryBasepoint (u = 9), montgomeryTwist, card of twist
Curve25519/X25519                       clamp, decodeU, encodeU, x25519 (RFC 7748 on numbers), x25519_eq_xMul
Curve25519/Ristretto/Basic              Ristretto group, card = L, basepoint, rel_iff_formula, even_iff_isSquare
Curve25519/Ristretto/Encoding           sqrtRatioM1, RFC constants, encodeRep/decodeRep, encode/decode
Curve25519/Ristretto/Map                mapRep/map, fromUniform
Curve25519/Proofs/**                    certificates and heavy proofs, not audited
```

Audited: everything except the two `Proofs/**` trees. `lakefile.toml` gains the `EllipticCurve`
lib (default target, strict CI build, linter); `Curve25519` requires it.

## 3. The abstract curve (`EllipticCurve/Curve/Basic`)

The central notion. Its API is small on purpose: a type, its point group, and what every model
provides to connect to it. Everything else about a curve is said through its models.

```lean
/-- An elliptic curve over `F`, up to `F`-isomorphism. Hidden construction. -/
def Curve (F : Type*) [Field F] : Type
namespace Curve
/-- The group of `F`-rational points. Hidden; only the instances and lemmas below are visible. -/
def Point (C : Curve F) : Type
instance : AddCommGroup C.Point ; instance : DecidableEq C.Point ; instance [Fintype F] : Fintype C.Point
end Curve

/-- What a model provides. -/
def TwistedEdwardsModel.toCurve (E) [E.IsComplete] : Curve F
def TwistedEdwardsModel.pointEquiv (E) [E.IsComplete] : E.Point ≃+ E.toCurve.Point
def MontgomeryModel.toCurve (M) [M.IsNonsingular] : Curve F
def MontgomeryModel.pointEquiv (M) [M.IsNonsingular] : M.Point ≃+ M.toCurve.Point
theorem TwistedEdwardsModel.toCurve_toMontgomery (E) : E.toMontgomery.toCurve = E.toCurve
theorem TwistedEdwardsModel.pointEquiv_eq (E) : E.pointEquiv = E.toMontgomeryEquiv.trans E.toMontgomery.pointEquiv
```

Rules:
- The group structure on a model's points is *defined* as the transport of `C.Point` along
  `pointEquiv` (hidden); the model's formula lemmas (`add_x`, `some_add_some`, …) are then
  theorems about that transport. A backend may instead prove the group axioms on the model
  directly and build `pointEquiv` afterwards; the API does not say which.
- `pointEquiv` is pinned only through the model-to-model equivalences and their coordinate
  lemmas (§6.2 for Edwards↔Montgomery). `Curve.Point` itself has no coordinates: statements that
  need coordinates go through a model.
- No lemma distinguishes isomorphic models: in particular there is no injectivity of `toCurve`,
  and no `Curve` constructor. Both would tie the API to a construction.
- Facts "about the curve" (cardinality, `addOrderOf`, torsion structure) are stated about
  `C.Point` for `C := E.toCurve` where convenient, and transported to each model's points by
  `pointEquiv` (`map_nsmul`, `Fintype.card_congr`), so they are proved once.

Construction (decided 2026-10-19, replacing the step-1 subtype): `Curve F` is the **quotient** of
the nonsingular Weierstrass models (`WeierstrassCurve.Affine F` with `IsElliptic`) by the orbit
relation of Mathlib's `VariableChange F` action, so that isomorphic models are *equal* curves and
`Curve F` is the inherent object (every elliptic curve over a field has a Weierstrass model).
`C.Point` is the point group of `Quotient.out C`. A model `M` has `M.toCurve := ⟦W_M⟧` and
`M.pointEquiv := (M.Point ≃+ W_M.Point).trans (W_M.Point ≃+ (Quotient.out ⟦W_M⟧).Point)`, the
second factor being the isomorphism of point groups induced by a variable change
(`EllipticCurve/Weierstrass/PointEquiv.lean`, our own: Mathlib has the action on curves,
`equation_iff_variableChange` and `nonsingular_iff_variableChange`, but not the point map).
Equalities of curves between different models are proved by exhibiting the variable change, e.g.
`montgomery.toCurve = edwards.toCurve` by the scaling `u² = −(A+2)` (a square mod `p`).
`TwistedEdwardsModel.toCurve := E.toMontgomery.toCurve` is `@[expose]` (decided: it only fixes
that the Edwards curve is that of its Montgomery model, and removes the cast from
`pointEquiv_eq`). Later improvement, invisible to the API: the `(j, twist datum)` description.

`Curve.twist` is **removed from the API for now**: on the quotient it needs a well-definedness
proof (isomorphic models have isomorphic twists) and no spec needs a curve-level twist (X25519
uses `MontgomeryModel.twist`). It returns, with `toCurve_twist`, when something needs it.

### Implementation notes (step 1, superseded by the quotient notes below where they differ)

Retained facts about the first construction (`Curve/Basic.lean`, `Curve/Impl.lean`):

- Mathlib's elliptic-curve modules are imported privately; no Weierstrass name is visible to
  importers. The construction interface for model modules is `Curve/Impl.lean`
  (`Curve.ofWeierstrass`, `Curve.ofWeierstrass_eq`, `Curve.ofWeierstrass_congr`,
  `Curve.pointEquivOfWeierstrass`); it is internal, imported privately only, and not part of the
  `EllipticCurve` root module.
- `instance : AddCommGroup C.Point` takes no `DecidableEq F`: Mathlib's group law is instantiated
  with the classical instance inside the hidden body. This instance, `Curve.Point`'s other
  instances and every model definition built on them (`toCurve`, `pointEquiv`, the groups on
  model points) are `noncomputable`; the module system also forces this (a computable definition
  cannot see through a non-exposed type definition).
- `Fintype C.Point` is given for `[Fintype F]` alone (through `instance [Finite F] : Finite
  C.Point` and `Fintype.ofFinite`), without `DecidableEq F`.
- Module system facts that shaped the files: instances are exposed by default (the body of an
  exposed instance would reveal the construction), so every instance on hidden types carries
  `@[no_expose]`; the body of a public non-exposed `def` and proofs may use private imports and
  private declarations, but public *statements* (and instance synthesis inside them) see only
  public imports, so side-condition proofs must not appear in statements; `import all` gives a
  module access to the private declarations and hidden bodies of the imported module;
  `theorem … := rfl` is rejected for exported theorems about hidden bodies, `by rfl` is accepted.
- Superseded: the subtype construction (`a₁ = a₃ = 0`), `Curve.twist` and `twistWeierstrass`,
  `twist_ofWeierstrass`; see the quotient notes.

### Implementation notes (quotient)

What was built for the quotient construction (`EllipticCurve/Curve/Basic.lean`,
`EllipticCurve/Curve/Impl.lean`, new `EllipticCurve/Weierstrass/PointEquiv.lean`, and the
re-plumbing of `Montgomery/Defs.lean`, `TwistedEdwards/Defs.lean`, `TwistedEdwards/Lemmas.lean`),
superseding the step-1 notes on the subtype, `Curve.twist`, `twistWeierstrass`,
`twist_ofWeierstrass` and `C.twist 0 = C`:

- `Curve F := Quotient (MulAction.orbitRel (VariableChange F) {W : WeierstrassCurve.Affine F //
  W.IsElliptic})`, with a private `MulAction` instance on the subtype
  (`C • ⟨W, _⟩ := ⟨C • W, _⟩`, Mathlib's `instance : (C • W).IsElliptic`); `Curve.Point C :=
  (Quotient.out C).1.Point`; the instances are as in step 1 (classical group law, `Finite` from
  `Finite F`, `Fintype` by `Fintype.ofFinite`). `Quotient.out` is noncomputable, which changes
  nothing: everything on `Curve` already was.
- `Curve/Impl.lean`: `ofWeierstrass (W) [W.IsElliptic] : Curve F := ⟦⟨W, _⟩⟧` (no `a₁ = 0`,
  `a₃ = 0` hypotheses any more); `ofWeierstrass_eq (W) (C : VariableChange F) : ofWeierstrass
  (C • W) = ofWeierstrass W` (`Quotient.sound`); `ofWeierstrass_congr (h : W = W')` kept;
  `pointEquivOfWeierstrass (W) [W.IsElliptic] [DecidableEq F] : (ofWeierstrass W).Point ≃+
  W.Point` is the cast along the orbit witness `∃ C, C • W = Quotient.out ⟦W⟧`
  (`Quotient.mk_out`, `Classical.choose`) composed with `(Point.variableChange W C).symm`.
- `Weierstrass/PointEquiv.lean` (audited, generic, Weierstrass names in its signatures; imported
  privately by `Curve/Impl` and by the root `EllipticCurve.lean`, so that it is built and linted
  with the library while `WeierstrassCurve` stays unknown to importers of the root): the point map
  of a variable change in Mathlib's direction, `W.Point → (C • W).Point`,
  `(x, y) ↦ (u⁻² (x - r), u⁻³ (y - s (x - r) - t))` (note `s (x - r)`, not `s x`: this is what
  `variableChange_def`, i.e. `(X, Y) ↦ (u² X + r, u³ Y + u² s X + t)`, inverts), with inverse
  `(x', y') ↦ (u² x' + r, u³ y' + u² s x' + t)`. Exposed coordinate formulas
  `VariableChange.mapX`, `mapY`, `invX`, `invY`; `Affine.equation_variableChange`,
  `nonsingular_variableChange` (via the chain rule on `polynomialX`, `polynomialY`: Mathlib's
  `equation_iff_variableChange` only covers translations); `variableChange_negY`,
  `variableChange_addX`, `variableChange_addY`, `variableChange_slope` (`ℓ' = u⁻¹ (ℓ - s)`; needs
  the two equations, since the tangent case uses `y₁ = y₂`); `Point.variableChange (W) (C)
  [DecidableEq F] : W.Point ≃+ (C • W).Point` pinned by `variableChange_zero`,
  `variableChange_some`, `variableChange_symm_zero`, `variableChange_symm_some`. Additivity
  follows Mathlib's `Point.map` proof: `add_of_Y_eq` and `add_some` on both sides, then the three
  transformation lemmas; every identity is polynomial in `u⁻¹` (`ring` after unfolding, `field_simp`
  only in the slope). Mathlib has no coordinate-ring isomorphism for variable changes, so the
  `toClass` route was not available. Not built: `variableChange_one`, `variableChange_mul` (their
  statements need casts, since `1 • W = W` and `(C * C') • W = C • C' • W` are propositional).
- `Montgomery/Defs.lean`: the group on `M.Point` is now `pointEquivWeierstrass.addCommGroup`
  (transport from Mathlib's group on `M.toWeierstrass.Point`, classical `DecidableEq`) rather
  than from `M.toCurve.Point`, so `zero_eq`, `neg_eq`, `add_eq` are `rfl` and `Lemmas.lean` is
  unchanged; `toCurve := Curve.ofWeierstrass M.toWeierstrass`; `pointEquiv :=
  M.pointEquivWeierstrass.addEquiv.trans (Curve.pointEquivOfWeierstrass M.toWeierstrass).symm`.
  `toCurve_twist` is removed with `Curve.twist`; `twist`, `twist_def`, `twist_A`, `twist_B` stay.
- `TwistedEdwards`: `toCurve` is `@[expose] noncomputable def toCurve := E.toMontgomery.toCurve`;
  `pointEquiv_eq : E.pointEquiv = E.toMontgomeryEquiv.trans E.toMontgomery.pointEquiv` (no cast);
  `toCurve_toMontgomery` unchanged. Nothing else in Edwards changes.
- Module-system facts beyond steps 1 and 2a: a `[DecidableEq F]`-generic `≃+` whose body lives
  at the classical instance must be defined by `obtain rfl : ‹DecidableEq F› = fun a b =>
  Classical.propDecidable (a = b)` *before* the structure is elaborated (inside a `where`
  structure the coercion of the classical `≃+` to a function synthesizes the ambient instance and
  fails with "synthesized type class instance is not definitionally equal"); `(C.u⁻¹ : F)`
  elaborates as `(↑C.u)⁻¹` while Mathlib's `variableChange_a₁`, … use `↑(C.u⁻¹)`, so proofs
  normalise with `Units.val_inv_eq_inv_val`; a `Finite`/`Fintype`/`DecidableEq` instance on a
  hidden type is noncomputable for importers too (`noncomputable example`).
- Checked: `lake build EllipticCurve --wfail` and `lake exe runLinter EllipticCurve` clean;
  `#print axioms` of `Curve.instAddCommGroupPoint`, `MontgomeryModel.pointEquiv`,
  `MontgomeryModel.some_add_some_of_u_ne`, `TwistedEdwardsModel.add_x`,
  `TwistedEdwardsModel.pointEquiv_eq`, `WeierstrassCurve.Affine.Point.variableChange` are
  `[propext, Classical.choice, Quot.sound]`; from a `module` importer of `EllipticCurve`, `unfold
  Curve`, `unfold Curve.Point`, `unfold MontgomeryModel.toCurve` fail, `WeierstrassCurve` and
  `Curve.twist` are unknown, and `E.toCurve` unfolds to `E.toMontgomery.toCurve`; two models
  related by a scaling `(u, 0, 0, 0)` have equal `ofWeierstrass`.

## 4. Twisted Edwards models (`EllipticCurve`)

### 4.1 `TwistedEdwards/Basic.lean`

```lean
/-- `a x² + y² = 1 + d x² y²`. -/
structure TwistedEdwardsModel (F : Type*) [Field F] where
  a : F
  d : F

namespace TwistedEdwardsModel
variable {F : Type*} [Field F] (E : TwistedEdwardsModel F)

@[expose] def Equation (x y : F) : Prop := E.a * x ^ 2 + y ^ 2 = 1 + E.d * x ^ 2 * y ^ 2

/-- Completeness: the affine points form the whole group, and the addition formula has no
exceptional cases. -/
class IsComplete : Prop where
  isSquare_a : IsSquare E.a
  a_ne_zero : E.a ≠ 0
  not_isSquare_d : ¬ IsSquare E.d

@[ext] structure Point where
  x : F
  y : F
  equation : E.Equation x y

instance : DecidableEq E.Point            -- from ext and DecidableEq F
theorem Point.ext_iff …
theorem Point.equation_iff (P : E.Point) : E.a * P.x ^ 2 + P.y ^ 2 = 1 + E.d * P.x ^ 2 * P.y ^ 2
theorem d_ne_zero [E.IsComplete], theorem a_ne_d [E.IsComplete]
```

### 4.2 `TwistedEdwards/Group.lean`

Exposed computable formulas, hidden instance, characterising lemmas:

```lean
variable [E.IsComplete]

/-- Denominators of the addition formula. -/
@[expose] def addDen₁ (P Q : E.Point) : F := 1 + E.d * P.x * Q.x * P.y * Q.y
@[expose] def addDen₂ (P Q : E.Point) : F := 1 - E.d * P.x * Q.x * P.y * Q.y
theorem addDen₁_ne_zero, addDen₂_ne_zero          -- completeness

@[expose] def addX (P Q : E.Point) : F := (P.x * Q.y + Q.x * P.y) / addDen₁ P Q
@[expose] def addY (P Q : E.Point) : F := (P.y * Q.y - E.a * P.x * Q.x) / addDen₂ P Q
theorem equation_addX_addY (P Q) : E.Equation (addX P Q) (addY P Q)

instance : AddCommGroup E.Point           -- hidden construction (today: transport, §4.5)

theorem zero_x : (0 : E.Point).x = 0
theorem zero_y : (0 : E.Point).y = 1
theorem neg_x (P) : (-P).x = -P.x
theorem neg_y (P) : (-P).y = P.y
theorem add_x (P Q) : (P + Q).x = addX P Q
theorem add_y (P Q) : (P + Q).y = addY P Q
theorem sub_eq … (derived), two_nsmul_x/y (doubling formulas, derived)

/-- Computable binary scalar multiplication, for `decide` on constants. -/
@[expose] def nsmulBinary (n : ℕ) (P : E.Point) : E.Point   -- by the exposed add formulas
theorem nsmulBinary_eq (n P) : nsmulBinary n P = n • P

/-- Order-2 and order-4 points, generic facts. -/
theorem eq_zero_or_eq_neg_zero_of_two_nsmul_eq_zero …   -- the 2-torsion is {(0,1),(0,−1)}
theorem x_eq_zero_iff, y_eq_zero_iff (4-torsion points (±√(1/a), 0) when a is a square)
```

Everything a spec about `add`, `double`, `neg`, `mul`, `Sum`, tables, `is_small_order`,
`is_torsion_free` needs is `AddCommGroup` plus these lemmas.

#### Implementation notes (step 2a)

What was built (`EllipticCurve/TwistedEdwards/Defs.lean`,
`EllipticCurve/TwistedEdwards/Lemmas.lean`, `EllipticCurve/Proofs/TwistedEdwards/Group.lean`), and
where it departs from §4.1, §4.2, §4.5 and the generic part of §6.2:

- Files: `TwistedEdwards/Defs.lean` (structure, `Equation`, `IsComplete`, `Point` with
  `DecidableEq` and `@[ext]`, the exposed formulas `addDen₁`, `addDen₂`, `addX`, `addY`, the hidden
  `toMontgomery` with `toMontgomery_def`/`toMontgomery_A`/`toMontgomery_B`, the instance
  `E.toMontgomery.IsNonsingular`, and the hidden bijection, group instance
  `instAddCommGroupPoint`, `toMontgomeryEquiv`, `toCurve`, `pointEquiv`),
  `TwistedEdwards/Lemmas.lean` (`import all` of `Defs`; the audited statements of §4.2 and of the
  generic part of §6.2, plus `nsmulBinary`) and `Proofs/TwistedEdwards/Group.lean` (`import all` of
  `Defs`, imported privately by `Lemmas`; not audited), rather than `TwistedEdwards/Basic.lean`,
  `TwistedEdwards/Group.lean` and `Equiv/EdwardsMontgomery.lean`. `Coords`, `Formulas`,
  `Encoding`, `rescale`, `toTwistedEdwards` are not built (steps 2b and later).
- `IsComplete` has a fourth field `two_ne_zero : (2 : F) ≠ 0`, for the same reason as
  `IsNonsingular`: the birational equivalence and the completeness argument need `char ≠ 2`.
- Construction (hidden): the bijection `E.Point ≃ E.toMontgomery.Point` is
  `(x, y) ↦ ((1 + y) / (1 - y), (1 + y) / ((1 - y) x))` for `y ≠ 1` and `(0, 1) ↦ ∞`, with inverse
  `∞ ↦ (0, 1)`, `(u, v) ↦ (u / v, (u - 1) / (u + 1))`; thanks to `/ 0 = 0` the generic formulas
  already send `(0, -1) ↦ (0, 0) ↦ (0, -1)`, so there is no further case split. The group is
  `Equiv.addCommGroup` along it, `toMontgomeryEquiv` is `Equiv.addEquiv`,
  `toCurve := E.toMontgomery.toCurve` and `pointEquiv := toMontgomeryEquiv.trans
  toMontgomery.pointEquiv`, so `toCurve_toMontgomery` holds by `rfl` in `Lemmas`. The
  decidability inside the bijection is classical; everything built on it is `noncomputable`.
- `add_x`/`add_y` (route of §4.5): `Proofs/TwistedEdwards/Group.lean` proves
  `φ ⟨addX P Q, addY P Q, _⟩ = φ P + φ Q` for the hidden bijection `φ`, hence
  `add_eq_mk : P + Q = ⟨addX P Q, addY P Q, _⟩` (public in `Lemmas`, with `add_x`, `add_y` as
  its components). The right-hand side is the chord-and-tangent formula of
  `Montgomery/Lemmas` (`some_add_some_of_u_ne`, `some_add_some_of_v_ne`, `some_add_some_eq_zero`,
  `zero_def`), and the comparison is reduced to polynomial identities in the Montgomery
  coordinates modulo the two Montgomery equations (Edwards coordinates eliminated through
  `x v = u`, `y (u + 1) = u - 1`; coefficients through `a B = A + 2`, `d B = A - 2`), checked by
  `linear_combination` with certificates computed by Singular (`lift`); the certificates are
  stated as standalone lemmas over plain field variables. Structure after aeneas-use-cases'
  `Parity/EdwardsGroup.lean` (`phi_eq_some`, `sum_formulas`, `finish`, `T_case`, `G1`–`G4`;
  there `a = -1`, `B = 1`, here general, so the certificates were recomputed); completeness
  `addDen₁_ne_zero`/`addDen₂_ne_zero` after FEC `Messy/Edwards/AddFormulaBase.lean`
  (`lam_sq_ne_one`, BBJLP). Cases: `P ∈ {(0, 1), (0, -1)}` (then by symmetry `Q`), and for
  `x₁ x₂ ≠ 0`: `u₁ ≠ u₂` (chord), `u₁ = u₂ ∧ v₁ = -v₂` (then `Q = -P`, sum `(0, 1)`),
  `u₁ = u₂ ∧ v₁ ≠ -v₂` (then `Q = P`, tangent).
- `nsmulBinary` lives in `Lemmas.lean` (its closure proof `equation_addX_addY` needs
  completeness) and takes `[E.IsComplete]`; it is `nsmulBinaryAux P n n` where the exposed
  `nsmulBinaryAux P k n` is structurally recursive on the fuel `k` (`= n • P` for `n < 2 ^ k`,
  `nsmulBinaryAux_eq`), so that kernel `decide` can evaluate it (well-founded recursion on `n`
  would be opaque to `decide`).
- Statements that differ from the text: `v_toMontgomeryEquiv (P) (hy : P.y ≠ 1)` needs no
  `P.x ≠ 0` (at `(0, -1)` both sides are `0`); `toMontgomeryEquiv_symm_y (Q) (hQ : Q ≠ 0)` has
  `Q ≠ 0` instead of `Q.u + 1 ≠ 0`, which is true for `Q = 0` (`u 0 = 0`) while `symm 0 = (0, 1)`
  (for affine `Q`, `Q.u + 1 ≠ 0` is automatic: `toMontgomery_u_add_one_ne_zero`);
  `toMontgomeryEquiv_of_x_eq_zero` names the proof component `E.toMontgomery_equation_zero_zero`;
  `pointEquiv_eq` is `E.pointEquiv = E.toCurve_toMontgomery ▸ E.toMontgomeryEquiv.trans
  E.toMontgomery.pointEquiv` (a public statement cannot unfold the hidden `toCurve`, even in the
  `import all` module, so the cast is unavoidable; `toCurve_toMontgomery` is still `rfl`).
- Extra lemmas: `Defs` states the elementary facts about the equation (`equation_zero_one`,
  `equation_zero_neg_one`, `equation_neg`, `y_sq_eq_one_of_x_eq_zero`,
  `y_eq_one_or_eq_neg_one_of_x_eq_zero`, `x_eq_zero_of_y_sq_eq_one`, `x_eq_zero_of_y_eq_one`,
  `x_eq_zero_of_y_eq_neg_one`, `y_ne_one_of_x_ne_zero`, `y_ne_neg_one_of_x_ne_zero`, `d_ne_zero`,
  `a_ne_d`) and about the Montgomery model (`a_mul_toMontgomery_B : a B = A + 2`,
  `d_mul_toMontgomery_B : d B = A - 2`, `toMontgomery_B_ne_zero`,
  `toMontgomery_equation_zero_zero`, `toMontgomery_u_add_one_ne_zero`,
  `toMontgomery_sq_add_mul_add_one_ne_zero` (no root of `u² + A u + 1`),
  `toMontgomery_u_eq_zero_of_v_eq_zero`, `toMontgomery_v_eq_zero_of_u_eq_zero`); `Lemmas` adds
  `add_eq_mk`, `zero_eq_mk`, `sub_x`, `sub_y`, `two_nsmul_x`, `two_nsmul_y` and the 2-torsion
  `two_nsmul_eq_zero_iff : 2 • P = 0 ↔ P.x = 0` (the 4-torsion lemmas `x_eq_zero_iff`,
  `y_eq_zero_iff` are not built). `zero_x`, `zero_y`, `neg_x`, `neg_y`, `add_x`, `add_y` are
  `@[simp]`.
- Module system facts beyond those of step 1: private declarations of `Defs` may be used in the
  *proofs* of the `import all` modules but not in their public *statements* (so the intermediate
  results about the bijection in `Proofs/TwistedEdwards/Group.lean` are `private`, and only
  `addDen₁_ne_zero`, `addDen₂_ne_zero`, `equation_addX_addY`, `add_eq_mk` and the formula lemmas
  are public there); `import all` does not let a public statement unfold a hidden definition
  (hence the cast in `pointEquiv_eq`); tactics must be imported explicitly even for private use
  (`Mathlib.Tactic.Ring`, `Mathlib.Tactic.NormNum`: `Mathlib.Tactic.LinearCombination` alone does
  not provide `ring`); `IsSquare` needs `public import Mathlib.Algebra.Group.Even` since it
  appears in the public `IsComplete`; `Equiv.addCommGroup` is in
  `Mathlib.Algebra.Group.TransferInstance`.

### 4.3 `TwistedEdwards/Coords.lean`: coordinate systems

Each coordinate system is a plain structure of field elements, with an `OnCurve` predicate, a total
`toPoint`, and the relation to the affine point. Names follow curve25519-dalek's
`curve_models.rs`, since those are standard (Hisil–Wong–Carter–Dawson 2008).

```lean
/-- Extended coordinates `(X : Y : Z : T)`, `x = X/Z`, `y = Y/Z`, `xy = T/Z`. -/
structure Extended (E) where X Y Z T : F
/-- Projective `(X : Y : Z)`. -/
structure Projective (E) where X Y Z : F
/-- Completed `((X : Z), (Y : T))` ∈ ℙ¹ × ℙ¹, `x = X/Z`, `y = Y/T`. -/
structure Completed (E) where X Y Z T : F
/-- Projective Niels `(Y+X : Y−X : Z : 2dT)`. -/
structure ProjectiveNiels (E) where YplusX YminusX Z T2d : F
/-- Affine Niels `(y+x, y−x, 2dxy)`. -/
structure AffineNiels (E) where yPlusX yMinusX xy2d : F

namespace Extended
@[expose] def OnCurve (P : E.Extended) : Prop :=
  P.Z ≠ 0 ∧ P.X * P.Y = P.Z * P.T ∧ E.Equation (P.X / P.Z) (P.Y / P.Z)
theorem onCurve_iff_homogeneous : P.OnCurve ↔ P.Z ≠ 0 ∧ P.X * P.Y = P.Z * P.T ∧
  E.a * P.X^2 * P.Z^2 + P.Y^2 * P.Z^2 = P.Z^4 + E.d * P.X^2 * P.Y^2     -- the form code uses
def toPoint [E.IsComplete] (P : E.Extended) : E.Point      -- hidden: ⟨X/Z, Y/Z, _⟩ if OnCurve, else 0
theorem toPoint_x (h : P.OnCurve) : P.toPoint.x = P.X / P.Z
theorem toPoint_y (h : P.OnCurve) : P.toPoint.y = P.Y / P.Z
theorem toPoint_of_not_onCurve (h : ¬ P.OnCurve) : P.toPoint = 0
/-- Projective equality, what `EdwardsPoint::ct_eq` computes (`T` ignored). -/
@[expose] def ProjEq (P Q : E.Extended) : Prop := P.X * Q.Z = Q.X * P.Z ∧ P.Y * Q.Z = Q.Y * P.Z
theorem projEq_iff_toPoint_eq (hP : P.OnCurve) (hQ : Q.OnCurve) : P.ProjEq Q ↔ P.toPoint = Q.toPoint
instance : DecidableRel (ProjEq (E := E))
end Extended
-- Projective: OnCurve := Z ≠ 0 ∧ Equation (X/Z) (Y/Z); toPoint; toPoint_x/y; ProjEq, projEq_iff_toPoint_eq.
-- Niels forms: no ProjEq (nothing compares them); Affine coordinates are the point itself.
-- Completed: OnCurve := Z ≠ 0 ∧ T ≠ 0 ∧ Equation (X/Z) (Y/T); toPoint; toPoint_x/y.
-- ProjectiveNiels: OnCurve := Z ≠ 0 ∧ Equation x y ∧ T2d * Z = 2 * E.d * X * Y  where
--   X := (YplusX − YminusX)/2, Y := (YplusX + YminusX)/2, x := X/Z, y := Y/Z; toPoint.
-- AffineNiels: OnCurve := Equation x y ∧ xy2d = 2 * E.d * x * y with x, y as above; toPoint.
```

Conversions (the ones the code has, as total functions, each with `onCurve_*` and `toPoint_*`
lemmas):

```lean
def Point.toExtended (P : E.Point) : E.Extended := ⟨P.x, P.y, 1, P.x * P.y⟩
def Point.toAffineNiels (P : E.Point) : E.AffineNiels
def Extended.toProjective, Extended.toProjectiveNiels, Extended.toAffineNiels (needs 1/Z)
def Projective.toExtended   -- (XZ : YZ : Z² : XY)
def Completed.toExtended    -- (XT : YZ : ZT : XY)
def Completed.toProjective  -- (XT : YZ : ZT)
theorem toPoint_toExtended (P : E.Point) : P.toExtended.toPoint = P     -- etc.
theorem onCurve_toProjective (h : P.OnCurve) : P.toProjective.OnCurve   -- etc.
theorem toPoint_toProjective (h : P.OnCurve) : P.toProjective.toPoint = P.toPoint
```

### 4.4 `TwistedEdwards/Formulas.lean`: operations in coordinates

Exactly the formulas `curve_models.rs` implements (`a = −1` specialised versions are what the
code uses; state them for `a = −1` as a hypothesis `E.a = -1`, or generically where cheap):

```lean
def Projective.double (P : E.Projective) : E.Completed        -- "dbl-2008-bbjlp"
def Extended.addNiels (P : E.Extended) (Q : E.ProjectiveNiels) : E.Completed
def Extended.subNiels …, Extended.addAffineNiels …, Extended.subAffineNiels …
def ProjectiveNiels.neg, AffineNiels.neg
def Extended.neg, Extended.identity, Projective.identity, ProjectiveNiels.identity, AffineNiels.identity

theorem Projective.double_onCurve (h : P.OnCurve) : P.double.OnCurve
theorem Projective.toPoint_double (h : P.OnCurve) : P.double.toPoint = 2 • P.toPoint
theorem Extended.addNiels_onCurve (hP) (hQ) : (P.addNiels Q).OnCurve
theorem Extended.toPoint_addNiels (hP) (hQ) : (P.addNiels Q).toPoint = P.toPoint + Q.toPoint
… (same for sub, affine variants, neg, identity)
```

These are the "formula is correct" halves of the `curve_models.rs` specs. The dalek spec of
`ProjectivePoint::double` then reads `r.toCompleted = self.toProjective.double` plus limb bounds
(where `toCompleted`/`toProjective` map limbs to field elements, `Defs`), and the math lemma
above gives the group meaning for free.

#### Implementation notes (step 2b)

What was built for §4.3–§4.4 (`EllipticCurve/TwistedEdwards/Coords/Defs.lean`,
`Coords/Lemmas.lean`, `Formulas/Defs.lean`, `Formulas/Lemmas.lean`, all in the root
`EllipticCurve.lean`), and where it departs from the text:

- Files: the two topics are the pairs `Coords/{Defs,Lemmas}` and `Formulas/{Defs,Lemmas}`
  rather than `Coords.lean`, `Formulas.lean`; no `Proofs/TwistedEdwards/Formulas.lean` was
  needed (every correctness proof is `simp only [coordinate relations]; ring`, see below).
  `Formulas/Defs` publicly imports `Coords/Lemmas`; `Coords/Defs` publicly imports
  `TwistedEdwards/Lemmas`.
- Structures as in §4.3: `E.Extended` (`X Y Z T`), `E.Projective` (`X Y Z`), `E.Completed`
  (`X Y Z T`), `E.ProjectiveNiels` (`YplusX YminusX Z T2d`), `E.AffineNiels`
  (`yPlusX yMinusX xy2d`), each `@[ext]` with `DecidableEq`. The coordinates recovered from the
  Niels forms are exposed functions `ProjectiveNiels.X`, `ProjectiveNiels.Y`
  (`((Y+X) ∓ (Y−X)) / 2`), `AffineNiels.x`, `AffineNiels.y`, and the Niels `OnCurve` predicates
  are stated with them exactly as in the text; their `toPoint_x`/`toPoint_y` read
  `P.toPoint.x = P.X / P.Z` resp. `P.toPoint.x = P.x`.
- Decidability: `instDecidableEquation : Decidable (E.Equation x y)` for `[DecidableEq F]`
  (new, in `Coords/Defs`; `Equation` is exposed but not reducible, so instance search needs it),
  `Decidable P.OnCurve` for all five systems, `DecidableRel ProjEq` for `Extended` and
  `Projective`, `Decidable P.IsZero`. All instances are exposed (default), so that kernel
  `decide` can run them from importing modules.
- Division-free forms: a generic `equation_div_iff (hZ) (hT) : E.Equation (X/Z) (Y/T) ↔
  a X² T² + Y² Z² = Z² T² + d X² Y²`, then `onCurve_iff_homogeneous` for all five systems:
  `Extended`/`Projective` as in the text (`a X² Z² + Y² Z² = Z⁴ + d X² Y²`), `Completed`
  (`a X² T² + Y² Z² = Z² T² + d X² Y²`), and the Niels forms, which take `(h2 : (2 : F) ≠ 0)`
  and are stated in `X' = (Y+X) − (Y−X) = 2X`, `Y' = (Y+X) + (Y−X) = 2Y`:
  `4 a X'² Z² + 4 Y'² Z² = 16 Z⁴ + d X'² Y'² ∧ 2 T2d Z = d X' Y'` (affine: `Z = 1`, `xy2d`).
- `toPoint` is `noncomputable` (classical `if h : P.OnCurve`; `0 : E.Point` is noncomputable
  anyway), hidden, with only `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve` (no `_def`, as
  §8 prescribes). `projEq_iff_toPoint_eq` is in `Coords/Defs` (it needs the body).
- `Coords/Lemmas` adds the relations the formula proofs use, all under `[E.IsComplete]`:
  `Extended.X_eq_toPoint_x_mul_Z : P.X = P.toPoint.x * P.Z`, `Y_eq_toPoint_y_mul_Z`,
  `T_eq_toPoint_mul_Z : P.T = x y Z`; the same for `Projective`, `Completed`
  (`Y_eq_toPoint_y_mul_T`), `ProjectiveNiels` (`X_eq…`, `Y_eq…`, `YplusX_eq : = (y + x) Z`,
  `YminusX_eq`, `T2d_eq : = 2 d x y Z`) and `AffineNiels` (`yPlusX_eq`, `yMinusX_eq`,
  `xy2d_eq`). Also the recovered coordinates of the conversions
  (`Extended.toProjectiveNiels_X/Y (h2)`, `Extended.toAffineNiels_x/y (h2)`,
  `Point.toAffineNiels_x/y (h2)`, `ProjectiveNiels.identity_X`, `identity_Y (h2)`, `neg_X`,
  `neg_Y`, and the `AffineNiels` analogues).
- Conversions, identities, negations are exposed and follow the Rust shape: `Point.toExtended
  = ⟨x, y, 1, x y⟩`, `Point.toAffineNiels = ⟨y + x, y − x, x y (2 d)⟩`, `Extended.toProjective`,
  `Extended.toProjectiveNiels = ⟨Y + X, Y − X, Z, T (2 d)⟩` (`T2d = T * EDWARDS_D2`),
  `Extended.toAffineNiels` through `recip := Z⁻¹`, `x := X recip`, `y := Y recip`,
  `⟨y + x, y − x, x y (2 d)⟩`, `Projective.toExtended = ⟨X Z, Y Z, Z², X Y⟩`,
  `Completed.toExtended = ⟨X T, Y Z, Z T, X Y⟩`, `Completed.toProjective = ⟨X T, Y Z, Z T⟩`,
  `Extended.identity = ⟨0, 1, 1, 0⟩`, `Projective.identity = ⟨0, 1, 1⟩`,
  `ProjectiveNiels.identity = ⟨1, 1, 1, 0⟩`, `AffineNiels.identity = ⟨1, 1, 0⟩`,
  `Extended.neg = ⟨−X, Y, Z, −T⟩`, `ProjectiveNiels.neg = ⟨Y−X, Y+X, Z, −T2d⟩`,
  `AffineNiels.neg = ⟨y−x, y+x, −xy2d⟩`. Rust's `square()` is written `^ 2`. Each has
  `onCurve_*` (no completeness needed, except `2 ≠ 0` as an explicit `(h2 : (2 : F) ≠ 0)` for
  everything that recovers `X` from a Niels form: `onCurve_toProjectiveNiels`,
  `onCurve_toAffineNiels`, `Point.onCurve_toAffineNiels`, `ProjectiveNiels.onCurve_identity`,
  `AffineNiels.onCurve_identity`) and `toPoint_*` (`[E.IsComplete]`): `toPoint_toProjective`,
  `toPoint_toProjectiveNiels`, `toPoint_toAffineNiels`, `Projective.toPoint_toExtended`,
  `Completed.toPoint_toExtended`, `Completed.toPoint_toProjective`, `Point.toPoint_toExtended
  : P.toExtended.toPoint = P`, `Point.toPoint_toAffineNiels`, `toPoint_identity = 0` (four),
  `toPoint_neg = -toPoint` (three), `Point.toExtended_injective`. `ProjEq`: `projEq_refl`,
  `projEq_symm` (no hypotheses), `projEq_trans (hQ : Q.Z ≠ 0)`.
- Formulas (`Formulas/Defs`, all exposed, defined for every model): `Projective.double`
  (`XX = X²`, `YY = Y²`, `ZZ2 = 2 Z²`, `(X + Y)²`, …, as `ProjectivePoint::double`), the four
  mixed operations named after their Niels argument, `Extended.addProjectiveNiels`,
  `subProjectiveNiels`, `addAffineNiels`, `subAffineNiels` (the text's `addNiels`/`subNiels`),
  with the `let`s of the Rust code (`PP`, `MM`, `TT2d`, `ZZ2`; `PM`, `MP`; `Txy2d`, `Z2`);
  `Extended.add` is "add-2008-hwcd" for general `a` (`C = d T₁ T₂`, `H = B − a A`),
  `Extended.double P := P.add P`, `Extended.nsmulAux P k n` (fuel `k`, structural, `identity`
  at `n = 0`, `Q.double` / `Q.double.add P` by the parity of `n`), `Extended.nsmul n P :=
  nsmulAux P n n`, `Extended.IsZero P := P.X = 0 ∧ P.Y = P.Z`. No inversion anywhere.
- Correctness (`Formulas/Lemmas`, all under `[E.IsComplete]`; the `a = −1` lemmas take the
  explicit hypothesis `(ha : E.a = -1)` first): `Projective.double_onCurve`,
  `Projective.toPoint_double : P.double.toPoint = 2 • P.toPoint`,
  `Extended.addProjectiveNiels_onCurve`, `Extended.toPoint_addProjectiveNiels : = P.toPoint +
  Q.toPoint`, `subProjectiveNiels_onCurve`, `toPoint_subProjectiveNiels : = P.toPoint −
  Q.toPoint`, `addAffineNiels_onCurve`, `toPoint_addAffineNiels`, `subAffineNiels_onCurve`,
  `toPoint_subAffineNiels`; for every `a`: `Extended.add_onCurve`, `toPoint_add`,
  `double_onCurve`, `toPoint_double`, `nsmulAux_spec (hP) (k n) (hn : n < 2 ^ k)`,
  `nsmul_onCurve`, `toPoint_nsmul : (nsmul n P).toPoint = n • P.toPoint`, `isZero_iff (h :
  P.OnCurve) : P.IsZero ↔ P.toPoint = 0`. Route: two public helpers
  `Completed.onCurve_and_toPoint_eq_add` and `Extended.onCurve_and_toPoint_eq_add` say that a
  completed point `c • (x₁ y₂ + x₂ y₁, y₁ y₂ − a x₁ x₂, addDen₁ p q, addDen₂ p q)`, resp. the
  extended point `(e f : g h : f g : e h)` built from these four, with `c ≠ 0` is on the curve
  and represents `p + q` (by `add_x`, `add_y`, `equation_addX_addY`, `addDen₁_ne_zero`,
  `addDen₂_ne_zero`: this is where completeness enters, giving `Z ≠ 0`, `T ≠ 0` of the
  completed outputs). Each formula is then reduced to four polynomial identities by `simp only
  [formula, X_eq_toPoint_x_mul_Z hP, …, addDen₁, addDen₂, ha]; ring` (the Niels inputs through
  `YplusX_eq`, `YminusX_eq`, `T2d_eq`, `yPlusX_eq`, …; subtraction through `p + (−q)` and
  `neg_x`, `neg_y`); only `Projective.double` needs the curve equation of `p` once
  (`linear_combination ±Z² * he` for `Z`, `T`). No Singular certificates. `nsmulAux_spec`
  mirrors `nsmulBinaryAux_eq`.
- Module-system and tactic facts beyond step 2a: `show` that changes the goal is flagged by the
  `linter.style.show` linter (use `change`); `dif_pos`/`dif_neg` are deprecated for
  `dite_eq_left`/`dite_eq_right`; `rw` does not close a goal that is `rfl` only after unfolding
  an exposed definition (add `rfl`); `simp only [f]` with an exposed `f` unfolds its `let`s and
  reduces the projections of the resulting constructor, which is the pattern used throughout.
- Checked: `lake build EllipticCurve --wfail` and `lake exe runLinter EllipticCurve` clean;
  `#print axioms` of `toPoint_addProjectiveNiels`, `toPoint_subProjectiveNiels`,
  `toPoint_addAffineNiels`, `toPoint_subAffineNiels`, `Projective.toPoint_double`,
  `Extended.toPoint_double`, `toPoint_add`, `toPoint_nsmul`, `isZero_iff`,
  `Extended.projEq_iff_toPoint_eq`, `Projective.projEq_iff_toPoint_eq`,
  `Point.toPoint_toExtended`, `toPoint_toAffineNiels` are `[propext, Classical.choice,
  Quot.sound]`. Certificate engine: from a `module` importing `EllipticCurve`, over `ZMod 13`
  with `E = (−1, 2)` (complete: `IsSquare (−1)`, `¬ IsSquare 2` by `decide`) and the point
  `(2, 4)` of order `16`, `Extended.IsZero (Extended.nsmul 16 ⟨2, 4, 1, 8⟩)` by plain `decide`
  and `16 • P.toPoint = 0` through `toPoint_nsmul`, `isZero_iff`; over `ZMod 1009` with
  `E = (−1, 11)` and `(11, 421)` of order `1032`, `IsZero (nsmul 1032 P)` by `decide +kernel`
  (the whole test file, both fields, `IsComplete` by enumeration over `ZMod 1009` included,
  elaborates in 1.4 s). Plain `decide` on `OnCurve` over `ZMod p` gets stuck in the elaborator
  on `/` (`ZMod.inv` is well-founded recursion); `decide +kernel` works, as does
  `rw [onCurve_iff_homogeneous]; decide`. `IsZero (nsmul k P)` needs no division. From the
  importer, `unfold Extended.toPoint` fails and the exposed formulas (`add`, `double`,
  `identity`, `toProjectiveNiels`, `OnCurve`, `ProjEq`, `IsZero`, `ProjectiveNiels.X`) reduce
  by `rfl`/`Iff.rfl`.

### 4.5 Construction of the group (hidden, `EllipticCurve/Proofs/TwistedEdwards/Group.lean`)

Route (Q1 in `curve-requirements.md`): `E.pointEquiv` is built as `E.toMontgomeryEquiv` followed
by `E.toMontgomery.pointEquiv` (§3); the group on `E.Point` is the transport along it, and
`add_x`/`add_y` follow from the coordinate lemmas of `toMontgomeryEquiv`, proved with polynomial
certificates (template: aeneas-use-cases `Parity/EdwardsGroup.lean`, FEC
`Messy/Edwards/AddFormula*.lean`). The API does not mention the route; a direct proof of the group
axioms with `pointEquiv` built afterwards can replace it later.

### 4.6 `TwistedEdwards/Encoding.lean` (generic, RFC 8032 shape)

```lean
-- EllipticCurve/Field/Sign.lean
/-- Parity of the canonical representative: RFC 8032's "negative". Decidable. -/
@[expose] def ZMod.isNeg {p} (x : ZMod p) : Prop := x.val % 2 = 1
theorem ZMod.isNeg_neg_iff [Fact (Odd p)] (hx : x ≠ 0) : (-x).isNeg ↔ ¬ x.isNeg ; theorem isNeg_zero …

-- EllipticCurve/TwistedEdwards/Encoding.lean
variable (E : TwistedEdwardsModel (ZMod p)) [Fact p.Prime] [E.IsComplete] (bits : ℕ) [Fact (p < 2 ^ bits)]
def encode (P : E.Point) : ℕ := P.y.val + 2 ^ bits * (P.x.val % 2)
theorem encode_lt (P) : encode E bits P < 2 ^ (bits + 1)
/-- Strict RFC 8032 decoding: `none` if y ≥ p or no square root or (x = 0 ∧ sign = 1). -/
def decode (n : ℕ) : Option E.Point
theorem decode_encode (P) : decode (encode P) = some P
theorem encode_decode {n P} (h : decode n = some P) : encode P = n
theorem decode_eq_some_iff : decode n = some P ↔ … (y, sign, equation characterisation)
theorem encode_injective
```

Generic in the model and in `bits` (RFC 8032 uses 255 for edwards25519 and 455 for edwards448).
The square root in `decode` is by `IsSquare`/choice; the `p ≡ 5 (mod 8)` formula with `√−1` is a
curve25519 fact used only in the dalek proofs. Dalek's lenient decoder lives in `Defs` (Q9), with
`decode_eq_lenient_of_canonical`.

## 5. Montgomery models (`EllipticCurve`)

### 5.1 `Montgomery/Basic.lean`

```lean
/-- `B v² = u³ + A u² + u`. -/
structure MontgomeryModel (F : Type*) [Field F] where
  A : F
  B : F

namespace MontgomeryModel
@[expose] def Equation (M) (u v : F) : Prop := M.B * v ^ 2 = u ^ 3 + M.A * u ^ 2 + u
class IsNonsingular (M) : Prop where B_ne_zero : M.B ≠ 0 ; A_sq_ne_four : M.A ^ 2 ≠ 4
/-- Points: the affine solutions plus the point at infinity. Our own type. -/
inductive Point (M) | zero | some (u v : F) (h : M.Equation u v)
instance : DecidableEq M.Point
instance [M.IsNonsingular] : AddCommGroup M.Point     -- hidden construction (today: Weierstrass transport)
theorem zero_def : (0 : M.Point) = .zero
theorem neg_some (h) : -(Point.some u v h) = Point.some u (-v) _
theorem some_add_some … (the chord/tangent formulas as characterising lemmas, incl. the u₁ = u₂ cases)
theorem Point.cases : ∀ P : M.Point, P = 0 ∨ ∃ u v h, P = Point.some u v h
/-- u-coordinate, `∞ ↦ 0` (the x-only convention). -/
def Point.u : M.Point → F
theorem u_zero : (0 : M.Point).u = 0 ; theorem u_mk : (Point.mk u v h).u = u
theorem u_neg (P) : (-P).u = P.u
def Point.v …; theorem v_neg
/-- Right-hand side `f u = u³ + A u² + u`. -/
@[expose] def rhs (M) (u : F) : F
theorem exists_point_with_u_iff : (∃ P : M.Point, P ≠ 0 ∧ P.u = u) ↔ IsSquare (M.rhs u / M.B)
```

Decision (principle 8): `Point` is our own inductive, not an abbreviation of Mathlib's
`WeierstrassCurve.Affine.Point`. The group instance is hidden and characterised by the addition
formulas, so the backend that builds it is free.

#### Implementation notes (step 1)

What was built (`EllipticCurve/Montgomery/Defs.lean`, `EllipticCurve/Montgomery/Lemmas.lean`),
and where it departs from the text above:

- Files: `Montgomery/Defs.lean` (structure, `Equation`, `rhs`, `IsNonsingular`, `Point`, `u`, `v`,
  the exposed formula functions, `twist`, and the hidden `toWeierstrass`/`toCurve`/group
  instance/`pointEquiv`) and `Montgomery/Lemmas.lean` (`import all` of `Defs`; all statements),
  rather than `Montgomery/Basic.lean` + `Montgomery/ToCurve.lean`. `toWeierstrass` is a `private`
  definition of `Defs` (its type mentions Mathlib's `WeierstrassCurve`, so it cannot be public);
  §5.4 (`toWeierstrassEquiv`) is not built yet.
- `IsNonsingular` has a third field `two_ne_zero : (2 : F) ≠ 0`. The Weierstrass discriminant of
  `y² = x³ + A B x² + B² x` is `16 B⁶ (A² - 4)`, so in characteristic `2` the conditions `B ≠ 0`,
  `A² ≠ 4` do not give an elliptic curve; the honest "nonsingular" includes `2 ≠ 0`.
- The chord-and-tangent formulas are stated with exposed formula functions (`@[expose]`, as the
  coordinate formulas of §8): `chordSlope u₁ v₁ u₂ v₂ = (v₂ - v₁) / (u₂ - u₁)`,
  `M.tangentSlope u v = (3 u² + 2 A u + 1) / (2 B v)`, `M.addU u₁ u₂ ℓ = B ℓ² - A - u₁ - u₂`,
  `M.addV u₁ u₂ v₁ ℓ = ℓ (u₁ - M.addU u₁ u₂ ℓ) - v₁`. The lemmas are `some_add_some_of_u_ne`
  (`u₁ ≠ u₂`), `some_add_some_of_v_ne` (`u₁ = u₂`, `v₁ ≠ -v₂`), `some_add_self` (`v ≠ 0`) and
  `some_add_some_eq_zero` (`u₁ = u₂`, `v₁ = -v₂`); the proof components of the right-hand sides
  are `equation_add_of_u_ne`, `equation_add_of_v_ne`, `equation_add_self`, and `equation_neg` for
  `neg_some`.
- Names: the constructor is `some`, so the coordinate lemmas are `u_some`/`v_some` (not `u_mk`);
  `u_zero`, `v_zero`, `u_neg`, `v_neg`, `zero_def`, `some_ne_zero`, `Point.cases`,
  `equation_iff_rhs`, `pointEquiv_zero`. `twist` lives in `Defs` with `twist_def`, `twist_A`,
  `twist_B` (`XOnly` is not built yet). No `neg_zero` of our own: the generic one applies.
- `toCurve_twist` was removed with `Curve.twist` (quotient decision); `twist`, `twist_def`,
  `twist_A`, `twist_B` remain.
- `exists_point_with_u_iff` is deferred to step 2b.
- `Point.u`, `Point.v` are hidden (characterised by `u_zero`, `u_some`, …), `Equation` and `rhs`
  exposed, `DecidableEq M.Point` derived (needs `DecidableEq F`), and the group instance is named
  `MontgomeryModel.instAddCommGroupPoint`.

### 5.4 `Equiv/MontgomeryWeierstrass.lean` (derived, for Mathlib interoperability)

```lean
/-- The Weierstrass model `y² = x³ + A B x² + B² x`, via `(u, v) ↦ (B u, B² v)`. -/
def toWeierstrass (M) : WeierstrassCurve.Affine F
def toWeierstrassEquiv (M) [M.IsNonsingular] : M.Point ≃+ M.toWeierstrass.Point
theorem toWeierstrassEquiv_some (h) : M.toWeierstrassEquiv (.some u v h) = .some (x := M.B * u) (y := M.B ^ 2 * v) _
```

Today this file is where the group on `M.Point` is actually built (transport along the
coordinate bijection, then `Function.Injective.addCommGroup` or `Equiv.addCommGroup`), and
`Montgomery/Basic.lean`'s instance is defined through it. Under another backend the file stays
true as a theorem and is no longer foundational. Either way, nothing outside `Proofs/` and this
file imports Mathlib's elliptic-curve modules.

### 5.2 `Montgomery/XOnly.lean`: twist, `xMul`, the ladder

```lean
/-- The quadratic twist by a non-square `c`: `B c v² = …`. -/
def twist (M) (c : F) : MontgomeryModel F := ⟨M.A, M.B * c⟩
theorem twist_or_curve (hc : ¬ IsSquare c) (u : F) :
  (∃ P : M.Point, P.u = u) ∨ ∃ P : (M.twist c).Point, P.u = u          -- every u lifts somewhere

/-- x-only scalar multiplication, total in `u`; defined via any lift, on the curve or the twist. -/
def xMul (M) (c : F) (n : ℕ) (u : F) : F
theorem xMul_eq_u_nsmul (P : M.Point) : M.xMul c n P.u = (n • P).u
theorem xMul_eq_u_nsmul_twist (P : (M.twist c).Point) : M.xMul c n P.u = (n • P).u
theorem xMul_zero_right (n) : M.xMul c n 0 = 0

/-- Projective x-only point `(U : W)`; `W = 0` is `∞`. -/
structure XZ where U W : F
@[expose] def XZ.toU (P : XZ) : F := P.U / P.W            -- 0 at ∞
@[expose] def xDBL (P : XZ) : XZ ; @[expose] def xADD (P Q D : XZ) : XZ     -- RFC 7748 step
theorem toU_xDBL …, theorem toU_xADD … (with the difference point conditions)
/-- The Montgomery ladder over `n` bits, as RFC 7748 states it (on field elements). -/
@[expose] def ladder (bits : ℕ) (k : ℕ) (u : F) : F
theorem ladder_eq_xMul (hk : k < 2 ^ bits) : ladder bits k u = M.xMul c k u
```

### 5.3 `Curve25519/X25519.lean`: RFC 7748 on numbers (curve25519-specific)

```lean
namespace curve25519
@[expose] def clamp (k : ℕ) : ℕ := 2 ^ 254 + 8 * (k % 2 ^ 254 / 8)        -- matches clamp_integer_spec
@[expose] def decodeU (n : ℕ) : ZMod p := ((n % 2 ^ 255 : ℕ) : ZMod p)      -- top bit masked
@[expose] def encodeU (u : ZMod p) : ℕ := u.val
/-- RFC 7748 §5 `X25519(k, u)` on 32-byte little-endian numbers. -/
@[expose] def x25519 (k u : ℕ) : ℕ := encodeU (ladder 255 (clamp k) (decodeU u))
theorem x25519_lt (k u) : x25519 k u < p
theorem x25519_eq_xMul (k u) : x25519 k u = encodeU (montgomery.xMul 2 (clamp k) (decodeU u))
```

Tier 2a needs `clamp`, `decodeU`, `encodeU`, `ladder`, `x25519` only; tier 2b adds the `xMul`
meaning. Byte arrays ↔ ℕ is `Array.asNat 8` on the dalek side.

#### Implementation notes (step 5)

What was built for §5.2 and §5.3 (`EllipticCurve/Montgomery/XOnly/{Defs,Lemmas}.lean`,
`Curve25519/X25519.lean`, `Curve25519/Proofs/X25519/TestVector.lean`, additions to
`EllipticCurve/Montgomery/Lemmas.lean` and `Curve25519/Basic.lean`), and where it departs from
the text above:

- **The ladder constant is `a24 = (A - 2) / 4`** (`MontgomeryModel.a24`, `121665` for
  curve25519, `montgomery_a24_eq`), as in RFC 7748: the RFC's `z_2 = E · (AA + a24 · E)` is only
  correct with that constant (`(A + 2) / 4` would pair with `BB`). `four_mul_a24 : 4 a24 = A - 2`.
- **Two layers.** The exposed formulas live in `namespace MontgomeryModel.XZ` and are
  parametrised by the field element `a24` rather than by the model: `XZ.dbl a24 P`,
  `XZ.add P Q u₁` (model-independent), `XZ.cswap`, `XZ.LadderState` (`R₀`, `R₁`, `swap`),
  `XZ.ladderStep a24 x₁ s kt`, `XZ.ladderLoop a24 x₁ k t s` (structural in the bit index `t`,
  processing bits `t - 1, …, 0` by `Nat.testBit`), `XZ.ladderXZ a24 bits k u : XZ F` (the
  projective result after the final `cswap`) and `XZ.ladder a24 bits k u := (ladderXZ …).toU`.
  The model-level names are `M.xDBL P := XZ.dbl M.a24 P`, `xADD P Q u₁ := XZ.add P Q u₁`
  (**no `M` argument**: it does not depend on the model and Lean drops an unused `variable`),
  `M.ladder bits k u := XZ.ladder M.a24 bits k u`. Hence `ladder_twist : (M.twist c).ladder =
  M.ladder` is one `simp [ladder, a24_twist]`. The ladder is written exactly as the RFC's
  pseudocode (swap bit carried across iterations, `swap ^= k_t`, `cswap`, final `cswap`), not in
  the pre-swapped form.
- **`Represents` is not the draft's formula.** With the convention `u(∞) = 0`, "`W ≠ 0 ∧ U = u(Q)
  W`" would let `(0 : 1)` represent `∞` (it represents `(0, 0)`), and `represents_xADD` is false
  for it. The definition is `XZ.Represents P Q := (Q = 0 ∧ P.W = 0 ∧ P.U ≠ 0) ∨ (Q ≠ 0 ∧ P.W ≠ 0 ∧
  P.U = Q.u * P.W)` (`represents_zero_iff`, `represents_some_iff`, `toU_of_represents`); `(0 : 0)`
  represents nothing.
- **Formula correctness:** `XZ.represents_xDBL (h : P.Represents Q) : (M.xDBL P).Represents
  (2 • Q)` and `XZ.represents_xADD (h₁ : P₁.Represents Q₁) (h₂ : P₂.Represents Q₂) (hd : (Q₁ -
  Q₂).u = u₁) (hu : u₁ ≠ 0) : (xADD P₁ P₂ u₁).Represents (Q₁ + Q₂)`, plus the `toU_xDBL`,
  `toU_xADD` corollaries. Degenerate cases: `Q = ∞` (`(U : 0) ↦ (U⁴ : 0)`); `Q` of order 2 (`v =
  0`: `W₂ = 4 W⁴ B v² = 0` and `U₂ = W⁴ (u + 1)² (u - 1)² ≠ 0` since `u = ±1` would force `A =
  ∓2`); `v ≠ 0` (the descent identity `B_mul_u_two_nsmul_mul_sq`); `Q₁ = ∞` or `Q₂ = ∞`; `Q₁ =
  -Q₂` (then `u₁ = u(2 Q₁) ≠ 0` gives `u₁² ≠ 1`, so the sum `(… : 0)` is a valid `∞`); `Q₁ = Q₂`
  is excluded by `u₁ ≠ 0`; distinct `u` by the new generic identity
  `MontgomeryModel.u_add_mul_u_sub_of_u_ne : u(Q₁ + Q₂) u(Q₁ - Q₂) (u₁ - u₂)² = (u₁ u₂ - 1)²`
  (`Montgomery/Lemmas.lean`, a `linear_combination` certificate after eliminating the two chord
  slopes; `B`-free, as in FEC's `uADD`). Also added there: `twist_rhs`.
- **Ladder invariant** (`XZ.ladderLoop_inv`, private): for `Q` with `u(Q) ≠ 0`, if the canonical
  pair `canon s := cswap s.swap s.R₀ s.R₁` represents `(m • Q, (m + 1) • Q)`, then after
  `ladderLoop … k t s` it represents `(m' • Q, (m' + 1) • Q)` with `m' = m · 2 ^ t + k % 2 ^ t`
  (`Nat.mod_pow_succ`, `Nat.toNat_testBit`); one step is `ladderStep_inv` (`m ↦ 2 m + k_t`), by
  `cases` on the two bits and the two helpers `step_even` (`(xDBL X, xADD X Y)`, difference
  `m • Q - (m + 1) • Q = -Q`, `u_neg`) and `step_odd` (`(xADD Y X, xDBL Y)`, difference `Q`).
  From the start state `((1 : 0), (u : 1), false)` and `k < 2 ^ bits`: `ladder_eq_u_nsmul (Q)
  (hu : Q.u ≠ 0) (hk : k < 2 ^ bits) : M.ladder bits k Q.u = (k • Q).u`;
  `ladder_eq_u_nsmul_twist` for `Q` on `M.twist c` via `ladder_twist`.
- **`u = 0`:** `ladder_zero : M.ladder bits k 0 = 0` by the invariant "`U W = 0` in both pairs"
  (with `x₁ = 0` every `xADD` has `W₃ = 0`, and `xDBL` of a pair with `U W = 0` has `W₂ = 4 U W
  (…) = 0`), whatever the swaps; the output `U / W` is then `0` in either case.
- **`xMul`** (hidden, `noncomputable`, `[M.IsNonsingular]`): `if ∃ Q : M.Point, Q.u = u then (n •
  Q).u else if c = 0 then 0 else (with isNonsingular_twist) if ∃ Q : (M.twist c).Point, Q.u = u
  then (n • Q).u else 0` (classical choice). Well-definedness: `u_nsmul_eq_of_u_eq (h : Q.u =
  Q'.u) : (n • Q).u = (n • Q').u` (if `u = 0` both points are 2-torsion, `u_nsmul_of_u_eq_zero`;
  else `eq_or_eq_neg_of_u_eq` and `neg_nsmul`, `u_neg`), and `u_nsmul_eq_u_nsmul_twist (hc : ¬
  IsSquare c) (h : P.u = Q.u)` for `P` on `M`, `Q` on the twist (if `u ≠ 0` and `rhs u ≠ 0` then
  `c = (v / w)²`; if `rhs u = 0` both are 2-torsion with the same `u`). Statements:
  `xMul_eq_u_nsmul (c) (n) (Q : M.Point) : M.xMul c n Q.u = (n • Q).u`, `xMul_eq_u_nsmul_twist
  (hc : ¬ IsSquare c) [(M.twist c).IsNonsingular] (n) (Q : (M.twist c).Point)`,
  `xMul_zero_right`, `xMul_zero_left`, `xMul_one [Finite F] (hc)`. `isNonsingular_twist (hc : c ≠
  0) : (M.twist c).IsNonsingular` is a theorem in `XOnly/Defs.lean` (`xMul` needs it).
- **The twist dichotomy needs a finite field.** `exists_point_with_u_iff (u) : (∃ P : M.Point,
  P.u = u) ↔ u = 0 ∨ IsSquare (M.rhs u / M.B)` is generic, but "`r` or `r / c` is a square" is
  false over ℚ, so `exists_point_u_or_twist [Finite F] (hc : ¬ IsSquare c) (u)` is stated for
  finite fields (Mathlib's `quadraticChar`, `quadraticChar_neg_one_iff_not_isSquare`,
  `quadraticChar_one_iff_isSquare`). Consequently `ladder_eq_xMul [Finite F] (hc : ¬ IsSquare c)
  (hk : k < 2 ^ bits) (u) : M.ladder bits k u = M.xMul c k u`, with the field-free form
  `ladder_eq_xMul_of_exists (hc) (hk) (h : (∃ P : M.Point, P.u = u) ∨ ∃ P : (M.twist c).Point,
  P.u = u)`.
- **`Curve25519/X25519.lean`** (`namespace curve25519`): `clamp`, `decodeU`, `encodeU` exposed as
  drafted; `x25519` is `@[expose] noncomputable` (it mentions the hidden `montgomery`; the kernel
  still evaluates it). Lemmas: `clamp_lt`, `two_pow_254_le_clamp`, `clamp_mod_eight`,
  `clamp_add_mod_eight : clamp k + k % 8 = 2 ^ 254 + k % 2 ^ 254` (exactly dalek's
  `clamp_integer_spec`), `clamp_mod_two_pow`, `encodeU_lt`, `decodeU_of_lt`, `decodeU_encodeU`,
  `decodeU_mod_two_pow`, `toU_eq_mul_pow_sub_two (P : XZ (ZMod p)) : P.toU = P.U * P.W ^ (p - 2)`
  (the RFC's final line, `ZMod.pow_card_sub_one_eq_one`), `x25519_lt`, `montgomery_a24_eq`,
  `not_isSquare_two` (`ZMod.exists_sq_eq_two_iff` with the new `p_mod_eight : p % 8 = 5` in
  `Curve25519/Basic.lean`), the hidden `montgomeryTwist := montgomery.twist 2` with
  `montgomeryTwist_def`, `_A`, `_B`, `instance : montgomeryTwist.IsNonsingular`,
  `montgomeryTwist_ladder`, and `x25519_eq_xMul (k u) : x25519 k u = encodeU (montgomery.xMul 2
  (clamp k) (decodeU u))`, `x25519_eq_u_nsmul (k) (Q : montgomery.Point) : x25519 k (encodeU Q.u)
  = encodeU (clamp k • Q).u`, `x25519_eq_u_nsmul_twist` (same for `montgomeryTwist.Point`).
  §6.1's `abbrev montgomeryTwist` is therefore already built here, hidden.
- **Test vectors** (`Curve25519/Proofs/X25519/TestVector.lean`, imported privately by the
  `Curve25519` root so that CI builds it; not audited): the two RFC 7748 §5.2 vectors and Alice's
  public key of §6.1, as little-endian numbers, by `decide +kernel` on `XZ.ladderXZ 121665 255
  (clamp k) (decodeU u)` checked as `U = e W ∧ W ≠ 0` (then `x25519 k u = e` by
  `montgomery_a24_eq` and `ZMod.val_natCast_of_lt`); `Curve25519.Basic` is `import all`ed so that
  the kernel unfolds `p`. The three 255-step ladders take about 1.7 s in total. A wrong expected
  value is rejected by the kernel (checked).
- Kernel facts: `let`-bound exposed formulas, `Nat.testBit` and the structural `ladderLoop`
  evaluate fine on 255-bit numbers; on `ZMod 1009` even `XZ.ladder` with its field inverse
  evaluates by `decide +kernel`. Checked: `lake build EllipticCurve --wfail`, `lake build
  Curve25519 --wfail`, both `runLinter`s clean; `#print axioms` of `ladder_eq_xMul`,
  `ladder_eq_u_nsmul`, `xMul_eq_u_nsmul`, `xMul_eq_u_nsmul_twist`, `represents_xDBL`,
  `represents_xADD`, `exists_point_u_or_twist`, `x25519_eq_xMul`, `x25519_lt`,
  `not_isSquare_two`, `x25519_vector₁` are `[propext, Classical.choice, Quot.sound]`; from a
  `module` importer, `unfold MontgomeryModel.xMul` and `unfold curve25519.montgomeryTwist` fail
  while `ladder`, `x25519`, `XZ.dbl`, `clamp`, `a24`, `Represents` unfold; on `v² = u³ + 3 u² + u`
  over `ZMod 1009` with `Q = (4, 376)` (order 264), `ladder_eq_u_nsmul` plus a kernel evaluation
  gives `(13 • Q).u = 840` and `(5 • Q).u = 993`, matching an independent affine computation.

## 6. The curve25519 application (`Curve25519` lib, namespace `curve25519`)

### 6.1 `Edwards/Basic.lean`

```lean
def edwards : TwistedEdwardsModel (ZMod p) := ⟨a, d⟩
theorem edwards_a : edwards.a = -1 ; theorem edwards_d : edwards.d = d
instance : edwards.IsComplete                   -- d non-square (Euler criterion certificate), −1 square
def montgomery : MontgomeryModel (ZMod p) := ⟨A, 1⟩
instance : montgomery.IsNonsingular
/-- The curve itself. -/
def curve : Curve (ZMod p) := edwards.toCurve
theorem toCurve_edwards : edwards.toCurve = curve ; theorem toCurve_montgomery : montgomery.toCurve = curve
theorem not_isSquare_two : ¬ IsSquare (2 : ZMod p)       -- the twist constant
abbrev montgomeryTwist := montgomery.twist 2
```

### 6.2 `EllipticCurve/Equiv/EdwardsMontgomery.lean` (generic) and `Curve25519/Montgomery.lean`

```lean
def TwistedEdwardsModel.toMontgomery (E) : MontgomeryModel F := ⟨2 * (E.a + E.d) / (E.a - E.d), 4 / (E.a - E.d)⟩
def TwistedEdwardsModel.toMontgomeryEquiv (E) [E.IsComplete] : E.Point ≃+ E.toMontgomery.Point
theorem u_toMontgomeryEquiv (P : E.Point) : (E.toMontgomeryEquiv P).u = (1 + P.y) / (1 - P.y)
theorem v_toMontgomeryEquiv (P : E.Point) (hx : P.x ≠ 0) (hy : P.y ≠ 1) :
  (E.toMontgomeryEquiv P).v = (1 + P.y) / ((1 - P.y) * P.x)
theorem toMontgomeryEquiv_of_y_eq_one (P) (h : P.y = 1) : E.toMontgomeryEquiv P = 0
theorem toMontgomeryEquiv_of_x_eq_zero (P) (hx : P.x = 0) (hy : P.y = -1) : E.toMontgomeryEquiv P = .some 0 0 _
theorem toMontgomeryEquiv_symm_y (Q) (hQ : Q.u + 1 ≠ 0) : (E.toMontgomeryEquiv.symm Q).y = (Q.u - 1) / (Q.u + 1)
theorem toMontgomeryEquiv_symm_x … (so both directions are pinned; principle 8)
/-- Rescaling `v ↦ c v` between `B` and `B / c²`. -/
def MontgomeryModel.rescale (M) (c : F) (hc : c ≠ 0) : M.Point ≃+ (⟨M.A, M.B / c ^ 2⟩ : MontgomeryModel F).Point
theorem u_rescale …
/-- The other direction: `a = (A+2)/B`, `d = (A−2)/B`. Always data; its point group agrees with
`M.Point` only when the Edwards model is complete, which needs hypotheses. -/
def MontgomeryModel.toTwistedEdwards (M) : TwistedEdwardsModel F
theorem MontgomeryModel.toTwistedEdwards_isComplete (h₁ : IsSquare ((M.A + 2) / M.B)) (h₂ : (M.A + 2) / M.B ≠ 0)
  (h₃ : ¬ IsSquare ((M.A - 2) / M.B)) : M.toTwistedEdwards.IsComplete
def MontgomeryModel.toTwistedEdwardsEquiv (M) [M.toTwistedEdwards.IsComplete] : M.Point ≃+ M.toTwistedEdwards.Point
theorem toTwistedEdwards_toMontgomery, toMontgomery_toTwistedEdwards (the two constructions are inverse up to rescaling)

namespace curve25519
/-- The birational isomorphism edwards ≃+ montgomery (B = 1), composing the two above. -/
def edwardsToMontgomery : edwards.Point ≃+ montgomery.Point
theorem u_edwardsToMontgomery (P) : (edwardsToMontgomery P).u = (1 + P.y) / (1 - P.y)
theorem pointEquiv_edwardsToMontgomery (P) :
  montgomery.pointEquiv (edwardsToMontgomery P) = (toCurve_montgomery ▸ toCurve_edwards ▸ edwards.pointEquiv P)
  -- stated without casts in practice: both sides land in `curve.Point` after `toCurve_*` rewrite
```

#### Implementation notes (step 6)

What was built for §6.2 and the twist part of §6.3 (`EllipticCurve/Montgomery/Rescale.lean`,
`EllipticCurve/Montgomery/Count.lean`, `Curve25519/Montgomery.lean`, additions to
`Curve25519/Basic.lean`, both roots), and where it departs from the text:

- **`card_twist` is not `4 L`.** The twist of curve25519 has `2 p + 2 − 8 L = 4 L'` points with
  the *other* prime `L' = 2^253 − 55484635554744707071703875581767296995` (Bernstein's
  "curve25519" paper), not `4 L`. `Curve25519/Basic.lean` gains the hidden `twistL : ℕ := 2 ^ 253
  - 55484635554744707071703875581767296995` with `twistL_def`, `twistL_eq_numeral`, `twistL_pos`,
  `two_mul_p_add_two : 2 * p + 2 = 8 * L + 4 * twistL`; the statements are `card_twist :
  Fintype.card montgomeryTwist.Point = 4 * twistL`, `natCard_twist`, `card_montgomery_add_card_twist
  : Fintype.card montgomery.Point + Fintype.card montgomeryTwist.Point = 2 * p + 2`,
  `four_mul_twistL_nsmul (P : montgomeryTwist.Point) : (4 * twistL) • P = 0`. The primality of
  `twistL` is not proved (nothing needs it; a Lucas certificate as in `Curve25519/Prime.lean` would
  do). The §6.3 line `card_twist : … = 4 * L` above is wrong and should read `4 * twistL`.
- **Rescaling is stated for two models**, not through a model `M.rescale c`: for `M M' :
  MontgomeryModel F` with `hA : M'.A = M.A`, `c ≠ 0` and `hB : M'.B * c ^ 2 = M.B`, the map
  `(u, v) ↦ (u, c v)` sends points of `M` to points of `M'` (`equation_rescale`; inverse
  `equation_rescale_div`), and `rescaleEquiv (M M') [M.IsNonsingular] [M'.IsNonsingular] (hA) (c)
  (hc) (hB) : M.Point ≃+ M'.Point` (hidden, computable body, no `import all`: additivity from the
  chord/tangent lemmas of `Montgomery/Lemmas` and the scaling identities `chordSlope_mul_left`,
  `tangentSlope_rescale` (`ℓ' = c ℓ`), `addU_rescale` (`u₃` unchanged), `addV_rescale` (`v₃`
  scaled by `c`), in the four cases `u₁ ≠ u₂`, tangent, inverse points, zero). Pinned by
  `rescaleEquiv_zero`, `rescaleEquiv_some : … (.some u v h) = .some u (c * v) _`,
  `rescaleEquiv_symm_zero`, `rescaleEquiv_symm_some : … = .some u (v / c) _`, `u_rescaleEquiv`,
  `v_rescaleEquiv : … = c * P.v`, `u_rescaleEquiv_symm`, `v_rescaleEquiv_symm : … = Q.v / c` (all
  `@[simp]`). Also `isNonsingular_rescale (M M') [M.IsNonsingular] (hA) (hB) : M'.IsNonsingular`
  (a theorem, not an instance) and `toCurve_eq_of_rescale : M'.toCurve = M.toCurve` (from
  `toCurve_eq_of_B_eq_mul_sq`). Not built: the compatibility of `rescaleEquiv` with `pointEquiv`
  (it needs the composition law of `Point.variableChange` through the `Classical.choose`d orbit
  witness of `Curve.pointEquivOfWeierstrass`), hence no `pointEquiv_edwardsToMontgomery`.
  The two-model form is what the application needs (`M = edwards.toMontgomery`, `M' =
  montgomery`, `c = sqrtNegAAddTwo`, `hB` by `montgomery_B_mul_sqrtNegAAddTwo_sq`); a model
  `M.rescale c := ⟨M.A, M.B / c²⟩` would have produced `⟨A, s² / s²⟩`, propositionally but not
  syntactically `montgomery`, and a cast.
- **Generic count** (`Montgomery/Count.lean`): `card_add_card_twist [Fintype F] (M) (h2 : (2 : F)
  ≠ 0) (hB : M.B ≠ 0) (hc : ¬ IsSquare c) : Nat.card M.Point + Nat.card (M.twist c).Point = 2 *
  Fintype.card F + 2` (no `IsNonsingular`, no `DecidableEq F` in the statement; `classical` in
  the proof). Proof: the private bijection `M.Point ≃ Option (Σ u, {v // M.Equation u v})` gives
  `Nat.card = ∑ u, #{v | M.Equation u v} + 1`; for each `u`, `M.Equation u v ↔ v² = rhs u / B`,
  and Mathlib's `quadraticChar_card_sqrts` (`#{x | x² = a} = χ(a) + 1`, needs `ringChar F ≠ 2`,
  obtained from `2 ≠ 0` by `ringChar.spec`) gives `(χ(a) + 1) + (χ(a c⁻¹) + 1) = 2` since
  `χ(c⁻¹) = −1` (`isSquare_inv`, `quadraticChar_neg_one_iff_not_isSquare`), uniformly in `a = 0`
  (`χ(0) = 0`). Also there: `instance instFinitePoint [Finite F] : Finite M.Point` and `instance
  instDecidableEquation [DecidableEq F] : Decidable (M.Equation u v)` (`Equation` is exposed but
  instance search does not unfold it). `Curve25519/Montgomery.lean` adds the `Fintype` instance
  on `montgomeryTwist.Point` (`Fintype.ofFinite`, `@[no_expose]`), and `card_twist` is
  `card_montgomery_add_card_twist` (the generic count at `montgomery`, `not_isSquare_two`,
  `ZMod.card`, `montgomeryTwist_def`) with `card_montgomery = 8 L`, `two_mul_p_add_two` and
  `omega`. `exists_montgomery_point_u_or_twist (u : ZMod p)` is `exists_point_u_or_twist` at
  `montgomeryTwist_def`.
- **`Curve25519/Montgomery.lean`** (`public import Curve25519.Edwards.Order`,
  `Curve25519.X25519`; `Curve25519.Ristretto.Basic` is imported *privately*, only for
  `even_iff_isSquare_u`): `montgomery_B_mul_sqrtNegAAddTwo_sq : montgomery.B *
  sqrtNegAAddTwo ^ 2 = edwards.toMontgomery.B`; `edwardsToMontgomery : edwards.Point ≃+
  montgomery.Point := edwards.toMontgomeryEquiv.trans (rescaleEquiv …)` (hidden, no `_def`:
  characterisation lemmas only, as for `toMontgomeryEquiv`), with `u_edwardsToMontgomery (P) :
  (edwardsToMontgomery P).u = (1 + P.y) / (1 - P.y)`, `v_edwardsToMontgomery (P) (hy : P.y ≠ 1) :
  (…).v = sqrtNegAAddTwo * ((1 + P.y) / ((1 - P.y) * P.x))` (RFC 7748 §4.1's `v = √(−486664) · u
  / x`, with the even root `sqrtNegAAddTwo`; this is the exact scaling, `v_rescaleEquiv` after
  `v_toMontgomeryEquiv`), `edwardsToMontgomery_of_y_eq_one (h : P.y = 1) : … = 0`,
  `edwardsToMontgomery_of_x_eq_zero (hx : P.x = 0) (hy : P.y = -1) : … = .some 0 0
  montgomery.equation_zero_zero`, `edwardsToMontgomery_symm_x (Q) (hv : Q.v ≠ 0) :
  (edwardsToMontgomery.symm Q).x = sqrtNegAAddTwo * Q.u / Q.v` (the RFC's `x = √(−486664) · u /
  v`), `edwardsToMontgomery_symm_y (Q) (hQ : Q ≠ 0) : (…).y = (Q.u - 1) / (Q.u + 1)`,
  `even_iff_isSquare_u' (P) : Even P ↔ IsSquare (edwardsToMontgomery P).u`.
- **Basepoint:** `montgomeryBasepoint := edwardsToMontgomery basepoint` (hidden,
  `montgomeryBasepoint_def`), `u_montgomeryBasepoint : montgomeryBasepoint.u = 9` (no
  certificate module: `u_edwardsToMontgomery`, `basepoint_y : = 4 / 5`, then `(1 + 4/5) / (1 −
  4/5) = 9` by `div_eq_iff`, `field_simp`, `ring`, with the new `five_ne_zero : (5 : ZMod p) ≠ 0`
  of `Curve25519/Basic.lean`), `montgomeryBasepoint_ne_zero`, `L_nsmul_montgomeryBasepoint`,
  `addOrderOf_montgomeryBasepoint : = L` (`AddEquiv.addOrderOf_eq`), `encodeU_nine : encodeU 9 =
  9` (`ZMod.val_ofNat_of_lt` with the new `nine_lt_p`), `x25519_basepoint (k) : x25519 k 9 =
  encodeU (clamp k • montgomeryBasepoint).u`, `x25519_basepoint_edwards (k) : x25519 k 9 = encodeU
  (edwardsToMontgomery (clamp k • basepoint)).u`, `x25519_edwards (k) (P) : x25519 k (encodeU
  (edwardsToMontgomery P).u) = encodeU (edwardsToMontgomery (clamp k • P)).u` (all by
  `x25519_eq_u_nsmul` and `map_nsmul`). No `Curve25519/Proofs/Montgomery/*` module was needed.
- Module-system facts: a `by …` block inside a *statement* (the proof argument of `.some u (v / c)
  (by …)`) does not parse across a line break after `exact`; name the proof (`equation_rescale_div`)
  instead. `rw [zero_def]` rewrites only the `(0 : M.Point)` of the first-found instance, so a goal
  `f 0 = 0` across two models needs `zero_def` twice. `addOrderOf_injective f.toAddMonoidHom`
  does not rewrite under the coercion of an `AddEquiv`; `AddEquiv.addOrderOf_eq` does.
- Checked: `LEAN_NUM_THREADS=8 lake build EllipticCurve --wfail`, `lake build Curve25519
  --wfail`, `lake exe runLinter EllipticCurve`, `lake exe runLinter Curve25519` clean;
  `#print axioms` of `edwardsToMontgomery`, `u_edwardsToMontgomery`, `v_edwardsToMontgomery`,
  `edwardsToMontgomery_symm_x`, `edwardsToMontgomery_symm_y`, `u_montgomeryBasepoint`,
  `addOrderOf_montgomeryBasepoint`, `x25519_basepoint`, `x25519_basepoint_edwards`,
  `x25519_edwards`, `card_twist`, `natCard_twist`, `card_montgomery_add_card_twist`,
  `exists_montgomery_point_u_or_twist`, `even_iff_isSquare_u'`, `rescaleEquiv`,
  `card_add_card_twist`, `toCurve_eq_of_rescale` are `[propext, Classical.choice, Quot.sound]`
  (`two_mul_p_add_two`: `[propext]`); from a `module` importing `Curve25519`,
  `u_edwardsToMontgomery`, `card_twist` and `v_rescaleEquiv` rewrite, while `unfold
  curve25519.edwardsToMontgomery`, `unfold curve25519.montgomeryBasepoint`, `unfold
  MontgomeryModel.rescaleEquiv` and `unfold curve25519.twistL` fail.

### 6.3 `Edwards/Basepoint.lean`, `Order.lean`, `Torsion.lean`

```lean
def basepoint : edwards.Point                      -- RFC 8032: y = 4/5, x even
theorem basepoint_y : basepoint.y = 4 / 5
theorem basepoint_x_val_even : ¬ basepoint.x.isNeg
theorem basepoint_x_eq : basepoint.x = (15112221349535400772501151409588531511454012693041857206046113283949847762202 : ZMod p)
def montgomeryBasepoint : montgomery.Point := edwardsToMontgomery basepoint
theorem u_montgomeryBasepoint : montgomeryBasepoint.u = 9
theorem addOrderOf_basepoint : addOrderOf basepoint = L           -- addition-chain certificate
theorem L_nsmul_basepoint : L • basepoint = 0 ; theorem basepoint_ne_zero

instance : Fintype edwards.Point                  -- from Fintype (ZMod p × ZMod p)
theorem card_point : Fintype.card edwards.Point = 8 * L           -- injective encoding + order-8L point
theorem eight_mul_L_nsmul (P : edwards.Point) : (8 * L) • P = 0
theorem card_montgomery : Fintype.card montgomery.Point = 8 * L
theorem card_twist : Fintype.card montgomeryTwist.Point = 4 * twistL   -- 2p + 2 − 8L = 4L', L' = 2^253 − 55484635554744707071703875581767296995 (a different prime; `twistL` in Basic.lean). The draft's `4 * L` was wrong (found in step 6).

def torsion8 : edwards.Point                      -- EIGHT_TORSION[1]
theorem addOrderOf_torsion8 : addOrderOf torsion8 = 8
def eightTorsion : Fin 8 → edwards.Point := fun i => i • torsion8   -- dalek's EIGHT_TORSION order, to be checked
theorem eightTorsion_injective
theorem eight_nsmul_eq_zero_iff (P) : 8 • P = 0 ↔ ∃ i, P = eightTorsion i
theorem L_nsmul_eq_zero_iff (P) : L • P = 0 ↔ ∃ n, P = n • basepoint     -- the prime-order subgroup
theorem exists_unique_decomposition (P) : ∃! (i : Fin 8) (n : Fin L), P = eightTorsion i + n • basepoint
```

#### Implementation notes (step 3)

What was built for §6.1 and §6.3 (`Curve25519/Edwards/Basic.lean`, `Edwards/Basepoint.lean`,
`Edwards/Torsion.lean`, `Edwards/Order.lean`, the non-audited `Curve25519/Proofs/Edwards/Certs.lean`,
additions to `Curve25519/Basic.lean`, one generic lemma in `EllipticCurve/Montgomery/Lemmas.lean`),
and where it departs from the text:

- `Edwards/Basic`: `edwards := ⟨a, d⟩` (hidden; `edwards_def`, `edwards_a : edwards.a = a`,
  `edwards_d`, `edwards_a_eq_neg_one`), `montgomery := ⟨(A : ZMod p), 1⟩` (hidden;
  `montgomery_def`, `montgomery_A`, `montgomery_A_eq : = 486662`, `montgomery_B`),
  `curve := edwards.toCurve` (hidden; `curve_def`, `toCurve_edwards`), `isSquare_a` (from
  `sqrtM1_sq`), `not_isSquare_d` (Euler's criterion `ZMod.euler_criterion` with
  `d_pow_p_div_two`), `instIsCompleteEdwards`, `instIsNonsingularMontgomery`,
  `instFactTwoLtP : Fact (2 < p)`, `edwards_toMontgomery_A : edwards.toMontgomery.A =
  montgomery.A`, `edwards_toMontgomery_B : edwards.toMontgomery.B = (sqrtNegAAddTwo : ZMod p) ^ 2`
  and `toCurve_montgomery : montgomery.toCurve = curve` (via `toCurve_toMontgomery` and the
  generic `MontgomeryModel.toCurve_eq_of_B_eq_mul_sq (M M') (hA : M'.A = M.A) (hc : c ≠ 0)
  (hB : M'.B = M.B * c ^ 2) : M'.toCurve = M.toCurve`, proved in `Montgomery/Lemmas` by the
  variable change `⟨Units.mk0 c hc, 0, 0, 0⟩` sending `W_M'` to `W_M`, `variableChange_def`,
  `ext <;> field_simp <;> ring`, then `Curve.ofWeierstrass_congr` and `Curve.ofWeierstrass_eq`;
  `Montgomery/Lemmas` now imports `EllipticCurve.Curve.Impl` privately). Not built:
  `not_isSquare_two`, `montgomeryTwist`, `montgomeryBasepoint`, `card_twist` (step 6).
- Numeric facts live in `Curve25519/Basic.lean`, not in `Edwards/Basic`: once
  `Mathlib.Algebra.Field.ZMod` is imported, every ring operation on `ZMod p` elaborates through
  `ZMod.instField p (inst : Fact p.Prime)`, and `rw [p_eq_numeral]` then fails ("motive is not
  type correct", the `Fact` instance depends on `p`). `Basic.lean` has no `Field` instance, so
  there `rw [d_eq_natCast, p_eq_numeral]; push_cast; reduce_mod_char` works. Added there:
  `two_lt_p`, `p_mod_two`, `d_ne_zero`, `a_sub_d_ne_zero`, `d_pow_p_div_two : d ^ (p / 2) = -1`,
  `two_mul_a_add_d : 2 (a + d) = A (a - d)`, `A_sq_ne_four`, `instNeZeroTwo : NeZero (2 : ZMod p)`
  (so that the generic `two_ne_zero` applies), `sqrtM1_sq : (sqrtM1 : ZMod p) ^ 2 = -1`, and the
  new hidden constant `sqrtNegAAddTwo : ℕ :=
  6853475219497561581579357271197624642482790079785650197046958215289687604742` (the even square
  root of `-(A + 2) = -486664`, computed by Tonelli–Shanks for `p ≡ 5 (mod 8)`) with
  `sqrtNegAAddTwo_def`, `_lt_p`, `_mod_two`, `_sq : = -(A + 2)`, `_ne_zero` and
  `four_eq_sqrtNegAAddTwo_sq_mul : 4 = sqrtNegAAddTwo² (a - d)`. The lemmas proved in `Basic`
  are used from the `Field` context by `exact` (the instance paths are defeq).
- Certificates (`Proofs/Edwards/Certs.lean`, `import all Curve25519.Basic`, imported privately by
  `Basepoint` and `Torsion`): `import all` does let the kernel unfold the hidden `p` and `L`, so
  `decide +kernel` evaluates `ZMod p` arithmetic there (from an ordinary importer it cannot).
  The field inversion in `d` is avoided by first rewriting the model to its numeral form,
  `edwards = ⟨-1, (37095…3555 : ℕ)⟩` (`edwards_def`, `a_def`, `d_eq_natCast`): `rw` on a goal
  whose only dependence on `edwards` is through `Extended.mk`/`Equation` literals has a
  type-correct motive, so each certificate is `rw [edwards_eq]; decide +kernel`. Everything else
  is the inversion-free route of §4.4: `Extended.nsmul`, `IsZero`/`ProjEq`, `isZero_iff`,
  `projEq_iff_toPoint_eq`, `toPoint_nsmul`, `Point.toPoint_toExtended`. Timings: kernel type
  checking of `IsZero (nsmul L B)` (the 253-step chain on 255-bit numbers) 0.17 s; the whole
  `Certs` module (equations, `L • B`, `8 • T`, `4 • T`, six `ProjEq` tables) 1.4 s wall, 1.3 GB
  RSS. No `native_decide`.
- Module-system facts: a privately imported name may not appear in a public *statement* nor in
  the body of a public hidden `def` (so the certificates are stated for any point with the
  given coordinates, `(P) (hx : P.x = <numeral>) (hy : P.y = <numeral>) : L • P = 0`, and
  `basepoint_equation`, `torsion8_equation` are public theorems of the audited modules that
  re-export `Proofs.*`; `basepoint := ⟨x, y, basepoint_equation⟩`); `if_neg` is deprecated for
  `ite_eq_right`; `isAddCyclic_of_addOrderOf_eq_card` is stated with `Nat.card`
  (`Nat.card_eq_fintype_card`); the coprime-order lemma is
  `AddCommute.addOrderOf_add_eq_mul_addOrderOf_of_coprime`; `h ▸` on `addOrderOf _ ∣ 8 * ↑n`
  with `n : Fin L` fails (the `Fin L` depends on `L`), `rwa [addOrderOf_basepoint] at` works.
- `Basepoint`: `basepoint := ⟨15112221349535400772501151409588531511454012693041857206046113283949847762202,
  46316835694926478169428394003475163141307993866256225615783033603165251855960, _⟩` (hidden;
  `basepoint_def`, `basepoint_x_eq`, `basepoint_y_eq`, `basepoint_y : = 4 / 5`,
  `basepoint_x_val_even : basepoint.x.val % 2 = 0` (stated with `val`, since `isNeg` is not
  built), `basepoint_ne_zero`, `L_nsmul_basepoint`, `addOrderOf_basepoint` by
  `addOrderOf_eq_prime`). The coordinates agree with dalek's `ED25519_BASEPOINT_POINT` limbs.
- `Torsion`: `torsion8 := ⟨14399317868200118260347934320527232580618823971194345261214217575416788799818,
  55188659117513257062467267217118295137698188065244968500265048394206261417927, _⟩` (dalek's
  `EIGHT_TORSION[1]`; hidden, `torsion8_def`, `torsion8_x_eq`, `torsion8_y_eq`,
  `torsion8_ne_zero`, `eight_nsmul_torsion8`, `four_nsmul_torsion8_ne_zero`, `addOrderOf_torsion8`
  by `addOrderOf_eq_prime_pow`); `eightTorsion i := (i : ℕ) • torsion8` (hidden, `eightTorsion_def`,
  `eightTorsion_apply`, `eightTorsion_zero`, `eightTorsion_one`, `eight_nsmul_eightTorsion`,
  `eightTorsion_injective`). Dalek's `EIGHT_TORSION` array is exactly `i • torsion8` (checked
  against the limbs, and pinned by the lemmas `eightTorsion_<i>_x_eq`, `eightTorsion_<i>_y_eq`
  for `i = 2, …, 7`): `2 • T = (-sqrtM1, 0) = (38214883241950591754978413199355411911188925816896391856984770930832735035197, 0)`,
  `3 • T = (x, -y)`, `4 • T = (0, -1)` (`eightTorsion_four_y`), `5 • T = (-x, -y)`,
  `6 • T = (sqrtM1, 0)` (`eightTorsion_six_x`), `7 • T = (-x, y)`, with
  `-x = 43496726750457979451437558183816721346016168361625936758514574428539776020131`,
  `-y = 2707385501144840649318225287225658788936804267575313519463743609750303402022`.
- `Order`: `instFiniteEdwardsPoint`/`instFintypeEdwardsPoint` (injection `P ↦ (x, y)`,
  `Fintype.ofFinite`), `sq_x_eq_of_y_eq`, `x_eq_or_x_eq_neg_of_y_eq` (`a - d y² ≠ 0` since `a/d`
  is not a square), `card_point_le : card ≤ 2 p` (injection `P ↦ (y, decide (x.val % 2 = 1))`,
  `ZMod.neg_val` and `p` odd), `coprime_eight_L`, `addOrderOf_torsion8_add_basepoint = 8 L`,
  `eight_mul_L_dvd_card`, `two_mul_p_lt_sixteen_mul_L`, `card_point = 8 L`,
  `eight_mul_L_nsmul`, `isAddCyclic`, and the decomposition through the bijection
  `Fin 8 × Fin L → edwards.Point`, `(i, n) ↦ eightTorsion i + n • basepoint` (injective by
  applying `(5 L) •`, which is the identity on `torsion8` since `5 L ≡ 1 (mod 8)` and kills
  `basepoint`, then `nsmul_eq_nsmul_iff_modEq`; bijective by cardinality):
  `exists_unique_decomposition (P) : ∃! q : Fin 8 × Fin L, P = eightTorsion q.1 + (q.2 : ℕ) •
  basepoint` (one `∃!` over the pair rather than the text's nested form),
  `eight_nsmul_eq_zero_iff`, `L_nsmul_eq_zero_iff` (both from the decomposition and
  coprimality). Nothing was narrowed. Also `card_curve : Fintype.card curve.Point = 8 L`
  (`toCurve_edwards`, `Fintype.card_congr edwards.pointEquiv.toEquiv`) and
  `instFiniteMontgomeryPoint`/`instFintypeMontgomeryPoint` (via `montgomery.pointEquiv`) with
  `card_montgomery = 8 L` (`toCurve_montgomery`): the rewrite `toCurve_montgomery` inside
  `Fintype.card montgomery.toCurve.Point` is fine, the `Fintype` instance on `Curve.Point` is
  uniform in the curve.
- Checked: `lake build Curve25519 --wfail`, `lake build EllipticCurve --wfail`,
  `lake exe runLinter Curve25519`, `lake exe runLinter EllipticCurve` clean; `#print axioms` of
  `addOrderOf_basepoint`, `card_point`, `eight_mul_L_nsmul`, `addOrderOf_torsion8`,
  `toCurve_montgomery`, `instIsCompleteEdwards`, `L_nsmul_eq_zero_iff`,
  `eight_nsmul_eq_zero_iff`, `exists_unique_decomposition`, `isAddCyclic`, `card_curve`,
  `card_montgomery`, `eightTorsion_two_x_eq`, `basepoint_y`, `toCurve_eq_of_B_eq_mul_sq` are
  `[propext, Classical.choice, Quot.sound]`; from a `module` importing `Curve25519`, `unfold
  curve25519.edwards` and `unfold curve25519.basepoint` fail while `edwards_a` and
  `basepoint_x_eq` work.

### 6.4 `Edwards/Encoding.lean`

Instantiates §4.6 at `edwards` with `bits = 255`: `abbrev encode := edwards.encode 255`,
`abbrev decode := edwards.decode 255`, the specialised lemmas (`encode_lt_two_pow_256`,
`decode_eq_some_iff` with `p` unfolded where useful), plus `encode_basepoint = <numeral>`
(ED25519_BASEPOINT_COMPRESSED).

#### Implementation notes (step 7)

What was built for §4.6 and §6.4 (`EllipticCurve/Field/Sign.lean`,
`EllipticCurve/TwistedEdwards/Encoding/Defs.lean`, `Encoding/Lemmas.lean`,
`Curve25519/Edwards/Encoding.lean`; both roots extended), and where it departs from the text:

- `Field/Sign` (namespace `ZMod`, `{p : ℕ}`): `@[expose] def isNeg (x : ZMod p) : Prop :=
  x.val % 2 = 1` with a `Decidable` instance, `@[expose] def abs (x) := if x.isNeg then -x else x`
  (RFC 9496's `CT_ABS`). The parity lemmas take the oddness of `p` as an explicit hypothesis
  `(hp : p % 2 = 1)` rather than `[Fact (Odd p)]` (the draft's form): in the curve25519 instance
  `p_mod_two` is exactly this statement, and for a complete model over `ZMod p` it is
  `TwistedEdwardsModel.mod_two_eq_one_of_isComplete E` (from `IsComplete.two_ne_zero` through
  `ZMod.mod_two_eq_one_of_two_ne_zero [Fact p.Prime] : (2 : ZMod p) ≠ 0 → p % 2 = 1`), so no
  instance has to be threaded. Lemmas: `isNeg_iff` (`Iff.rfl`), `isNeg_iff_odd_val`,
  `not_isNeg_iff : ¬ x.isNeg ↔ x.val % 2 = 0`, `not_isNeg_iff_even_val`, `isNeg_zero`,
  `isNeg_one [Fact (1 < p)]`, `isNeg_natCast_iff (h : n < p) : (n : ZMod p).isNeg ↔ n % 2 = 1`,
  `isNeg_ofNat_iff` (the same for numerals; with `ZMod.val_ofNat_of_lt` this makes every
  curve25519 sign certificate a `rw` plus `decide`, no kernel computation in `ZMod p`),
  `ne_zero_of_isNeg`; for odd `p`: `isNeg_neg_iff (hx : x ≠ 0) : (-x).isNeg ↔ ¬ x.isNeg`,
  `isNeg_neg_of_not_isNeg`, `not_isNeg_neg_of_isNeg`, `isNeg_or_isNeg_neg`,
  `eq_of_sq_eq_of_isNeg_iff [Fact p.Prime] (h : x ^ 2 = y ^ 2) (hs : x.isNeg ↔ y.isNeg) : x = y`
  (the uniqueness statement behind `decode` and `encode_injective`); `abs_of_isNeg`,
  `abs_of_not_isNeg`, `abs_zero`, `abs_eq_or_abs_eq_neg`, `abs_sq`, `abs_mul_self`,
  `abs_eq_zero_iff` (no hypothesis), and for odd `p`: `not_isNeg_abs`, `abs_neg`, `abs_abs`,
  `abs_eq_iff : x.abs = y ↔ (y = x ∨ y = -x) ∧ ¬ y.isNeg`, `abs_eq_abs_iff : x.abs = y.abs ↔
  x = y ∨ x = -y`; square roots (`[Fact p.Prime]`): `eq_or_eq_neg_of_sq_eq`,
  `exists_sq_eq_not_isNeg (hp) (hx : IsSquare x) : ∃ r, r ^ 2 = x ∧ ¬ r.isNeg`,
  `exists_sq_eq_isNeg (hp) (hx) (hx0 : x ≠ 0)`, and
  `existsUnique_sq_eq_not_isNeg (hp) (hx : IsSquare x) : ∃! r, r ^ 2 = x ∧ ¬ r.isNeg` (stated for
  every square, including `0`, whose unique root `0` is not negative). The module imports
  `Mathlib.Algebra.Field.ZMod` publicly (the field instance for `Fact p.Prime`).
- `Encoding/Defs`: the new exposed formula `xSq (E) (y : F) : F := (y ^ 2 - 1) / (E.d * y ^ 2 -
  E.a)`, the equation solved for `x²` (generic `a`; for `a = -1` it is RFC 8032's
  `(y² - 1) / (d y² + 1)`, `curve25519.edwards_xSq`), so that the dalek `decompress` spec can
  say `IsSquare (edwards.xSq y)`. `@[expose] def encode (E) (bits) (P : E.Point) : ℕ :=
  P.y.val + 2 ^ bits * (if P.x.isNeg then 1 else 0)` (the draft's `P.x.val % 2` is written
  through `isNeg`, so that specs about `is_negative` connect). `decode (E) (bits) (n) :
  Option E.Point` is hidden and noncomputable (`open scoped Classical`): `none` unless
  `n < 2 ^ (bits + 1) ∧ n % 2 ^ bits < p`, then `some ⟨x, y, _⟩` for the `x` with
  `E.Equation x y ∧ (x.isNeg ↔ n / 2 ^ bits = 1)` (by `Classical.choose`) if one exists, else
  `none`. This is the RFC 8032 §5.1.3 procedure with its square root left implicit: "no root"
  and "`x = 0` with `x_0 = 1`" are exactly the cases where no `x` on the model has the requested
  sign (`decode_eq_none_iff`). The range check `n < 2 ^ (bits + 1)` is the strict reading of
  "the 32 bytes" (needed for `encode_decode`); the sign bit is `n / 2 ^ bits`, not
  `n / 2 ^ bits % 2`. The width hypothesis is an instance `[Fact (p < 2 ^ bits)]`, carried only
  by the lemmas that need `y.val < 2 ^ bits`; `encode`, `decode`, `decode_eq_some_iff` and
  `decode_eq_none_iff` do not need it.
- `Encoding/Lemmas` (generic, `E : TwistedEdwardsModel (ZMod p)`, `[Fact p.Prime]`,
  `[E.IsComplete]` where the group or completeness is used): `d_mul_sq_sub_a_ne_zero (y) :
  E.d * y ^ 2 - E.a ≠ 0` (any field, complete model), `equation_iff_sq_eq_xSq : E.Equation x y
  ↔ x ^ 2 = E.xSq y`, `xSq_eq_zero_iff : E.xSq y = 0 ↔ y ^ 2 = 1`, `isSquare_xSq_iff : IsSquare
  (E.xSq y) ↔ ∃ x, E.Equation x y`, `Point.sq_x_eq_xSq`, `sq_x_eq_sq_x_of_y_eq`,
  `mod_two_eq_one_of_isComplete`, `eq_of_y_eq_of_isNeg_iff (hy : P.y = Q.y) (hs : P.x.isNeg ↔
  Q.x.isNeg) : P = Q`; `encode_zero : encode E bits 0 = 1`; with `[Fact (p < 2 ^ bits)]`:
  `val_y_lt_two_pow`, `encode_lt : encode E bits P < 2 ^ (bits + 1)`, `encode_mod_two_pow :
  encode E bits P % 2 ^ bits = P.y.val`, `encode_div_two_pow : encode E bits P / 2 ^ bits = if
  P.x.isNeg then 1 else 0`, `encode_injective`; decoding: `decode_eq_some_iff : decode E bits n
  = some P ↔ n < 2 ^ (bits + 1) ∧ n % 2 ^ bits < p ∧ P.y = ((n % 2 ^ bits : ℕ) : ZMod p) ∧
  (P.x.isNeg ↔ n / 2 ^ bits = 1)` (the draft's two sign conjuncts `(P.x = 0 → s = 0)`,
  `(P.x ≠ 0 → (P.x.isNeg ↔ s = 1))` collapse into the single `↔`, since `isNeg 0` is false and
  `s ≤ 1`), `decode_eq_none_iff : decode E bits n = none ↔ 2 ^ (bits + 1) ≤ n ∨ p ≤ n % 2 ^ bits
  ∨ ¬ IsSquare (E.xSq y) ∨ (y ^ 2 = 1 ∧ n / 2 ^ bits = 1)` with `y := ((n % 2 ^ bits : ℕ) :
  ZMod p)`, and with `[Fact (p < 2 ^ bits)]`: `decode_eq_some_iff_encode_eq : decode E bits n =
  some P ↔ encode E bits P = n` (strict decoding is the partial inverse of encoding),
  `decode_encode`, `encode_decode`, `decode_isSome_iff : (decode E bits n).isSome ↔ ∃ P, encode
  E bits P = n` (the draft's `decode_ne_none_of_canonical`). Nothing was narrowed.
- `Curve25519/Edwards/Encoding`: `instance : Fact (p < 2 ^ 255)`, `noncomputable abbrev encode :
  edwards.Point → ℕ := TwistedEdwardsModel.encode edwards 255`, `noncomputable abbrev decode`
  likewise (`noncomputable` because `edwards` is: the compiler would have to pass it; the
  kernel is unaffected). The abbreviations are transparent to importers: the generic lemmas
  apply to `encode`/`decode` directly (checked), and `unfold encode TwistedEdwardsModel.encode`
  works while `unfold TwistedEdwardsModel.decode` fails. Specialised restatements:
  `encode_eq (P) : encode P = P.y.val + 2 ^ 255 * (if P.x.isNeg then 1 else 0)` (`rfl`),
  `encode_lt_two_pow_256`, `encode_mod_two_pow_255`, `encode_div_two_pow_255`,
  `encode_injective`, `decode_encode`, `encode_decode`, `decode_eq_some_iff` (with `2 ^ 256`,
  `2 ^ 255`), `decode_eq_some_iff_encode_eq`, `decode_eq_none_iff`, `decode_isSome_iff`,
  `edwards_xSq (y) : edwards.xSq y = (y ^ 2 - 1) / (d * y ^ 2 + 1)`; the sign of the basepoint
  `not_isNeg_basepoint_x : ¬ basepoint.x.isNeg` (the draft's `basepoint_x_val_even` in §6.3
  keeps its `val % 2 = 0` form in `Basepoint.lean`; this is its restatement); the numerals
  `encode_basepoint : encode basepoint =
  46316835694926478169428394003475163141307993866256225615783033603165251855960` (the
  little-endian value of dalek's `ED25519_BASEPOINT_COMPRESSED`, bytes `58 66 … 66`: `y` with
  sign bit `0`, checked in Python), `encode_basepoint_lt : encode basepoint < 2 ^ 255`,
  `encode_zero : encode 0 = 1`, and all eight torsion points: `encode_eightTorsion_zero = 1`,
  `encode_torsion8 = encode_eightTorsion_one = 55188…417927` (`x` even), `encode_eightTorsion_two
  = 57896044618658097711785492504343953926634992332820282019728792003956564819968 = 2 ^ 255`
  (`encode_eightTorsion_two_eq_two_pow`; `(-√-1, 0)`, `-√-1` odd), `encode_eightTorsion_three =
  2707385501144840649318225287225658788936804267575313519463743609750303402022` (`-y`),
  `encode_eightTorsion_four = 57896044618658097711785492504343953926634992332820282019728792003956564819948`
  with `encode_eightTorsion_four_add_one : encode (eightTorsion 4) + 1 = p` (`(0, -1)`),
  `encode_eightTorsion_five = 60603430119802938361103717791569612715571796600395595539192535613706868221990`
  (`-y + 2 ^ 255`), `encode_eightTorsion_six = 0` (`(√-1, 0)`, `√-1` even),
  `encode_eightTorsion_seven = 113084703736171354774252759721462249064333180398065250519993840398162826237895`
  (`y + 2 ^ 255`). No certificate module was needed: each proof is `rw [encode_eq,
  <coordinates>, ite_eq_left/right (ZMod.isNeg_ofNat_iff …), ZMod.val_ofNat_of_lt …]` with the
  side conditions `numeral < p` by `rw [p_eq_numeral]; decide` (a pure `ℕ` goal, so the
  `Field`-instance obstruction to `rw [p_eq_numeral]` does not arise) and the parities and
  `2 ^ 255` sums by `decide`. No additions to `Curve25519/Basic.lean` were needed.
- Module-system facts: `split_ifs` pre-simplifies `none = some P` to `False`, so the
  surrounding `iff_of_false` takes `by simp`; `(2 : ZMod 2) = 0` cannot be `decide`d in a
  context with `[Fact p.Prime]` (the numeral elaborates through the field instance), use
  `exact_mod_cast ZMod.natCast_self 2`; `omega` does not see through `n / 2 ^ bits` when
  `2 ^ bits` appears both as `↑2 ^ bits` and `↑(2 ^ bits)` after casts, so the sign-bit case
  split is by `Nat.le_one_iff_eq_zero_or_eq_one`.
- Checked: `lake build EllipticCurve --wfail`, `lake build Curve25519 --wfail`,
  `lake exe runLinter EllipticCurve`, `lake exe runLinter Curve25519` clean; `#print axioms` of
  `TwistedEdwardsModel.decode_encode`, `encode_decode`, `decode_eq_some_iff`,
  `decode_eq_none_iff`, `encode_injective`, `ZMod.existsUnique_sq_eq_not_isNeg`,
  `curve25519.encode_basepoint`, `curve25519.decode_encode`, `encode_eightTorsion_seven` are
  `[propext, Classical.choice, Quot.sound]`; from a `module` importing `Curve25519`, `unfold
  TwistedEdwardsModel.decode` fails while `encode`, `ZMod.isNeg`, `ZMod.abs` unfold,
  `rw [decode_encode]` works, and `decide` evaluates `isNeg`/`abs` on `ZMod 7` numerals.

## 7. Ristretto

In scope now. Two layers: a **generic** quotient construction for complete twisted Edwards curves
(`TwistedEdwards/Even.lean`: this is the Decaf/Ristretto group construction, independent of the
encoding), and the **ristretto255** instance with RFC 9496's encoding and map
(`Ristretto/*.lean`). Dalek specs are stated about Edwards *representatives* (the code's data);
the quotient type exists so that the dalek-independent specification can say "a group of prime
order `L` with an injective encoding", and so that representative-level statements have a
meaning to refer to.

### 7.1 `EllipticCurve/TwistedEdwards/Even.lean` (generic)

```lean
namespace TwistedEdwardsModel
variable (E : TwistedEdwardsModel F) [E.IsComplete]

/-- The 4-torsion `{P | 4 • P = 0}`. -/
def torsion4 : AddSubgroup E.Point
theorem mem_torsion4 (P) : P ∈ E.torsion4 ↔ 4 • P = 0
theorem torsion4_eq_torsionBy : E.torsion4 = (Submodule.torsionBy ℤ E.Point 4).toAddSubgroup
-- The even points are Mathlib's: `Even P` (`∃ Q, P = Q + Q`), `even_iff_exists_two_nsmul`,
-- `Even.add`, `Even.neg`, and the subgroup `AddSubgroup.even E.Point` with `AddSubgroup.mem_even`.
-- Nothing to define.

/-- Representatives are equal in the quotient iff they differ by 4-torsion. -/
@[expose] def Rel (P Q : E.Point) : Prop := P - Q ∈ E.torsion4
theorem rel_refl, rel_symm, rel_trans, rel_add (compatibility with +, −)

/-- The quotient group `AddSubgroup.even E.Point ⧸ (torsion4 ⊓ even)`. Hidden construction. -/
def EvenQuotient : Type
instance : AddCommGroup E.EvenQuotient
def EvenQuotient.mk (P : E.Point) (h : Even P) : E.EvenQuotient
theorem EvenQuotient.mk_eq_mk_iff : mk P hP = mk Q hQ ↔ E.Rel P Q
theorem EvenQuotient.mk_add, mk_neg, mk_zero, mk_nsmul (homomorphism lemmas)
theorem EvenQuotient.mk_surjective
end TwistedEdwardsModel
```

### 7.2 `Ristretto/Basic.lean` (namespace `curve25519`)

```lean
/-- The ristretto255 group. -/
def Ristretto : Type := edwards.EvenQuotient          -- hidden; users see only the API below
instance : AddCommGroup Ristretto ; instance : DecidableEq Ristretto ; instance : Fintype Ristretto
namespace Ristretto
def mk (P : edwards.Point) (h : Even P) : Ristretto
theorem mk_eq_mk_iff : mk P hP = mk Q hQ ↔ edwards.Rel P Q
theorem mk_add …, mk_surjective

/-- Curve-specific facts (edwards.Point ≅ ℤ/8 × ℤ/L, from §6.3). -/
theorem torsion4_eq : edwards.torsion4 = {0, (0,-1), (√-1, 0), (-√-1, 0)}  (as an explicit `Finset`/characterisation)
theorem card_torsion4 : Fintype.card edwards.torsion4 = 4
theorem card_even : Fintype.card (AddSubgroup.even edwards.Point) = 4 * L
/-- 2-descent (the Decaf criterion): the representative-level test the code and the RFC use.
Proof obligation of the backend, both directions; the old project proved only `→`. -/
theorem even_iff_isSquare (P : edwards.Point) : Even P ↔ IsSquare (1 - P.y ^ 2)
theorem even_iff_isSquare' (P) (hx : P.x ≠ 0) : Even P ↔ IsSquare (1 + d * P.y ^ 2)   -- corollary
/-- What `RistrettoPoint::ct_eq` computes. -/
theorem rel_iff_formula (P Q) : edwards.Rel P Q ↔ P.x * Q.y = P.y * Q.x ∨ P.x * Q.x = P.y * Q.y

theorem card : Fintype.card Ristretto = L
def basepoint : Ristretto := mk curve25519.basepoint even_basepoint
theorem addOrderOf_basepoint : addOrderOf basepoint = L
theorem isAddCyclic : IsAddCyclic Ristretto ; theorem zmultiples_basepoint_eq_top
end Ristretto
```

Representative-level facts that dalek specs use directly: `Rel` (equality), `Even` (validity
invariant; closed under `+`, `-`, `•` by Mathlib's `Even.add`, `Even.neg`, `Even.nsmul`), and
exact Edwards equality for arithmetic (stronger than `Rel`).

#### Implementation notes (step 4)

What was built for §7.1 and §7.2 (`EllipticCurve/TwistedEdwards/Even/Defs.lean`,
`Even/Lemmas.lean`, `Curve25519/Ristretto/Basic.lean`, additions to
`EllipticCurve/Montgomery/Lemmas.lean` and `Curve25519/Basic.lean`; no new `Proofs/` module),
and where it departs from the text:

- Files: the generic topic is the pair `Even/{Defs,Lemmas}` rather than `Even.lean`. `Defs`
  (`public import TwistedEdwards.Lemmas`, `Mathlib.Algebra.Group.Subgroup.Even`,
  `Mathlib.GroupTheory.QuotientGroup.Defs`) holds the hidden `torsion4 : AddSubgroup E.Point`
  (carrier `{P | 4 • P = 0}`) with `mem_torsion4`, the exposed `Rel P Q := P - Q ∈ E.torsion4`,
  the hidden type `EvenQuotient : Type u := ↥(AddSubgroup.even E.Point) ⧸
  E.torsion4.addSubgroupOf (AddSubgroup.even E.Point)` with its `@[no_expose] noncomputable`
  `AddCommGroup` instance, `Finite`/`Fintype` instances under `[Finite E.Point]`, the hidden
  `EvenQuotient.mk P h := QuotientAddGroup.mk ⟨P, _⟩`, and `EvenQuotient.decidableEq
  [DecidableRel E.Rel] : DecidableEq E.EvenQuotient` (a `def`, noncomputable like everything built
  on the hidden group law). `Lemmas` (`import all` of `Defs`) holds all statements; it publicly
  imports `Mathlib.SetTheory.Cardinal.Finite` (for `Nat.card`) and
  `Mathlib.Algebra.Module.Torsion.Basic` (for `torsion4_eq_torsionBy`; +0.2 s of imports).
- Generic statements: `four_nsmul_eq_zero_iff (P) : 4 • P = 0 ↔ P.x = 0 ∨ P.y = 0` (the
  4-torsion of any complete model is `{x = 0} ∪ {y = 0}`), `mem_torsion4_iff`,
  `torsion4_eq_torsionBy : E.torsion4 = (Submodule.torsionBy ℤ E.Point 4).toAddSubgroup`;
  `rel_iff_sub_mem` (`Iff.rfl`), `rel_refl`, `rel_symm`, `rel_trans`, `rel_of_eq`, `rel_add`,
  `rel_neg`, `rel_sub`, `rel_nsmul`, `rel_add_of_mem (hT : T ∈ torsion4) : Rel (P + T) P`, and
  the generic coordinate form `rel_iff (P Q) : E.Rel P Q ↔ P.x * Q.y = P.y * Q.x ∨
  P.y * Q.y + E.a * P.x * Q.x = 0`; `EvenQuotient.mk_eq_mk_iff : mk P hP = mk Q hQ ↔ E.Rel P Q`,
  `mk_surjective (q) : ∃ P h, mk P h = q`, `mk_zero`, `mk_add`, `mk_neg`, `mk_sub`, `mk_nsmul`,
  `mk_zsmul` (each takes the evenness proof of the result as a separate argument `h`, so that no
  proof term is pinned: `mk_add (hP) (hQ) (h : Even (P + Q)) : mk (P + Q) h = mk P hP + mk Q hQ`),
  `mk_eq_zero_iff : mk P hP = 0 ↔ P ∈ E.torsion4`, and the cardinality
  `card_evenQuotient_mul_card (E) : Nat.card E.EvenQuotient * Nat.card ↥(E.torsion4 ⊓
  AddSubgroup.even E.Point) = Nat.card ↥(AddSubgroup.even E.Point)`.
- The 2-descent, generic half. `Montgomery/Lemmas` gained `equation_zero_zero`,
  `v_eq_zero_of_u_eq_zero (hB : B ≠ 0)`, and the descent identities of the 2-torsion point
  `(0, 0)` for a nonsingular `M` (the descent map is `Q ↦ B u(Q)` modulo squares, not `u(Q)`: in
  Weierstrass terms `y² = x (x² + A B x + B²)` with `x = B u`; for curve25519 `B` is a square, so
  the two agree): `u_mul_u_mul_u_add_of_u_ne : u₁ u₂ u₃ (u₁ - u₂)² = B (u₁ v₂ - u₂ v₁)²` (the
  text's `((u₁u₂ − 1)/(u₁ − u₂))²` is wrong, it has no `v`s: `λ²` carries the cross term
  `v₁ v₂`), `u_zero_zero_add_mul_u : u((0, 0) + Q) · u(Q) = 1`, `B_mul_u_two_nsmul_mul_sq :
  B u(2 Q) (2 v)² = (u² - 1)²`, hence `isSquare_B_mul_u_two_nsmul (Q) : IsSquare (B * (2 • Q).u)`,
  `isSquare_B_mul_u_neg`, `isSquare_B_mul_u_add : IsSquare (B u₁) → IsSquare (B u₂) → IsSquare
  (B u(Q₁ + Q₂))` (cases `∞`, `Q₂ = -Q₁`, `Q₁ = Q₂`, `u₁ = 0` or `u₂ = 0` (translation), chord).
  The certificates are three `linear_combination`s with hand-computed coefficients, no Singular.
  `Even/Lemmas` transports this to `E`: `isSquare_toMontgomery_B_mul_u_iff (P) : IsSquare
  (E.toMontgomery.B * (E.toMontgomeryEquiv P).u) ↔ IsSquare ((E.a - E.d) * (1 - P.y ^ 2))` (as
  `B u = (2 / ((a − d)(1 − y)))² · (a − d)(1 − y²)`, both `0` at `(0, 1)`), the hidden subgroup
  `E.descent : AddSubgroup E.Point` with `mem_descent : P ∈ E.descent ↔ IsSquare ((E.a - E.d) *
  (1 - P.y ^ 2))` (closed under `+` by `isSquare_B_mul_u_add` through `map_add`; `neg_y` makes
  negation trivial), `two_nsmul_mem_descent`, `even_le_descent : AddSubgroup.even E.Point ≤
  E.descent`, `isSquare_of_even`. The generic criterion is `(a − d)(1 − y²)`, not `1 − y²`: the
  factor `a − d = 4 / B` is what makes it independent of the model's scaling; for curve25519
  `a − d = (2 / sqrtNegAAddTwo)²` (`a_sub_d_eq_sq`, `isSquare_a_sub_d`) and it disappears.
- `Curve25519/Ristretto/Basic.lean` (`public import Curve25519.Edwards.Order`; everything is
  audited, no `Proofs/Ristretto` module was needed). The 4-torsion: `eightTorsion_two_x :
  (eightTorsion 2).x = -sqrtM1` (via the new numeric fact `neg_sqrtM1_eq` in `Basic`),
  `four_nsmul_eightTorsion_eq_zero_iff (i) : 4 • eightTorsion i = 0 ↔ (i : ℕ) % 2 = 0`,
  `mem_torsion4_iff (P) : P ∈ edwards.torsion4 ↔ P = 0 ∨ P = eightTorsion 2 ∨ P = eightTorsion 4
  ∨ P = eightTorsion 6` (from `eight_nsmul_eq_zero_iff` and `fin_cases`), `eightTorsion_four_ne_zero`,
  `addOrderOf_eightTorsion_two = 4`, `torsion4_eq_zmultiples : edwards.torsion4 = zmultiples
  (eightTorsion 2)`, `card_torsion4 : Nat.card edwards.torsion4 = 4` (`Nat.card_zmultiples`).
  The even points: `even_iff_four_mul_L_nsmul (P) : Even P ↔ (4 * L) • P = 0` (`←`: from
  `exists_unique_decomposition`, `8 ∣ 4 L i` forces `i = 2 j` as `L` is odd, and
  `n • basepoint = 2 • (((L + 1) / 2 · n) • basepoint)`), `torsion4_le_even`,
  `zmultiples_torsion8_add_basepoint_eq_top`, `addOrderOf_two_nsmul_torsion8_add_basepoint = 4 L`
  (`addOrderOf_nsmul'`), `even_eq_zmultiples : AddSubgroup.even edwards.Point = zmultiples
  (2 • (torsion8 + basepoint))`, `card_even : Nat.card (AddSubgroup.even edwards.Point) = 4 * L`
  (stated with `Nat.card`, as all cardinalities of subgroups here), `even_basepoint`,
  `not_even_torsion8`. Equality: `rel_iff_formula` as in the text, and the instance
  `instDecidableRelRel : DecidableRel edwards.Rel` (computable, by the formula).
- The 2-descent, curve-specific half: `mem_descent_iff (P) : P ∈ edwards.descent ↔ IsSquare
  (1 - P.y ^ 2)`; the certificate `not_isSquare_one_sub_torsion8_y_sq` by Euler's criterion
  (`ZMod.euler_criterion`) from the numeric fact `one_sub_torsion8_y_sq_pow_p_div_two : (1 - (y_T :
  ZMod p) ^ 2) ^ (p / 2) = -1` in `Curve25519/Basic.lean` (`rw [p_eq_numeral]; norm_num;
  reduce_mod_char`, the pattern of `d_pow_p_div_two`; it elaborates in well under a second);
  `torsion8_not_mem_descent`; `descent_eq_even : edwards.descent = AddSubgroup.even edwards.Point`
  by counting (`even ≤ descent` gives `4 L ∣ |descent|`, Lagrange gives `|descent| ∣ 8 L`,
  `descent ≠ ⊤` by the certificate, so `|descent| = 4 L` and `AddSubgroup.eq_of_le_of_card_ge`);
  then `even_iff_isSquare (P) : Even P ↔ IsSquare (1 - P.y ^ 2)` (both directions, no longer a
  proof obligation), `even_iff_isSquare' (P) (hx : P.x ≠ 0) : Even P ↔ IsSquare (1 + d * P.y ^ 2)`
  (`1 − y² = (sqrtM1 · x)² (1 + d y²)`), and `even_iff_isSquare_u (P) : Even P ↔ IsSquare
  (edwards.toMontgomeryEquiv P).u`. Size: about 40 lines of generic Montgomery identities, 60
  lines of generic transport, 60 lines of curve-specific counting.
- The group: `Ristretto : Type := edwards.EvenQuotient` (hidden), instances `AddCommGroup`
  (`@[no_expose] noncomputable`), `Finite`, `Fintype` (noncomputable), `DecidableEq`
  (`EvenQuotient.decidableEq`, noncomputable); `Ristretto.mk`, `mk_eq_mk_iff`, `mk_surjective`,
  `mk_zero`, `mk_add`, `mk_neg`, `mk_sub`, `mk_nsmul`, `mk_zsmul`, `mk_eq_zero_iff` (re-exported
  from the generic ones), `card : Nat.card Ristretto = L` (from `card_evenQuotient_mul_card`
  with `torsion4 ⊓ even = torsion4`), `card_fintype : Fintype.card Ristretto = L`,
  `basepoint := mk curve25519.basepoint even_basepoint` (hidden, `basepoint_def`),
  `basepoint_ne_zero` (`4 • basepoint ≠ 0` as `L ∤ 4`), `L_nsmul_basepoint`,
  `addOrderOf_basepoint = L`, `isAddCyclic`, `zmultiples_basepoint_eq_top`.
- Numeric facts added to `Curve25519/Basic.lean`: `sqrtM1_ne_zero`, `neg_sqrtM1_eq :
  -(sqrtM1 : ZMod p) = 38214883241950591754978413199355411911188925816896391856984770930832735035197`,
  `one_sub_torsion8_y_sq_pow_p_div_two`.
- Module-system facts beyond step 3: a `theorem … := rfl` whose two sides differ by a hidden
  definition is rejected even in the `import all` module ("Not a definitional equality …
  must be exposed"), while tactic proofs (`change`, `rw [private bridge lemma]`, `exact
  map_add _ _ _`) go through; so the `mk_*` lemmas rewrite with a private `mk_eq_mk'` to
  `QuotientAddGroup.mk'` and finish with `map_zero`/`map_add`/`map_nsmul`. Names available in a
  non-module scratch file through private imports are not available in a `module` (`smul_add`,
  `smul_zero` needed `nsmul_add`, `nsmul_zero`, `neg_nsmul`; `Nat.card` needed `public import
  Mathlib.SetTheory.Cardinal.Finite`). `Set.mem_setOf_eq` is deprecated for `Set.mem_ofPred_eq`;
  `even_zero` is `Even.zero`. A `_` for a slope argument that is only determined by a later
  `by` block stays a metavariable inside that block (pass `chordSlope 0 0 u v` explicitly).
  `rw [← smul_smul]` rewrites the first `(a * b) • x` it finds; use `mul_smul a b x` with explicit
  arguments. `Nat.card_eq_fintype_card` needs `(α := edwards.Point)` when several `Nat.card`s
  are present.
- Checked: `lake build EllipticCurve --wfail`, `lake build Curve25519 --wfail`,
  `lake exe runLinter EllipticCurve`, `lake exe runLinter Curve25519` clean; `#print axioms` of
  `even_iff_isSquare`, `even_iff_isSquare'`, `even_iff_isSquare_u`, `rel_iff_formula`,
  `Ristretto.card`, `Ristretto.card_fintype`, `Ristretto.addOrderOf_basepoint`,
  `Ristretto.isAddCyclic`, `Ristretto.zmultiples_basepoint_eq_top`, `EvenQuotient.mk_eq_mk_iff`,
  `EvenQuotient.card_evenQuotient_mul_card`, `even_le_descent`, `rel_iff`,
  `four_nsmul_eq_zero_iff`, `MontgomeryModel.isSquare_B_mul_u_add`, `even_iff_four_mul_L_nsmul`,
  `card_even`, `card_torsion4`, `mem_torsion4_iff`, `descent_eq_even`,
  `not_isSquare_one_sub_torsion8_y_sq`, `instDecidableEqRistretto` are `[propext,
  Classical.choice, Quot.sound]`; from a `module` importing `Curve25519`, `unfold
  curve25519.Ristretto`, `unfold TwistedEdwardsModel.EvenQuotient` and `unfold
  TwistedEdwardsModel.torsion4` fail, `unfold TwistedEdwardsModel.Rel` works, and
  `rw [Ristretto.mk_eq_mk_iff, rel_iff_formula]` turns an equality of classes into the
  coordinate formula.

### 7.3 `Ristretto/Encoding.lean` (RFC 9496 §4.3.1–4.3.2)

Field-level helpers, exposed and computable (the dalek field specs `sqrt_ratio_i_spec`,
`is_negative_spec` must connect to them: `Defs` proves `sqrt_ratio_i` computes `sqrtRatioM1`):

```lean
namespace curve25519
/-- RFC 9496 §4.2 `SQRT_RATIO_M1(u, v)`: `(true, √(u/v))` or `(false, √(i·u/v))`, root non-negative. -/
@[expose] def sqrtRatioM1 (u v : ZMod p) : Bool × ZMod p
theorem sqrtRatioM1_spec (u v) : … (the four cases, result non-negative)   -- same shape as sqrt_ratio_i_spec
/-- The RFC constants, as field elements with the RFC's sign: `SQRT_AD_MINUS_ONE`,
`INVSQRT_A_MINUS_D`, `ONE_MINUS_D_SQ`, `D_MINUS_ONE_SQ`, `SQRT_M1`. -/
def sqrtAdMinusOne, invsqrtAMinusD, oneMinusDSq, dMinusOneSq : ZMod p ; def sqrtM1' : ZMod p := sqrtM1
theorem sqrtAdMinusOne_sq : sqrtAdMinusOne ^ 2 = a * d - 1 ; theorem not_isNeg_sqrtAdMinusOne  (etc.)

namespace Ristretto
/-- `encodeRep P`: RFC 9496 §4.3.2 on a representative; a canonical field element `< p`. -/
def encodeRep (P : edwards.Point) : ℕ
theorem encodeRep_lt (P) : encodeRep P < p
theorem encodeRep_rel (hP : Even P) (h : edwards.Rel P Q) : encodeRep P = encodeRep Q   -- coset invariance
/-- `decodeRep s`: §4.3.1; `none` iff `s ≥ p`, `s` negative, no square root, `x·y` negative or `y = 0`. -/
def decodeRep (s : ℕ) : Option edwards.Point
theorem decodeRep_eq_none_iff (s) : decodeRep s = none ↔ p ≤ s ∨ (s : ZMod p).isNeg ∨ ¬ IsSquare (…) ∨ …
theorem even_decodeRep (h : decodeRep s = some P) : Even P
theorem encodeRep_decodeRep (h : decodeRep s = some P) : encodeRep P = s
theorem decodeRep_encodeRep (hP : Even P) : ∃ Q, decodeRep (encodeRep P) = some Q ∧ edwards.Rel P Q
theorem encodeRep_eq_iff (hP : Even P) (hQ : Even Q) : encodeRep P = encodeRep Q ↔ edwards.Rel P Q

/-- Quotient level: an injection with a decidable image. -/
def encode : Ristretto → ℕ ; theorem encode_mk (hP) : encode (mk P hP) = encodeRep P
def decode : ℕ → Option Ristretto ; theorem decode_eq_some_iff : decode s = some x ↔ encode x = s
theorem encode_injective ; theorem decode_encode (x) : decode (encode x) = some x
theorem encode_basepoint : encode basepoint = RISTRETTO_BASEPOINT_COMPRESSED (numeral)
theorem encode_zero : encode 0 = 0
end Ristretto
```

### 7.4 `Ristretto/Map.lean` (RFC 9496 §4.3.4)

```lean
namespace curve25519.Ristretto
/-- `MAP(r)`, the Elligator-style map of a field element to an even point. -/
def mapRep (r : ZMod p) : edwards.Point
theorem even_mapRep (r) : Even (mapRep r)
theorem mapRep_x, mapRep_y (r) : … (the RFC formulas, with the `sqrtRatioM1` case split)
def map (r : ZMod p) : Ristretto := mk (mapRep r) (even_mapRep r)
/-- One-way map from 64 uniform bytes (§4.3.4): `MAP(r₀) + MAP(r₁)`, each half masked to 255 bits. -/
def fromUniformRep (n : ℕ) : edwards.Point := mapRep (decodeU (n % 2^256)) + mapRep (decodeU (n / 2^256))
def fromUniform (n : ℕ) : Ristretto
theorem fromUniform_eq_mk …
end curve25519.Ristretto
```

The on-curve proof of `mapRep` (the old project's `sorry`) is backend work; the API only needs
`even_mapRep` and the coordinate formulas.

#### Implementation notes (step 8)

What was built for §7.3 and §7.4 (`Curve25519/Ristretto/Encoding/Defs.lean`,
`Curve25519/Ristretto/Encoding.lean`, `Curve25519/Ristretto/Map.lean`, the non-audited
`Curve25519/Proofs/Ristretto/{Algebra,Elligator,Certs,TestVector,MapVector}.lean`, additions to
`Curve25519/Basic.lean` and `EllipticCurve/Field/Sign.lean`, the `Curve25519` root), and where
it departs from the text:

- **Layout.** The encoding topic is the pair `Ristretto/Encoding/Defs.lean` (the hidden
  definitions, `sqrtRatioM1` and its lemmas) and `Ristretto/Encoding.lean` (`import all` of
  `Defs`: every property, the quotient level, the basepoint), so that the certificate module
  `Proofs/Ristretto/Certs.lean` can `import all` the definitions and evaluate `encodeRep` on
  numerals. `Ristretto/Map.lean` is a single module (its own hidden `mapRep` and the lemmas about
  it). The pure field identities are `Proofs/Ristretto/Algebra.lean` (decoding/encoding, stated
  with the square roots as hypotheses `W r² = 1`; imported privately by `Encoding/Defs` for the
  on-curve proof of `decodeRep`, re-exported there as `decodeRep_equation`) and
  `Proofs/Ristretto/Elligator.lean` (`ell_good`, the port of the old project's Elligator algebra
  with the branch data abstracted). Everything else is proved in the audited modules.
- **Constants** are hidden natural numbers in `Curve25519/Basic.lean`, like `sqrtM1` and
  `sqrtNegAAddTwo` (so that `_lt_p` and the parity make sense), not `ZMod p` values in
  `Ristretto/Encoding`: `sqrtAdMinusOne`, `invsqrtAMinusD`, `oneMinusDSq`, `dMinusOneSq`, each
  with `_def`, `_lt_p`, and `sqrtAdMinusOne_sq : (sqrtAdMinusOne : ZMod p) ^ 2 = a * d - 1`,
  `sqrtAdMinusOne_ne_zero`, `invsqrtAMinusD_sq_mul : (invsqrtAMinusD : ZMod p) ^ 2 * (a - d) = 1`,
  `invsqrtAMinusD_ne_zero`, `oneMinusDSq_eq : (oneMinusDSq : ZMod p) = 1 - d ^ 2`,
  `dMinusOneSq_eq : = (d - 1) ^ 2` (all `rw [p_eq_numeral]; push_cast; reduce_mod_char`).
  **The RFC's `SQRT_AD_MINUS_ONE` is odd**, i.e. negative (`sqrtAdMinusOne_mod_two : % 2 = 1`;
  the text's `not_isNeg_sqrtAdMinusOne` is false; nothing needs its sign: it only enters squared),
  while `INVSQRT_A_MINUS_D` is even (`invsqrtAMinusD_mod_two : % 2 = 0`; its sign matters for
  byte-exactness of `compress`, §7.5). Also `sqrtM1_mod_two : sqrtM1 % 2 = 0` and
  `sqrtM1_pow_p_div_two : (sqrtM1 : ZMod p) ^ (p / 2) = -1` (`p ≡ 5 (mod 8)`), whence
  `not_isSquare_sqrtM1` (Euler's criterion) in `Encoding/Defs`, with `not_isSquare_neg_d`,
  `isSquare_sqrtM1_mul_of_not_isSquare (hx : ¬ IsSquare x) : IsSquare (sqrtM1 * x)` (via
  `ZMod.pow_div_two_eq_neg_one_or_one`) and `not_isSquare_sqrtM1_mul_sq (hr : r ≠ 0)`.
- **`sqrtRatioM1`** (`Encoding/Defs`, exposed but `noncomputable`: the root is
  `(Classical.choose h).abs` for `h : IsSquare (u / v)`, resp. of `IsSquare (sqrtM1 * (u / v))`;
  the text's "computable" is not achievable without a square-root algorithm, and nothing needs it:
  the kernel never evaluates it, certificates exhibit the root as a numeral and use the uniqueness
  lemmas). Statements: `sqrtRatioM1_of_v_eq_zero : v = 0 → sqrtRatioM1 u v = (decide (u = 0), 0)`,
  `sqrtRatioM1_zero_zero`, `sqrtRatioM1_zero_right (hu : u ≠ 0) : sqrtRatioM1 u 0 = (false, 0)`,
  `sqrtRatioM1_zero_left (v) : sqrtRatioM1 0 v = (true, 0)`, `sqrtRatioM1_of_isSquare (hv : v ≠ 0)
  (h : IsSquare (u / v)) : (sqrtRatioM1 u v).1 = true ∧ v * (sqrtRatioM1 u v).2 ^ 2 = u`,
  `sqrtRatioM1_of_not_isSquare (hv) (h : ¬ …) : .1 = false ∧ v * r ^ 2 = sqrtM1 * u`,
  `not_isNeg_sqrtRatioM1_snd`, `sqrtRatioM1_spec (u v)` (the conjunction of the four cases and the
  sign, the shape of `sqrt_ratio_i_spec`), `sqrtRatioM1_fst_iff : (sqrtRatioM1 u v).1 = true ↔
  u = 0 ∨ (v ≠ 0 ∧ IsSquare (u / v))`; the **uniqueness lemmas** that the dalek `Defs` layer will
  use to identify `sqrt_ratio_i`'s output: `sqrtRatioM1_eq_of_mul_sq_eq (hv : v ≠ 0) (hr : v * r ^ 2
  = u) (hneg : ¬ r.isNeg) : sqrtRatioM1 u v = (true, r)` and
  `sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul (hu : u ≠ 0) (hv) (hr : v * r ^ 2 = sqrtM1 * u) (hneg) :
  = (false, r)`; the inverse square root `sqrtRatioM1 1 v`: `sqrtRatioM1_one_zero = (false, 0)`,
  `sqrtRatioM1_one_fst_iff : (sqrtRatioM1 1 v).1 = true ↔ v ≠ 0 ∧ IsSquare v`,
  `sqrtRatioM1_one_of_isSquare (hv) (h) : v * (sqrtRatioM1 1 v).2 ^ 2 = 1`,
  `sqrtRatioM1_one_of_fst (h : (sqrtRatioM1 1 v).1 = true) : v * … = 1`,
  `sqrtRatioM1_one_eq_of_mul_sq_eq (hr : v * r ^ 2 = 1) (hneg) : sqrtRatioM1 1 v = (true, r)`.
- **`decodeRep`** (hidden, `Option edwards.Point`): `none` unless `s < p ∧ ¬ (s : ZMod p).isNeg`
  (so `s ≥ 2^255` is rejected by `s ≥ p`); then the RFC's `let`-chain with
  `r := (sqrtRatioM1 1 (v u2²)).2`, `x := |2 s' (r u2)|`, `y := u1 (r (r u2) v)`, and `some ⟨x, y,
  decodeRep_equation …⟩` iff `(sqrtRatioM1 1 (v u2²)).1 = true ∧ ¬ (x y).isNeg ∧ y ≠ 0`. No `_def`
  (the body carries the on-curve proof); instead the exact characterisations
  `decodeRep_eq_none_iff (s) : decodeRep s = none ↔ p ≤ s ∨ (s : ZMod p).isNeg ∨ let … ;
  (sqrtRatioM1 1 (v * u2 ^ 2)).1 = false ∨ (x * y).isNeg ∨ y = 0` (the RFC's rejection reasons,
  the intermediates as `let`s in the statement) and `decodeRep_eq_some_iff : decodeRep s = some P
  ↔ s < p ∧ ¬ (s : ZMod p).isNeg ∧ P.y = (1 - s'^2) / (1 + s'^2) ∧ ¬ P.x.isNeg ∧ ¬ (P.x * P.y).isNeg
  ∧ P.y ≠ 0` (`s' := (s : ZMod p)`; the direction `←` is the Decaf decoding correctness: `v ≠ 0`
  always (`decode_v_ne_zero`, a zero would make `-d` a square), `x² v = 4 s²` for any point with
  `y = u1/u2` (`x_sq_mul_v_eq`), so `v u2²` is a nonzero square — `(2 s u2 / x)²`, or `-d - 1 =
  sqrtAdMinusOne²` at `x = 0` — and the decoded `|2 s r u2|` is `x` by sign). Corollaries:
  `decodeRep_lt`, `not_isNeg_of_decodeRep`, `decodeRep_y`, `not_isNeg_decodeRep_x`,
  `not_isNeg_decodeRep_xy`, `decodeRep_y_ne_zero`, `one_add_sq_ne_zero_of_decodeRep`,
  `decodeRep_y_ne_neg_one`, `decodeRep_x_sq (h) : P.x ^ 2 * (-(d * (1 - s'^2)^2) - (1 + s'^2)^2) = 4
  * s'^2` (the text's `x² = 4 s² / (…)`, without the division), `even_decodeRep` (`1 - y² = (2 s /
  (1 + s²))²`), `decodeRep_zero : decodeRep 0 = some 0`.
- **`encodeRep`** (hidden, `ℕ`): the RFC's `let`-chain on `(x, y, 1, x y)`, result
  `(denInv * (1 - y'')).abs.val`; `encodeRep_def` (`fun` form) and `encodeRep_eq (P)` (applied)
  restate the body (the kernel can evaluate it on numerals once `sqrtRatioM1 1 W` is rewritten
  to `(true, r)`). Statements: `encodeRep_lt (P) : encodeRep P < p`, `not_isNeg_encodeRep (P)`,
  `encodeRep_of_mul_eq_zero (h : P.x * P.y = 0) : encodeRep P = 0` (the 4-torsion: `W = 0`,
  `sqrtRatioM1 1 0 = (false, 0)`, everything collapses), `encodeRep_zero`, the round trips
  `encodeRep_decodeRep (h : decodeRep s = some P) : encodeRep P = s` and `decodeRep_encodeRep (hP
  : Even P) : ∃ Q, decodeRep (encodeRep P) = some Q ∧ edwards.Rel P Q`, the invariance
  `encodeRep_rel (hP : Even P) (h : edwards.Rel P Q) : encodeRep P = encodeRep Q` and
  `encodeRep_eq_iff (hP) (hQ) : encodeRep P = encodeRep Q ↔ edwards.Rel P Q`. Nothing is missing.
- **Proof of the round trips and the invariance** (all in `Encoding.lean`, through the
  canonical representative). The classes in coordinates: `rel_iff_coords (P Q) : edwards.Rel P Q
  ↔ (Q.x = P.x ∧ Q.y = P.y) ∨ (Q.x = -P.x ∧ Q.y = -P.y) ∨ (Q.x = P.y * sqrtM1 ∧ Q.y = P.x * sqrtM1)
  ∨ (Q.x = -(P.y * sqrtM1) ∧ Q.y = -(P.x * sqrtM1))` (the translates by `eightTorsion 4, 6, 2`,
  from `curve25519.mem_torsion4_iff` and `add_x`/`add_y`; the converse by `rel_iff_formula`),
  `eq_of_rel_of_canonical`: two related points with `x` and `x y` non-negative, `y ≠ 0` and
  `y ≠ -1` are equal (the four cases are one line each: `-x` and `x` both non-negative forces
  `x = 0`, then `y = ±1`; a rotation negates `x y`), `even_of_rel`. The encoder, for an even `P`
  with `x y ≠ 0`: `W = (1 + y)(1 - y)(x y)²` is a nonzero square (`even_iff_isSquare`), so
  `W I² = 1` and `z_inv = 1`; private `xRot`, `yRot` (the rotated point `(y √-1, x √-1)` when
  `x y` is negative), `yC` (negated when `xRot` is negative) and `denC` give `encodeRep P =
  (denC P * (1 - yC P)).abs.val` with `denC² (1 - yC²) = 1` (`enc_den2_sq`, and `enc_den1_sq`
  for the rotated branch: `(I u1 K)² (1 + x²) = 1` from `K² (a - d) = 1` and the curve equation,
  `(1 - y²)(1 + x²) = -x² y² (1 + d)`); `exists_canon (P) : ∃ C, Rel P C ∧ C.x = (xRot P).abs ∧
  C.y = yC P` (one of the four translates), and `C` is canonical (`not_isNeg_abs_xRot_mul_yC`,
  `yC_ne_zero`). Then `decodeRep_encodeRep` is `decodeRep_eq_some_iff` at `C` with `S² = (1 -
  y_C)/(1 + y_C)` (`sq_eq_div_of`, `div_eq_of_sq_eq_div`); `encodeRep_decodeRep` notes that a
  decoded point has `rotate = false` and no sign flip, so `S² = (1 - y)/(1 + y) = s'²` and `S = s'`
  by sign (`x = 0` gives `y = 1`, `s = 0`); `encodeRep_rel` decodes both encodings to canonical
  representatives of one class, equal by `eq_of_rel_of_canonical`, and `encodeRep_eq_iff`
  follows. The old project's `IsCanonicalRistrettoRep` (`x`, `x y` non-negative, `y ≠ 0`) is not
  enough for uniqueness: `(0, 1)` and `(0, -1)` both satisfy it; `y ≠ -1` is the missing clause
  (a decoded `y = (1 - s²)/(1 + s²)` is never `-1`).
- **Quotient level**: `encode (x : Ristretto) : ℕ := encodeRep (Classical.choose (mk_surjective
  x))` (hidden; `encode_mk (hP) : encode (mk P hP) = encodeRep P` by `encodeRep_rel`),
  `encode_lt`, `not_isNeg_encode`, `decode (s) : Option Ristretto` (hidden: `some (mk (choose h) …)`
  if `h : ∃ P, decodeRep s = some P`, else `none`), `decode_eq_some_iff_decodeRep : decode s = some
  x ↔ ∃ P (h : decodeRep s = some P), mk P (even_decodeRep h) = x`, `decode_eq_none_iff : decode s
  = none ↔ decodeRep s = none`, `decode_eq_some_iff : decode s = some x ↔ encode x = s`,
  `decode_encode`, `encode_decode`, `encode_injective`, `encode_inj`, `decode_isSome_iff : (decode
  s).isSome ↔ ∃ x, encode x = s`, `encode_zero : encode 0 = 0`, `decode_zero`, and the basepoint:
  `encodeRep_basepoint`, `encode_basepoint : encode basepoint =
  53453403443306840533278073560698739391446669128918427283046925944918568268514` (RFC 9496 §A.1
  `e2f2ae0a 6abc4e71 a884a961 c500515f 58e30b6a a582dd8d b6a65945 e08d2d76`, little-endian; the
  inverse square root of `W` at the basepoint is the numeral
  `52572753176437111631691385822184065804252865134316606714987751091199353072154`; the
  basepoint's class is encoded through its *rotated* canonical representative, as `x y` is odd),
  `decode_basepoint`. Note the name clash under `open curve25519 curve25519.Ristretto`:
  `Ristretto.encode`/`decode`/`basepoint` versus the Edwards `curve25519.encode`/`decode`/
  `basepoint`; use qualified names.
- **`Map.lean`**: `mapRep (r₀ : ZMod p) : edwards.Point` (hidden) is the RFC's `let`-chain
  (`r = √-1 r₀²`, `u = (r + 1) oneMinusDSq`, `v = (-1 - r d)(r + d)`, `s`, `c`,
  `N = c (r - 1) dMinusOneSq - v`) with the affine point `(2 s v / (N sqrtAdMinusOne),
  (1 - s²)/(1 + s²))`, i.e. the RFC's `(w0 w3 : w2 w1 : w1 w3 : w0 w2)` as `(w0/w1, w2/w3)`; the
  on-curve proof is the public `mapRep_equation (r₀) : let …; edwards.Equation (…) (…)`, from the
  private `map_facts` (`ell_good` at the branch data: `v = 0` gives `s = 0`, `c = r`; a square
  gives `s² v = u`, `c = -1`; otherwise `s = -|ρ r₀|` with `v ρ² = √-1 u`, so `s² v = r u`, `c = r`;
  and `u ≠ 0` since `r = -1` would make `√-1` a square). Statements, all with the intermediates as
  `let`s: `mapRep_x : (mapRep r₀).x = let …; 2 * s * v / (N * sqrtAdMinusOne)`, `mapRep_y : … =
  (1 - s ^ 2) / (1 + s ^ 2)`, `mapRep_den_ne_zero : let …; N * sqrtAdMinusOne ≠ 0`,
  `mapRep_one_add_sq_ne_zero : let …; 1 + s ^ 2 ≠ 0`, `even_mapRep` (`1 - y² = (2 s/(1 + s²))²`);
  `map (r₀) := mk (mapRep r₀) (even_mapRep r₀)` (hidden, `map_def`, `mk_mapRep`);
  `fromUniformRep (n) := mapRep (decodeU (n % 2 ^ 256)) + mapRep (decodeU (n / 2 ^ 256))` (hidden,
  `fromUniformRep_def`, `even_fromUniformRep`), `fromUniform (n) := mk (fromUniformRep n) …`
  (hidden, `fromUniform_def`, `mk_fromUniformRep`, `fromUniform_eq_mk`, `fromUniform_eq_add_map :
  fromUniform n = map (decodeU (n % 2 ^ 256)) + map (decodeU (n / 2 ^ 256))`). A `let`-chain in a
  statement zeta-reduces under `dsimp only`/`simp only`, and `exact`/`rfl` see through it; it was
  preferred to exposing six helper definitions.
- **Certificates and test vectors** (`decide +kernel`, `import all Curve25519.Basic` so that the
  kernel unfolds `p`, `sqrtM1` and the constants; `d` is never evaluated: its inverse would need
  `Nat.gcdA`'s well-founded recursion, so it is first rewritten to its numeral by
  `d_eq_natCast`): `Proofs/Ristretto/Certs.lean` (the basepoint: the root numeral and
  `sqrtRatioM1_one_eq_of_mul_sq_eq`, then one kernel evaluation of the rest of `encodeRep_eq`;
  1.2 s for the module), `Proofs/Ristretto/TestVector.lean` (RFC 9496 §A.1: `encode (k •
  basepoint)` for `k = 2, …, 15`, coordinates of `k • B` by a `ProjEq` check of `Extended.nsmul`
  as in `Proofs/Edwards/Certs`; 1.4 s) and `Proofs/Ristretto/MapVector.lean` (RFC 9496 §A.3, the
  seven one-way-map vectors as `encode (fromUniform (lo + 2 ^ 256 * hi)) = …`, both branches of
  `sqrtRatioM1` occurring: the root numeral and the uniqueness lemmas, the coordinates of
  `mapRep` by `div_eq_iff` and the kernel, the sum by `add_x`/`add_y`, the encoding as above;
  2.3 s). The last two are imported privately by the root, like `Proofs/X25519/TestVector`. All
  21 vectors of RFC 9496 §A.1 and §A.3 check (they were also reproduced in Python first).
- **`Field/Sign`** additions: `eq_zero_of_not_isNeg_of_not_isNeg_neg (hp) (h : ¬ x.isNeg) (h' : ¬
  (-x).isNeg) : x = 0`, `abs_eq_abs_of_sq_eq (hp) (h : x ^ 2 = y ^ 2) : x.abs = y.abs`,
  `eq_abs_of_sq_eq_of_not_isNeg (hp) (h : x ^ 2 = y ^ 2) (hx : ¬ x.isNeg) : x = y.abs`.
- Module-system and tactic facts beyond step 7: `rw … at hc` fails when `Classical.choose h`
  occurs and `h`'s type contains the rewritten term (motive): prove `Classical.choose h = 0`
  separately and rewrite the goal; `obtain ⟨P, hP⟩ := h` is refused when `Classical.choose h` is
  in the goal (destructure after `iff_of_false`); `exact Option.noConfusion h` for `h : none =
  some P` fails on universes, `cases h` works; `exact two_ne_zero (by linear_combination …)`
  elaborates the `by` block before the instance is known (name the `have`); `simp only […,
  reduceIte, and_self]` decides `if true = true` and `if false = true` (`Bool.false_eq_true`);
  `set x := e` without `with` when the equation is not needed; `Nat.cast_ofNat` turns `((n : ℕ) :
  ZMod p)` into the numeral; Lake rebuilds by content hash, so `touch` does not re-elaborate
  (timings were taken with `lake env lean`: every new module elaborates in 1.2–2.3 s, ≤ 1.5 GB).
- Checked: `LEAN_NUM_THREADS=8 lake build Curve25519 --wfail`, `lake build EllipticCurve
  --wfail`, `lake exe runLinter Curve25519`, `lake exe runLinter EllipticCurve` clean; `#print
  axioms` of `sqrtRatioM1_spec`, `sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul`, `even_decodeRep`,
  `decodeRep_eq_some_iff`, `decodeRep_eq_none_iff`, `encodeRep_decodeRep`, `decodeRep_encodeRep`,
  `encodeRep_rel`, `encodeRep_eq_iff`, `encode_injective`, `decode_encode`, `decode_eq_some_iff`,
  `even_mapRep`, `mapRep_equation`, `mapRep_x`, `encode_basepoint`, `encodeRep_basepoint`,
  `decode_basepoint`, `fromUniform_eq_add_map`, `not_isSquare_sqrtM1`, `rel_iff_coords`,
  `eq_of_rel_of_canonical`, and of the test vectors `encode_two_nsmul_basepoint`,
  `encode_fifteen_nsmul_basepoint`, `fromUniform_vector₁`, `fromUniform_vector₇` are `[propext,
  Classical.choice, Quot.sound]` (no `Lean.ofReduceBool`); from a `module` importing `Curve25519`,
  `unfold Ristretto.decodeRep`, `unfold Ristretto.encodeRep`, `unfold Ristretto.mapRep` and
  `unfold Ristretto.encode` fail, `unfold sqrtRatioM1` works, `rw [Ristretto.decode_eq_some_iff]`,
  `rw [Ristretto.mapRep_y]; dsimp only` and `Ristretto.decode_encode` work.

### 7.5 Dalek-facing summary (what `Defs` will add; see §9)

- `RistrettoPoint` is `EdwardsPoint`; its invariant is `P.OnCurve ∧ Even P.toPoint` (Mathlib's
  `Even`), kept separate from the bounds; no new predicate.
- `CompressedRistretto.asNat`; a `decompress` spec reads
  `r.map toPoint = Ristretto.decodeRep bytes.asNat ∧ ∀ q, r = some q → q.OnCurve ∧ q.Bounded`,
  `compress` reads `r.asNat = Ristretto.encodeRep self.toPoint`, `ct_eq` reads
  `c = 1 ↔ edwards.Rel self.toPoint other.toPoint`, arithmetic reads exact Edwards equality
  plus `Even`.
- Byte-exactness of `compress` against the RFC needs the constants' **signs**; the existing
  dalek constant specs (`INVSQRT_A_MINUS_D_spec : r² (a−d) = 1`) will gain a `¬ isNeg` conjunct
  at the campaign stage (statement change: owner sign-off).

## 8. Conventions for hidden definitions and `decide`

- A hidden definition cannot be unfolded by ordinary importers, not even by the kernel. Modules
  that need the bodies use `import all` on the definitions module (principle 2): that is where
  every certificate check lives (`basepoint.equation`, `8 • torsion8 = 0`,
  `addOrderOf basepoint = L`, cardinalities), typically a `Proofs/*.lean` module whose results
  the audited properties module re-exports. Everyone else works through the lemmas or through the
  exposed computable functions (`addX`, `addY`, `nsmulBinary`, `ladder`). The dalek constants
  proofs (in `Proofs/…/Constants/*`) compare limbs against `basepoint_x_eq`-style numerals, never
  by unfolding `basepoint`, and are not given `import all` access to `Curve25519`.
- Layout per topic, e.g. `TwistedEdwards/Group/Defs.lean` (hidden `add`, the instance),
  `TwistedEdwards/Group/Lemmas.lean` (`import all …/Defs`; `add_x`, `add_y`, …, audited
  statements), `Proofs/TwistedEdwards/Group.lean` (`import all …/Defs`; the transport or
  certificate proof of the group axioms, not audited). The module list in §2 names the topics;
  each expands to this pair or triple.
- Exposed (`@[expose]`): `Equation`, `OnCurve`, `ProjEq`, `isNeg`, `rhs`, the coordinate formulas
  (`addX`, `addY`, `addDen₁`, `addDen₂`, `nsmulBinary`, `xDBL`, `xADD`, `ladder`, `clamp`,
  `decodeU`, `encodeU`, `x25519`, `XZ.toU`). Hidden: everything whose construction may change
  (`Point` instances, `toPoint`, `toMontgomeryEquiv`, `xMul`, `encode`/`decode`, `basepoint`,
  `torsion8`, `toWeierstrass`).
- Every hidden definition that is *data* gets a `_def` lemma unless its construction is meant to
  be swappable (then only characterisation lemmas: this is the case for the group instance,
  `toPoint`, `toMontgomeryEquiv`, `xMul`).
- Naming: Mathlib style (`addOrderOf_basepoint`, `u_neg`, `toPoint_double`); coordinate
  structures named after `curve_models.rs`. "Curve" in a type name is reserved for the abstract
  object; models are `…Model`.

## 9. What `Defs` adds on top (dalek layer, for later)

```lean
def FieldElement51.toField (x : FieldElement51) : ZMod p := (x.asNat : ZMod p)
def EdwardsPoint.toExtended (P : EdwardsPoint) : edwards.Extended := ⟨P.X.toField, P.Y.toField, P.Z.toField, P.T.toField⟩
@[expose] def EdwardsPoint.OnCurve (P) : Prop := P.toExtended.OnCurve
def EdwardsPoint.toPoint (P) : edwards.Point := P.toExtended.toPoint
@[expose] def EdwardsPoint.Bounded (P) : Prop := ∀ i < 5, P.X[i]!.val < 2^52 ∧ …   -- separate
-- likewise ProjectivePoint/CompletedPoint/ProjectiveNielsPoint/AffineNielsPoint/AffinePoint → §4.3 coordinate types
-- tables: LookupTable.Represents t P := ∀ j, t[j].OnCurve ∧ t[j].toPoint = (j+1) • P
-- bytes: CompressedEdwardsY.asNat, MontgomeryPoint.u := decodeU bytes.asNat, lenient decoder
-- Ristretto: invariant `Even P.toPoint` (Mathlib); CompressedRistretto.asNat
```

#### Implementation notes (Defs layer)

What was built for §9 (`Defs/{FieldElement51,CurveModels,Edwards,Montgomery,Ristretto,Window,
ScalarMul}.lean`, `Proofs/Helpers/{ToField,Coords,Edwards}.lean`; roots `Defs.lean`,
`Proofs.lean`), and where it departs from the text:

- **Naming and hiding.** Everything lives in the namespace of the Aeneas type and is used with
  dot notation (`self.toExtended`, `self.OnCurve`, `t.Represents P`). Data definitions are
  hidden with a `_def` lemma (`toExtended_def`, `toPoint_def`, `asNat_def`, `u_def`, `toXZ_def`,
  `decodeLenient_def`); the `Prop`s `OnCurve`, `Bounded`, `ProjEq`, `Represents` are
  `@[expose]`. The maps to the coordinate types and the `toPoint`s are `noncomputable` (their
  types mention the hidden `p`; `Montgomery.toPoint` of the library is noncomputable anyway);
  `MontgomeryPoint.u` is computable (`decodeU` is).
- **Both x86_64 configurations.** The structures `«x86_64-tables»` and `«x86_64-no-tables»` are
  distinct types, so every definition and every `Coords` lemma appears twice with identical
  bodies (the files are generated from one template; nothing is shared through a class except
  the table entries, below). The i686 structures (u32 limbs) get nothing.
- **`FieldElement51.toField : ZMod p := (self.asNat : ZMod p)`** (`Defs/FieldElement51`, which
  now imports `Curve25519.Basic`). The bridge from the field specs' `asNat % p` form is
  `Proofs/Helpers/ToField.lean`, one lemma per spec shape: `toField_mul_of_mod`,
  `toField_sq_of_mod`, `toField_two_mul_sq_of_mod`, `toField_pow_of_mod`,
  `toField_add_of_limbs` (the limbwise `add_spec`), `toField_sub_of_mod`, `toField_neg_of_mod`,
  `toField_inv_of_mod` (`invert`, with `0⁻¹ = 0`), `toField_eq_of_mod_eq` (`reduce`),
  `toField_eq_decodeU_of_asNat_eq` (`from_bytes`), `toField_val`/`asNat_eq_val_of_mod`
  (`to_bytes`), `eq_one_iff_isNeg_toField` (`is_negative`), `eq_one_iff_toField_eq_zero`
  (`is_zero`), `eq_one_iff_toField_eq` (`ct_eq`), `exists_sq_mul_mod_iff_isSquare_div` (the
  `∃ x : ℕ, x² v ≡ u` tests), `toField_eq_toField_iff`, `toField_eq_zero_iff`,
  `limbs_lt_of_le`, and the two uniqueness results `sqrtRatioM1_eq_of_spec`,
  `sqrtRatioM1_one_eq_of_spec`: the conjuncts of `sqrt_ratio_i_spec` (resp. `invsqrt_spec`) give
  `sqrtRatioM1 u.toField v.toField = (decide (c = 1#u8), r.toField)` (resp. `sqrtRatioM1 1 …`),
  the §7.3 obligation "`sqrt_ratio_i` computes `sqrtRatioM1`".
- **`curve_models.rs`** (`Defs/CurveModels`): `ProjectivePoint.toProjective`,
  `CompletedPoint.toCompleted`, `AffineNielsPoint.toAffineNiels`
  (`⟨y_plus_x, y_minus_x, xy2d⟩`), `ProjectiveNielsPoint.toProjectiveNiels`
  (`⟨Y_plus_X, Y_minus_X, Z, T2d⟩`), each with `OnCurve := (toX self).OnCurve`,
  `toPoint := (toX self).toPoint` and `Bounded` as one conjunction of per-field bounds
  `∀ i < 5, self.X[i]!.val < 2 ^ k`: `k = 52` for `ProjectivePoint`, `54` for `CompletedPoint`
  and both Niels forms (`curve-requirements.md` Q2). `Inhabited` instances for the Niels
  structures and `EdwardsPoint` (needed by `t[j]!`, as `instInhabitedScalar`).
- **`edwards.rs`** (`Defs/Edwards`): `EdwardsPoint.toExtended`, `OnCurve`, `toPoint`,
  `Bounded` (all four `< 2^52`), `ProjEq self other := self.toExtended.ProjEq other.toExtended`;
  `affine.AffinePoint.OnCurve := edwards.Equation x.toField y.toField`, `toPoint` (the point,
  else `0`; `toPoint_def` is a `dite` under `open scoped Classical`), `Bounded` (`< 2^52`);
  `CompressedEdwardsY.asNat := Array.asNat 8 self`; `decodeLenient n` as in the text
  (`y := n % 2^255` cast, sign `n / 2^255`, `some ⟨x, y, _⟩` for the `x` with
  `Equation x y ∧ (x = 0 ∨ (x.isNeg ↔ n / 2^255 = 1))`, else `none`; `Classical.choose`, as
  the library's `decode`). Its lemmas are `Proofs/Helpers/Edwards.lean`:
  `decodeLenient_eq_some_iff` (`P.y = y ∧ (P.x = 0 ∨ (P.x.isNeg ↔ s = 1))`),
  `decodeLenient_eq_none_iff` (`¬ IsSquare (xSq y)`), `decodeLenient_isSome_iff`,
  `decodeLenient_eq_decode_of_canonical (hn : n < 2^256) (hy : n % 2^255 < p)
  (hs : ¬ (y² = 1 ∧ s = 1))`, `decodeLenient_encode`, `encode_of_decodeLenient` (same
  canonicity hypotheses, with `¬ (P.x = 0 ∧ s = 1)`), `decodeLenient_y`,
  `decodeLenient_x_eq_zero_or_isNeg_iff`.
- **Basepoint tables** (`Defs/Edwards`, `«x86_64-tables»` only: the no-tables configuration has
  no such types). `BasepointTable::create` stores `table.0[i] = LookupTable::from(&P)` with
  `P = (2^(2w))^i • B` (`P.mul_by_pow_2(radix + radix)` after each row), so
  `EdwardsBasepointTable.Represents self P := ∀ i < 32, (self[i]!).Represents (2 ^ (8 * i) • P)`
  (radix 16, `w = 4`), and `2 ^ (10 * i)`, `2 ^ (12 * i)`, `2 ^ (14 * i)`, `2 ^ (16 * i)` for
  `Radix32`, `Radix64`, `Radix128`, `Radix256` (`w = 5, 6, 7, 8`): entry `j` of row `i` is
  `(j + 1) • 2^(2 w i) • P`. `Bounded` likewise row by row. (For `w ≥ 5` and large `i` the
  exponent exceeds Lean's evaluation threshold `256`; proofs keep `2 ^ (2 w i)` symbolic.)
- **`window.rs`** (`Defs/Window`): the entry types are abstracted by a class
  `Curve25519Dalek.PointRepr T` with fields `OnCurve`, `toPoint`, `Bounded`, instantiated by the
  four Niels structures (instances forward to the definitions of `Defs/CurveModels`), so that
  each table predicate is stated once: `LookupTable.Represents t P := ∀ j < 8,
  PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P` and
  `LookupTable.Bounded t := ∀ j < 8, PointRepr.Bounded t[j]!`, the same with `16/32/64/128`
  for `LookupTableRadix32/64/128/256`, and `(2 * k + 1) • P` over `8`/`64` entries for
  `NafLookupTable5`/`NafLookupTable8`. This is the "generic helper" of the text; a spec about a
  concrete table reads e.g. `(t : LookupTable AffineNielsPoint.«x86_64-tables»).Represents P`
  and unfolds through the instance.
- **Precomputations** (`Defs/ScalarMul`, requirements R10):
  `VartimePrecomputedStraus.Represents self ps := List.Forall₂ NafLookupTable8.Represents
  self.static_lookup_tables.val ps` (same length, table `i` is the NAF table of `ps[i]`), and
  `Bounded`; the backend enum `backend.VartimePrecomputedStraus` (single variant `Scalar`) gets
  the same two predicates by pattern matching, and its alias `edwards.VartimeEdwardsPrecomputation`
  needs nothing (dot notation unfolds the alias).
- **`montgomery.rs`** (`Defs/Montgomery`): `MontgomeryPoint.asNat` (added, for the canonical
  output of `to_montgomery`/`to_bytes`) and `MontgomeryPoint.u := decodeU self.asNat`;
  `ProjectivePoint.toXZ : MontgomeryModel.XZ (ZMod p) := ⟨U.toField, W.toField⟩` and
  `Bounded` with **`< 2^52`**: `differential_add_and_double` adds `U ± W` before squaring or
  multiplying, so it needs inputs `< 2^53`, and every producer (`identity = (ONE, ZERO)`,
  `from_bytes` (`< 2^51`), the `mul`/`square` outputs of the step) gives `< 2^52`; `< 2^52`
  is the output bound of every field operation and matches the Edwards structures. The
  `Coords` lemma `toXZ_toU : self.toXZ.toU = U.toField / W.toField` is `as_affine`'s meaning
  (`0` at `W = 0`).
- **`ristretto.rs`** (`Defs/Ristretto`, a separate file rather than inside `Defs/Edwards`):
  only `CompressedRistretto.asNat`; `RistrettoPoint` keeps `EdwardsPoint`'s definitions with the
  invariant `self.OnCurve ∧ Even self.toPoint` (§7.5).
- **`Proofs/Helpers/Coords.lean`**: for every structure, `onCurve_iff` (`Iff.rfl`),
  `onCurve_iff_equation` (on the limbs' values), `onCurve_iff_homogeneous` (with `a`, `d` of
  `curve25519`), `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`; the Niels coordinates
  `toAffineNiels_x/y`, `toProjectiveNiels_X/Y`; `EdwardsPoint.projEq_iff` (the coordinate form)
  and `projEq_iff_toPoint_eq`, `ProjectivePoint.projEq_iff_toPoint_eq`;
  `AffinePoint.toPoint_eq_mk`, `toExtended_toPoint` (the `(x : y : 1 : x y)` of `to_edwards`).
  Conversion lemmas (`as_projective`, `as_extended`, …) are not restated: a spec of the form
  `r.toProjective = self.toExtended.toProjective` feeds the library's `onCurve_toProjective`,
  `toPoint_toProjective` directly.
- Checked: `lake build Defs --wfail`, `lake build Proofs --wfail`, `lake exe runLinter Defs`,
  `lake exe runLinter Proofs`; `#print axioms` of the bridge lemmas are
  `[propext, Classical.choice, Quot.sound]`.

## 10. Open points for the review

1. ~~Names~~ Decided (2026-10-19): `curve25519.curve`, `curve25519.edwards`,
   `curve25519.montgomery`, `montgomeryTwist`, `basepoint`, `montgomeryBasepoint`, `torsion8`,
   `eightTorsion`; `Curve25519` (UpperCamel) stays unused. Models and the curve are terms, hence
   lowerCamelCase.
2. ~~`MontgomeryModel.Point` as `abbrev` of the Weierstrass point type~~ Decided: own inductive
   (principle 8), so that the backend can change to the isomorphism-class design.
3. ~~Generic encoding parametrised by `bits`, or only the curve25519 instance.~~ Decided
   (2026-10-19): generic, `bits` an explicit parameter; `isNeg` moves to
   `EllipticCurve/Field/Sign`; the curve25519 instance is `abbrev`s plus specialised lemmas.
4. ~~Whether projective equality belongs at the math level or in `Defs`.~~ Decided
   (2026-10-19): math level, as `Extended.ProjEq`/`Projective.ProjEq` with
   `projEq_iff_toPoint_eq`; Ristretto's `Rel` with `rel_iff_formula` follows the same pattern.
5. ~~Order of work~~ Decided (2026-10-19): §3 Curve + §5.1–5.2 Montgomery → §4.1–4.5 Edwards
   model, group, coordinates, formulas (with `edwards.IsComplete`) → §6.1, 6.3 instances and
   certificates → §7.1–7.2 even subgroup, quotient, `card = L` → §5.3 `x25519` → §6.2 curve25519
   Montgomery facts and twist → §4.6/6.4 Edwards encoding → §7.3–7.4 Ristretto encoding and map.
   Review gates: after the generic Edwards API (step 2) and at the end.
6. ~~Names of the generic library and the Ristretto objects~~ Decided (2026-10-19): library
   `EllipticCurve` (modules `EllipticCurve/Curve/…`, `EllipticCurve/TwistedEdwards/…`, …; note
   Mathlib's `Mathlib.AlgebraicGeometry.EllipticCurve` is a different namespace); generic quotient
   `TwistedEdwardsModel.EvenQuotient` (docstring: the Decaf/Ristretto construction); type
   `curve25519.Ristretto`, representative-level functions suffixed `Rep` (`encodeRep`,
   `decodeRep`, `mapRep`), quotient-level unsuffixed.
7. ~~2-descent~~ Decided (2026-10-19): "even" is Mathlib's `Even` / `AddSubgroup.even`, nothing
   of ours; `even_iff_isSquare : Even P ↔ IsSquare (1 - P.y ^ 2)` is stated now as a backend
   proof obligation (a later correction touches only this lemma, with sign-off).

All open points are decided; the draft is the reference for Phase 2.
