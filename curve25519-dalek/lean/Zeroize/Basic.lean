/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Zhang-Liao, Alessandro D'Angelo,
  Hoang Le Truong, Markus Ferdinand Dablander
-/
module
public import Aeneas
public import Curve25519Dalek.Types
@[expose] public section
-- The style linter misreads `@[rust_fun "..."]` attributes.
set_option linter.style.whitespace false
-- Docstrings quote the Aeneas name patterns, which exceed 100 characters.
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek

/-! # Functions of the `zeroize` crate (zeroize-1.8.2) — TRUSTED

This file is the trusted base for `zeroize`. Nothing here is derived.

* **Signatures.** Each external function that Aeneas expects (see the gitignored
  `Curve25519Dalek/FunsExternal_Template.lean`) is an `opaque` constant with the template's exact
  name, type and `@[rust_fun]` attribute. `opaque` adds no axiom, so `#print axioms` lists exactly
  the spec axioms below.
* **Spec axioms.** Each function has one axiom that restates the Rust body/documentation. Every
  spec that relies on a trait method of the generic `Z` (`Default::default`, `Zeroize::zeroize`)
  is conditional on that method's behaviour. An unconditional spec could prove `False`.

Volatile writes, `atomic_fence` and the "best effort" caveats (e.g. earlier `Vec` reallocations)
are not observable in the functional semantics. Zeroizing replaces the value by its zeroized
value. The trait structures `zeroize.Zeroize` / `zeroize.DefaultIsZeroes` are generated in
`Curve25519Dalek/Types.lean` (namespace `Curve25519Dalek`), so this library is specific to this
crate's translation. Derived results are in `Zeroize/Lemmas.lean` and `Zeroize/Instances.lean`.
-/

/-- [zeroize::{impl zeroize::Zeroize for Z}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 301:4-301:25
    Name pattern: [zeroize::{zeroize::Zeroize<@Z>}::zeroize] -/
@[rust_fun "zeroize::{zeroize::Zeroize<@Z>}::zeroize"]
opaque zeroize.Zeroize.Blanket.zeroize
  {Z : Type} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) : Z → Result Z

/-- "Marker trait for types whose [`Default`] is the desired zeroization result" (lib.rs:281).
    Body (lib.rs:301-304): `volatile_write(self, Z::default()); atomic_fence();`. The result is
    exactly `Z::default()` (including its failure, if `default` fails). -/
axiom zeroize.Zeroize.Blanket.zeroize_eq {Z : Type} (inst : zeroize.DefaultIsZeroes Z) (x : Z) :
    zeroize.Zeroize.Blanket.zeroize inst x = inst.coredefaultDefaultInst.default

/-- [zeroize::{impl zeroize::Zeroize for [Z; N]}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 373:4-373:25
    Name pattern: [zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize] -/
@[rust_fun "zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize"]
opaque Array.Insts.ZeroizeZeroize.zeroize
  {Z : Type} {N : Std.Usize} (ZeroizeInst : zeroize.Zeroize Z) :
  Array Z N → Result (Array Z N)

/-- "Impl [`Zeroize`] on arrays of types that impl [`Zeroize`]." (lib.rs:368). Body
    (lib.rs:373-375): `self.iter_mut().zeroize();`. Every element is zeroized, so each element of
    the result satisfies any postcondition that the element `zeroize` guarantees. -/
axiom Array.Insts.ZeroizeZeroize.zeroize_spec
    {Z : Type} {N : Std.Usize} (inst : zeroize.Zeroize Z) (a : Array Z N) {post : Z → Prop}
    (h : ∀ x ∈ a.val, inst.zeroize x ⦃ post ⦄) :
    Array.Insts.ZeroizeZeroize.zeroize inst a ⦃ a' => ∀ y ∈ a'.val, post y ⦄

/-- [zeroize::{impl zeroize::Zeroize for core::slice::iter::IterMut<'_0, Z>}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 385:4-385:25
    Name pattern: [zeroize::{zeroize::Zeroize<core::slice::iter::IterMut<'0, @Z>>}::zeroize] -/
@[rust_fun
  "zeroize::{zeroize::Zeroize<core::slice::iter::IterMut<'0, @Z>>}::zeroize"]
opaque core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  core.slice.iter.IterMut Z → Result ((core.slice.iter.IterMut Z) ×
    (core.slice.iter.IterMut Z → core.slice.iter.IterMut Z))

/-- Body (lib.rs:385-389): `for elem in self { elem.zeroize(); }`. Every element the iterator has
    not yet yielded (indices `it.i ..`) is zeroized, and the already-yielded prefix is unchanged.
    The iterator ends exhausted. The zeroized slice is returned in the new iterator, so the
    backward function (ending the `'0` borrow) is the identity. -/
axiom core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec
    {Z : Type} (inst : zeroize.Zeroize Z) (it : core.slice.iter.IterMut Z) {post : Z → Prop}
    (h : ∀ x ∈ it.slice.val.drop it.i, inst.zeroize x ⦃ post ⦄) :
    core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize inst it ⦃ it' back =>
      back = id ∧ it'.i = it.slice.length ∧ it'.slice.length = it.slice.length ∧
      it'.slice.val.take it.i = it.slice.val.take it.i ∧
      ∀ y ∈ it'.slice.val.drop it.i, post y ⦄

/-- [zeroize::{impl zeroize::Zeroize for alloc::vec::Vec<Z>}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 551:4-551:25
    Name pattern: [zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize] -/
@[rust_fun "zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize"]
opaque alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  alloc.vec.Vec Z → Result (alloc.vec.Vec Z)

/-- "\"Best effort\" zeroization for `Vec`. Ensures the entire capacity of the `Vec` is zeroed.
    Cannot ensure that previous reallocations did not leave values on the heap." (lib.rs:547-550).
    Body (lib.rs:551-560): zeroize the elements, `self.clear()`, zeroize the spare capacity.
    Aeneas' `Vec` has no capacity, so the observable result is the empty vector. Only the success
    of the element `zeroize` matters. -/
@[step]
axiom alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec
    {Z : Type} (inst : zeroize.Zeroize Z) (v : alloc.vec.Vec Z)
    (h : ∀ x ∈ v.val, inst.zeroize x ⦃ _ => True ⦄) :
    alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v ⦃ v' => v' = alloc.vec.Vec.new Z ⦄
