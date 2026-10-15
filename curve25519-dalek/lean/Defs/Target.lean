/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.String
public import Aeneas.Std.Target
public import Aeneas.Std.WP
public section

/-! # The compilation target (audited)

Functions with per-target variants are translated as dispatchers on Aeneas's `get_target`, an axiom
whose only spec is that it succeeds. `OnX86_64` says that it returns one of the two x86_64 target
names (u64 backend, with or without precomputed tables). It is neither provable nor refutable from
the axioms, so a statement assuming it holds for both x86_64 configurations and says nothing about
the i686 ones (u32 backend). -/

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace Curve25519Dalek

/-- The crate is compiled for one of the two x86_64 targets (u64 backend). -/
@[expose, nolint defsWithUnderscore]
def OnX86_64 : Prop :=
  get_target ⦃ (t : Str) => t = toStr "x86_64-tables" ∨ t = toStr "x86_64-no-tables" ⦄

end Curve25519Dalek
