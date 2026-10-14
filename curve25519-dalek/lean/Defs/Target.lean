/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas
@[expose] public section

/-! # The compilation target (audited)

Functions with per-target variants are translated as dispatchers on `get_target`, an Aeneas axiom
about which nothing is known. Specs of dispatchers assume a 64-bit target (u64 backend) until the
u32 backend is verified. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-- The crate is compiled for one of the two x86_64 targets (u64 backend). -/
def OnX86_64 : Prop :=
  get_target ⦃ (t : Str) => t = toStr "x86_64-tables" ∨ t = toStr "x86_64-no-tables" ⦄

attribute [nolint defsWithUnderscore] OnX86_64
