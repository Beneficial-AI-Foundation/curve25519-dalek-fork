/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Basic
public import Defs.Scalar52
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64

@[step]
theorem index_spec (self : Scalar52) (_index : Usize) (hindex : _index.val < 5) :
    index self _index ⦃ (r : U64) =>
      r = self[_index.val]! ⦄ := by
  unfold index
  step*
  simp_lists [*]

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64
