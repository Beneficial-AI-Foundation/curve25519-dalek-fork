/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import ToAeneas.Array
public import Defs.FieldElement2625
public import Defs.FieldElement51
public section

/-! # `montgomery.rs`: the `u`-coordinate bytes and the ladder's projective points (audited)

`MontgomeryPoint` is 32 bytes: `bytes` is them as a `Vector UInt8 32` (`Array.toVector`), the
byte string of RFC 7748, and `u` the `u`-coordinate they encode, RFC 7748 `decodeUCoordinate`
(bit `255` masked, reduced modulo `p`).

`ProjectivePoint (U : W)` is the `x`-only projective point of the Montgomery ladder: `toXZ` maps
it to `MontgomeryModel.XZ (ZMod p)`, whose `toU` is `U / W` (`0` at `W = 0`, as `as_affine`).
`LimbsLt n` says every limb is `< 2^n`; the x86_64 specs use `LimbsLt 52`: the code's
`differential_add_and_double` adds two coordinates before squaring or multiplying them, so it
needs limbs `< 2^53`, and every producer (`identity`, `from_bytes`, the `mul`/`square` outputs of
the ladder step) gives `< 2^52`. -/

open Aeneas Aeneas.Std curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.montgomery

/-! ### `MontgomeryPoint` -/

/-- Needed for `v[i]!` on vectors of points; the default is never observed for in-range
indices. -/
instance MontgomeryPoint.instInhabited : Inhabited MontgomeryPoint :=
  inferInstanceAs (Inhabited (Array U8 32#usize))

/-- The 32 bytes as a `Vector UInt8 32`, the byte string of RFC 7748. -/
@[expose] def MontgomeryPoint.bytes (self : MontgomeryPoint) : Vector UInt8 32 :=
  Aeneas.Std.Array.toVector self

/-- The `u`-coordinate encoded by the bytes: RFC 7748 `decodeUCoordinate` (the value of the low
`255` bits) as a field element. -/
@[expose] def MontgomeryPoint.u (self : MontgomeryPoint) : ZMod p :=
  (decodeUCoordinate self.bytes : ZMod p)

/-! ### `ProjectivePoint` -/

namespace ProjectivePoint.«x86_64-tables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«x86_64-tables») : MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«x86_64-tables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«x86_64-tables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«x86_64-tables»

namespace ProjectivePoint.«i686-tables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«i686-tables») : MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«i686-tables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«i686-tables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«i686-tables»

namespace ProjectivePoint.«x86_64-no-tables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«x86_64-no-tables») :
    MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«x86_64-no-tables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«x86_64-no-tables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«x86_64-no-tables»

namespace ProjectivePoint.«i686-no-tables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«i686-no-tables») :
    MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«i686-no-tables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«i686-no-tables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«i686-no-tables»

end Curve25519Dalek.montgomery
