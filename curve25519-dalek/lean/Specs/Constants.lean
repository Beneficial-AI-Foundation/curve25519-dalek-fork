/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519.Edwards.Encoding
public import Curve25519.Edwards.Torsion
public import Curve25519.Montgomery
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Montgomery
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointPoint
import Proofs.Backend.Serial.U64.Constants.EightTorsion
import Proofs.Constants.Ed25519BasepointCompressed
import Proofs.Constants.X25519Basepoint
public section

/-! # Specs of `src/constants.rs`

Spec summary: the public point constants of `constants.rs` with their spec statements, restated
with `recall` from the theorems proved in `Proofs/`, and the axioms they depend on. Items appear
in the order of `constants.rs`, starting with the constants it re-exports from the 64-bit backend
(`backend/serial/u64/constants.rs`); those are per-configuration, so each has two statements.

Not restated here: `ED25519_BASEPOINT_TABLE` (`x86_64-tables` only), whose items assume as a
hypothesis that it represents the basepoint (see `Specs/Edwards.lean`); `BASEPOINT_ORDER`
(`pub(crate)`, proved in `Proofs/Constants/BasepointOrder.lean`); the Ristretto constants
(`RISTRETTO_BASEPOINT_COMPRESSED`, `RISTRETTO_BASEPOINT_POINT`, `RISTRETTO_BASEPOINT_TABLE`), left
for the specs of `ristretto.rs`. Not translated: `X25519_LOW_ORDER_POINTS`.

Definitions used: `EdwardsPoint.toPoint`, `OnCurve`, `Bounded`, `CompressedEdwardsY.asNat`
(`Defs/Edwards.lean`), `MontgomeryPoint.asNat` (`Defs/Montgomery.lean`), `curve25519.basepoint`
(`Curve25519/Edwards/Basepoint.lean`), `curve25519.encode` (`Curve25519/Edwards/Encoding.lean`),
`curve25519.eightTorsion` (`Curve25519/Edwards/Torsion.lean`), `curve25519.montgomeryBasepoint`
(`Curve25519/Montgomery.lean`), `curve25519.encodeU` (`Curve25519/X25519.lean`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel

namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
recall ED25519_BASEPOINT_POINT_spec_point :
    ED25519_BASEPOINT_POINT.«x86_64-tables» ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_POINT_spec_point

end «x86_64-tables»
end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-no-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
recall ED25519_BASEPOINT_POINT_spec_point :
    ED25519_BASEPOINT_POINT.«x86_64-no-tables» ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_POINT_spec_point

end «x86_64-no-tables»
end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-tables»

/-- `EIGHT_TORSION`: entry `i` represents `eightTorsion i = i • torsion8`. -/
recall EIGHT_TORSION_spec_point :
    EIGHT_TORSION.«x86_64-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«x86_64-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = eightTorsion i ∧ r[i.val]!.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EIGHT_TORSION_spec_point

end «x86_64-tables»
end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-no-tables»

/-- `EIGHT_TORSION`: entry `i` represents `eightTorsion i = i • torsion8`. -/
recall EIGHT_TORSION_spec_point :
    EIGHT_TORSION.«x86_64-no-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«x86_64-no-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = eightTorsion i ∧ r[i.val]!.Bounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EIGHT_TORSION_spec_point

end «x86_64-no-tables»
end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.constants

/-- `ED25519_BASEPOINT_COMPRESSED`: RFC 8032's encoding of the basepoint. -/
recall ED25519_BASEPOINT_COMPRESSED_spec :
    ED25519_BASEPOINT_COMPRESSED.asNat = curve25519.encode curve25519.basepoint

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_COMPRESSED_spec

end Curve25519Dalek.constants

namespace Curve25519Dalek.constants

/-- `X25519_BASEPOINT`: RFC 7748's encoding of the `u`-coordinate `9` of the Montgomery
basepoint. -/
recall X25519_BASEPOINT_spec :
    X25519_BASEPOINT.asNat = curve25519.encodeU curve25519.montgomeryBasepoint.u

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms X25519_BASEPOINT_spec

end Curve25519Dalek.constants
