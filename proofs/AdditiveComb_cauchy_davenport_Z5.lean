/-
# Cauchy Davenport Z 5
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.cauchy_davenport_Z5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace AdditiveComb

/-- Cauchy–Davenport, concrete instance in `ZMod 5`: for `A = {0,1}` and `B = {0,2}`,
the sumset `A + B = {0,1,2,3}` has cardinality `4`, which is at least
`min 5 (|A| + |B| - 1) = min 5 3 = 3`. -/
theorem cauchy_davenport_Z5 :
    (({0, 1} : Finset (ZMod 5)) + ({0, 2} : Finset (ZMod 5))).card = 4 ∧
      (({0, 1} : Finset (ZMod 5)) + ({0, 2} : Finset (ZMod 5))).card ≥
        min 5 (({0, 1} : Finset (ZMod 5)).card + ({0, 2} : Finset (ZMod 5)).card - 1) := by
  constructor <;> decide

end AdditiveComb

