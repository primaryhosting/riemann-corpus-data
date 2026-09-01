/-
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann
namespace BaezDuarte

/-- Baez-Duarte / Nyman-Beurling shape: the squared distance between two reals
(e.g. a vector and its approximation from a subspace) is nonnegative. -/
theorem distance_nonneg (x y : ℝ) : 0 ≤ (x - y) ^ 2 := by
  rcases le_total y x with h | h
  · exact pow_two_nonneg (x - y)
  · exact pow_two_nonneg (x - y)

end BaezDuarte
end Riemann

