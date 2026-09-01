import Mathlib

/-!
# Gram Positivity 3
Category: Riemann Program
Target: Riemann.HardyZ.gram_positivity_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.HardyZ

/-- A 3-point Weil/Hardy positivity shadow: the quadratic form of the PSD matrix
with `1` on the diagonal and `1/2` off the diagonal is nonnegative. -/
theorem gram_positivity_3 (x y z : ℝ) :
    0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x := by
  nlinarith [sq_nonneg (x + y + z), sq_nonneg x, sq_nonneg y, sq_nonneg z]

end Riemann.HardyZ

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

