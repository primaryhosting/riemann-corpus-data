import Mathlib

/-!
# Finite Distance Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: NymanBeurling.finite_distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace NymanBeurling

/-- Scalar core of the Nyman–Beurling finite-shape estimate: for real `u`, `p`
with `p ^ 2 ≤ u ^ 2` and `0 ≤ u`, the residual `u ^ 2 - p ^ 2` is nonnegative.

The hypothesis `0 ≤ u` is part of the requested statement but is not needed for
the conclusion; the result follows from `sub_nonneg` applied to `h`. -/
theorem finite_distance_nonneg (u p : ℝ) (h : p ^ 2 ≤ u ^ 2) (hu : 0 ≤ u) :
    0 ≤ u ^ 2 - p ^ 2 := by
  clear hu
  exact sub_nonneg.mpr h

end NymanBeurling

