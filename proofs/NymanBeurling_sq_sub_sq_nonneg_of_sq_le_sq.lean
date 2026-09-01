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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace NymanBeurling

/-- Key intermediate lemma: if `p ^ 2 ≤ u ^ 2`, then the difference `u ^ 2 - p ^ 2`
is nonnegative. -/
theorem sq_sub_sq_nonneg_of_sq_le_sq (u p : ℝ) (h : p ^ 2 ≤ u ^ 2) :
    0 ≤ u ^ 2 - p ^ 2 :=
  sub_nonneg.mpr h

/-- Scalar core of the Nyman–Beurling finite-shape distance formula: the residual
squared distance `u ^ 2 - p ^ 2` is nonnegative whenever `p ^ 2 ≤ u ^ 2` (and `0 ≤ u`).

Here `u` is the norm of the unit vector and `p` the norm of its projection onto the
finite-dimensional subspace. The hypothesis `0 ≤ u` is part of the requested statement,
but it is not needed for the conclusion. -/
theorem finite_distance_nonneg (u p : ℝ) (hp : p ^ 2 ≤ u ^ 2) (hu : 0 ≤ u) :
    0 ≤ u ^ 2 - p ^ 2 :=
  sq_sub_sq_nonneg_of_sq_le_sq u p hp

end NymanBeurling

