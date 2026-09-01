import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- **Cos trace norm bound.** For any family of angles `θ : Fin 4001 → ℝ`, the trace of the
`4001 × 4001` real diagonal matrix with entries `cos (θ i)` has absolute value at most `4001`.

The key Mathlib ingredients are `Matrix.trace_diagonal`, `Finset.abs_sum_le_sum_abs` and
`Real.abs_cos_le_one`. -/
theorem CosTraceNorm4001 (θ : Fin 4001 → ℝ) :
    |(Matrix.diagonal fun i => Real.cos (θ i)).trace| ≤ 4001 := by
  rw [Matrix.trace_diagonal]
  calc |∑ i, Real.cos (θ i)| ≤ ∑ _i : Fin 4001, (1 : ℝ) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum fun i _ => Real.abs_cos_le_one (θ i)
    _ = 4001 := by simp

end Brockian

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

