/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- **Cos trace norm bound.**
For the real diagonal matrix `A = diag (cos (θ 0), …, cos (θ (n-1)))`, its trace is bounded in
absolute value by its trace norm `∑ i, |cos (θ i)|` (the sum of its singular values, which for a
diagonal matrix are the absolute values of the diagonal entries), and that trace norm is in turn
bounded by the dimension `n`. -/
theorem CosTraceNorm3001 (n : ℕ) (θ : Fin n → ℝ) :
    |(Matrix.diagonal (fun i => Real.cos (θ i)) : Matrix (Fin n) (Fin n) ℝ).trace|
        ≤ ∑ i, |Real.cos (θ i)| ∧
      ∑ i, |Real.cos (θ i)| ≤ (n : ℝ) := by
  constructor
  · rw [Matrix.trace_diagonal]
    exact Finset.abs_sum_le_sum_abs _ _
  · calc ∑ i, |Real.cos (θ i)| ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one (θ i)
    _ = (n : ℝ) := by simp

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

