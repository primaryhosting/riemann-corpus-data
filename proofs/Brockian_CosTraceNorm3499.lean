/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- **Cosine trace-norm bound.**  If each row `i` of a real square matrix `A` is rescaled by
`Real.cos (θ i)`, then the trace of the resulting matrix is bounded in absolute value by the
sum of the absolute values of the diagonal entries of `A`. -/
theorem CosTraceNorm3499 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (θ : Fin n → ℝ) :
    |Matrix.trace (Matrix.of fun i j => Real.cos (θ i) * A i j)| ≤ ∑ i, |A i i| := by
  rw [Matrix.trace]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro i _
  simp only [Matrix.diag_apply, Matrix.of_apply, abs_mul]
  have h : |Real.cos (θ i)| ≤ 1 := Real.abs_cos_le_one _
  nlinarith [abs_nonneg (A i i), abs_nonneg (Real.cos (θ i))]

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

