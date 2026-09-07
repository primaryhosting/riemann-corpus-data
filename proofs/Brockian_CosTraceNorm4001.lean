import Mathlib
/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset Matrix

/-- **Cos Trace Norm 4001.**  For any family of angles `θ : Fin n → ℝ`, the diagonal
matrix with entries `cos (θ i)` has trace equal to `∑ i, cos (θ i)`, and this trace is
bounded in absolute value by `n`.

The key Mathlib ingredients are `Matrix.trace_diagonal`, `Finset.abs_sum_le_sum_abs`
and `Real.abs_cos_le_one`. -/
theorem CosTraceNorm4001 {n : ℕ} (θ : Fin n → ℝ) :
    Matrix.trace (Matrix.diagonal fun i => Real.cos (θ i)) = ∑ i, Real.cos (θ i) ∧
      |Matrix.trace (Matrix.diagonal fun i => Real.cos (θ i))| ≤ (n : ℝ) := by
  have htr : Matrix.trace (Matrix.diagonal fun i => Real.cos (θ i)) = ∑ i, Real.cos (θ i) :=
    Matrix.trace_diagonal _
  refine ⟨htr, ?_⟩
  rw [htr]
  calc |∑ i, Real.cos (θ i)| ≤ ∑ i : Fin n, |Real.cos (θ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => Real.abs_cos_le_one (θ i)
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

