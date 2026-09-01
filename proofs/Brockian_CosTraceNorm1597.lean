/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- **Cos trace norm bound.** For any phases `θ : Fin n → ℝ`, the diagonal matrix with
entries `cos (θ i)` has trace bounded in absolute value by `n`, and its trace norm
(the sum of the absolute values of its diagonal entries, which are its singular values)
is bounded by `n` as well.

The key Mathlib ingredients are `Matrix.trace_diagonal`, `Finset.abs_sum_le_sum_abs`
and `Real.abs_cos_le_one`. -/
theorem CosTraceNorm1597 (n : ℕ) (θ : Fin n → ℝ) :
    |Matrix.trace (Matrix.diagonal fun i => Real.cos (θ i))| ≤ n ∧
      (∑ i, |Real.cos (θ i)|) ≤ n := by
  have hsum : (∑ i : Fin n, |Real.cos (θ i)|) ≤ n := by
    calc (∑ i : Fin n, |Real.cos (θ i)|) ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Real.abs_cos_le_one (θ i)
      _ = n := by simp
  refine ⟨?_, hsum⟩
  rw [Matrix.trace_diagonal]
  exact (Finset.abs_sum_le_sum_abs _ _).trans hsum

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

