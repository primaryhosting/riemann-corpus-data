/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- **Cos Trace Norm 3499.**

For the real diagonal matrix `D = diagonal (fun i => cos (θ i))` of size `n`, the absolute
value of its trace is bounded by its trace norm `∑ i, |cos (θ i)|` (the sum of the singular
values of a real diagonal matrix), which in turn is bounded by `n`.

The proof uses the Mathlib lemmas `Matrix.trace_diagonal`, `Finset.abs_sum_le_sum_abs` and
`Real.abs_cos_le_one`. -/
theorem CosTraceNorm3499 (n : ℕ) (θ : Fin n → ℝ) :
    |Matrix.trace (Matrix.diagonal fun i => Real.cos (θ i))| ≤ ∑ i, |Real.cos (θ i)| ∧
      ∑ i, |Real.cos (θ i)| ≤ (n : ℝ) := by
  constructor
  · rw [Matrix.trace_diagonal]
    exact Finset.abs_sum_le_sum_abs _ _
  · calc ∑ i, |Real.cos (θ i)| ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
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

