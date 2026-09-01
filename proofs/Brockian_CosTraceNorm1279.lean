/-
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian

open Finset

/-- **Cos trace norm bound.** For a diagonal matrix whose entries are cosines of
arbitrary real phases, the absolute value of the trace (equivalently, the trace norm
of the matrix, which for a diagonal matrix is the sum of the absolute values of its
entries) is bounded by the dimension.

We record both bounds: the trace-norm bound `∑ i, |cos (θ i)| ≤ n` and the
consequent bound `|trace| ≤ n`. -/
theorem CosTraceNorm1279 (n : ℕ) (θ : Fin n → ℝ) :
    ∑ i, |Real.cos (θ i)| ≤ (n : ℝ) ∧
      |(Matrix.diagonal fun i => Real.cos (θ i)).trace| ≤ (n : ℝ) := by
  have hnorm : ∑ i, |Real.cos (θ i)| ≤ (n : ℝ) := by
    calc ∑ i : Fin n, |Real.cos (θ i)| ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Real.abs_cos_le_one (θ i)
      _ = (n : ℝ) := by simp
  refine ⟨hnorm, ?_⟩
  have htr : (Matrix.diagonal fun i => Real.cos (θ i)).trace = ∑ i, Real.cos (θ i) := by
    simp [Matrix.trace_diagonal]
  rw [htr]
  exact (Finset.abs_sum_le_sum_abs _ _).trans hnorm

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

