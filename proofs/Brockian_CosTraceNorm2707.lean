/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian

/-- **Cos trace-norm bound.**  A weighted sum of cosines is bounded in absolute value by the
sum of the absolute values of the weights.  (Trace-norm style bound: for a "trace"
`∑ k, c k * cos (f k)` the phases can only shrink the total mass.)

The proof is by induction on the number of terms `n`. -/
theorem CosTraceNorm2707 (n : ℕ) (c f : ℕ → ℝ) :
    |∑ k ∈ Finset.range n, c k * Real.cos (f k)| ≤ ∑ k ∈ Finset.range n, |c k| := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      refine (abs_add _ _).trans ?_
      have hterm : |c n * Real.cos (f n)| ≤ |c n| := by
        rw [abs_mul]
        calc |c n| * |Real.cos (f n)| ≤ |c n| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (f n)) (abs_nonneg _)
          _ = |c n| := mul_one _
      exact add_le_add ih hterm

/-- Specialisation: an unweighted sum of `n` cosines has absolute value at most `n`. -/
theorem CosTraceNorm2707_card (n : ℕ) (f : ℕ → ℝ) :
    |∑ k ∈ Finset.range n, Real.cos (f k)| ≤ n := by
  have h := CosTraceNorm2707 n (fun _ => 1) f
  simpa using h

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

