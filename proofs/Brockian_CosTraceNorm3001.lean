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

namespace Brockian

/-- The real diagonal matrix whose `i`-th diagonal entry is `cos (θ i)`. -/
noncomputable def cosDiag (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => Real.cos (θ i)

/-- Trace norm (Schatten `1`-norm) of a real diagonal matrix with diagonal `d`: since the
singular values of `Matrix.diagonal d` are the numbers `|d i|`, the trace norm is `∑ i, |d i|`. -/
noncomputable def diagTraceNorm (n : ℕ) (d : Fin n → ℝ) : ℝ := ∑ i, |d i|

/-- **Cos trace norm bounds.** For the diagonal matrix `cosDiag n θ` with diagonal entries
`cos (θ i)`:

* the absolute value of its trace is at most its trace norm;
* its trace norm is at most `n`;
* the trace norm equals `n` exactly when every `cos (θ i)` is `±1`.
-/
theorem CosTraceNorm3001 (n : ℕ) (θ : Fin n → ℝ) :
    |(cosDiag n θ).trace| ≤ diagTraceNorm n (fun i => Real.cos (θ i)) ∧
      diagTraceNorm n (fun i => Real.cos (θ i)) ≤ (n : ℝ) ∧
      (diagTraceNorm n (fun i => Real.cos (θ i)) = (n : ℝ) ↔
        ∀ i, Real.cos (θ i) = 1 ∨ Real.cos (θ i) = -1) := by
  have habs : ∀ i : Fin n, |Real.cos (θ i)| ≤ (1 : ℝ) := fun i => Real.abs_cos_le_one (θ i)
  have htrace : (cosDiag n θ).trace = ∑ i, Real.cos (θ i) := by
    simp [cosDiag, Matrix.trace, Matrix.diag]
  have hsum : diagTraceNorm n (fun i => Real.cos (θ i)) ≤ (n : ℝ) := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => |Real.cos (θ i)|)
      (g := fun _ : Fin n => (1 : ℝ)) (fun i _ => habs i)
    simpa [diagTraceNorm] using this
  refine ⟨?_, hsum, ?_⟩
  · rw [htrace]
    simpa [diagTraceNorm] using
      Finset.abs_sum_le_sum_abs (fun i : Fin n => Real.cos (θ i)) Finset.univ
  · constructor
    · intro heq i
      have hall : ∀ j ∈ (Finset.univ : Finset (Fin n)), |Real.cos (θ j)| = 1 := by
        refine (Finset.sum_eq_sum_iff_of_le (fun j _ => habs j)).1 ?_
        simpa [diagTraceNorm, eq_comm] using heq
      have : |Real.cos (θ i)| = 1 := hall i (Finset.mem_univ i)
      exact abs_eq (by norm_num) |>.1 this
    · intro h
      have : ∀ i : Fin n, |Real.cos (θ i)| = 1 := by
        intro i
        rcases h i with h1 | h1 <;> simp [h1]
      simp [diagTraceNorm, this]

end Brockian

