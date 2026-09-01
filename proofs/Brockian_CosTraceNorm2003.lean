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

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Brockian

/-- **Cos trace norm bounds.**

For the real diagonal matrix `D = diagonal (fun i => cos (θ i))` of size `n`:

* its trace is dominated in absolute value by its trace norm
  `‖D‖₁ = ∑ i, |cos (θ i)|` (the sum of the singular values of `D`, which for a
  diagonal matrix are the absolute values of the diagonal entries);
* the trace norm is at most the dimension `n`;
* that second bound is attained exactly when every `cos (θ i)` is `±1`,
  i.e. every `θ i` is an integer multiple of `π`.
-/
theorem CosTraceNorm2003 (n : ℕ) (θ : Fin n → ℝ) :
    |(Matrix.diagonal (fun i => Real.cos (θ i))).trace| ≤ ∑ i, |Real.cos (θ i)| ∧
      (∑ i, |Real.cos (θ i)|) ≤ (n : ℝ) ∧
        ((∑ i, |Real.cos (θ i)|) = (n : ℝ) ↔ ∀ i, ∃ k : ℤ, θ i = k * Real.pi) := by
  have htr : (Matrix.diagonal (fun i => Real.cos (θ i))).trace = ∑ i, Real.cos (θ i) := by
    simp [Matrix.trace, Matrix.diag]
  have hbound : ∀ i : Fin n, |Real.cos (θ i)| ≤ 1 := fun i => Real.abs_cos_le_one (θ i)
  refine ⟨?_, ?_, ?_⟩
  · rw [htr]
    exact Finset.abs_sum_le_sum_abs _ _
  · calc (∑ i, |Real.cos (θ i)|) ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hbound i
      _ = (n : ℝ) := by simp
  · constructor
    · intro hsum i
      have hall : |Real.cos (θ i)| = 1 := by
        by_contra hj
        have hjlt : |Real.cos (θ i)| < 1 := lt_of_le_of_ne (hbound i) hj
        have hlt : (∑ j, |Real.cos (θ j)|) < ∑ _j : Fin n, (1 : ℝ) :=
          Finset.sum_lt_sum (fun j _ => hbound j) ⟨i, Finset.mem_univ i, hjlt⟩
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one] at hlt
        exact absurd hsum (ne_of_lt hlt)
      obtain ⟨k, hk⟩ := Real.abs_cos_eq_one_iff.mp hall
      exact ⟨k, hk.symm⟩
    · intro h
      have hone : ∀ i : Fin n, |Real.cos (θ i)| = 1 := by
        intro i
        obtain ⟨k, hk⟩ := h i
        exact Real.abs_cos_eq_one_iff.mpr ⟨k, hk.symm⟩
      simp [hone]

end Brockian

