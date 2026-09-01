/-
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Finset Matrix

namespace Zeta23Redux.LinAlg

/-- The linear functional `M ↦ ∑ i, ∑ j, M i j * (μ i * ν j)` is linear in the matrix `M`. -/
lemma isLinearMap_sum_weights {n : Type*} [Fintype n] (μ ν : n → ℝ) :
    IsLinearMap ℝ (fun M : Matrix n n ℝ => ∑ i, ∑ j, M i j * (μ i * ν j)) where
  map_add M N := by
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul c M := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Rearrangement step: for antitone weights, a permutation can only decrease the pairing. -/
lemma sum_permMatrix_mul_le {n : Type*} [Fintype n] [LinearOrder n] [DecidableEq n]
    (σ : Equiv.Perm n) {μ ν : n → ℝ} (hμ : Antitone μ) (hν : Antitone ν) :
    ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (μ i * ν j) ≤ ∑ i, μ i * ν i := by
  have hsum : ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (μ i * ν j) = ∑ i, μ i * ν (σ i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [hsum]
  simpa using (hμ.monovary hν).sum_smul_comp_perm_le_sum_smul (σ := σ)

/--
**Doubly stochastic rearrangement bound.**
If `S` is doubly stochastic and `μ`, `ν` are antitone weight sequences, then
`∑ i, ∑ j, S i j * (μ i * ν j) ≤ ∑ i, μ i * ν i`.
This is the Birkhoff/rearrangement step feeding the von Neumann trace inequality.
-/
theorem sum_doublyStochastic_mul_le {n : Type*} [Fintype n] [LinearOrder n] [DecidableEq n]
    {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) {μ ν : n → ℝ}
    (hμ : Antitone μ) (hν : Antitone ν) :
    ∑ i, ∑ j, S i j * (μ i * ν j) ≤ ∑ i, μ i * ν i := by
  have hsub : (doublyStochastic ℝ n : Set (Matrix n n ℝ)) ⊆
      {M | (∑ i, ∑ j, M i j * (μ i * ν j)) ≤ ∑ i, μ i * ν i} := by
    rw [doublyStochastic_eq_convexHull_permMatrix]
    refine convexHull_min ?_ (convex_halfSpace_le (isLinearMap_sum_weights μ ν) _)
    rintro _ ⟨σ, rfl⟩
    exact sum_permMatrix_mul_le σ hμ hν
  exact hsub hS

end Zeta23Redux.LinAlg

