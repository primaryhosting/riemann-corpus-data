import Mathlib

/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

variable {ι : Type*} [Fintype ι]

/-- The set of probability vectors indexed by `ι`. -/
def probSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- The Gibbs entropy `-∑ i, p i * log (p i)` of a probability vector. -/
noncomputable def gibbsEntropy (p : ι → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

lemma convex_probSimplex : Convex ℝ (probSimplex ι) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · have h1 := hx.1 i
    have h2 := hy.1 i
    simpa using add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2]
    linarith

/-- The Gibbs entropy `−∑ pᵢ log pᵢ` is concave on the simplex of probability vectors. -/
theorem entropy_concave : ConcaveOn ℝ (probSimplex ι) gibbsEntropy := by
  refine ⟨convex_probSimplex, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [gibbsEntropy, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
    Pi.add_apply, Pi.smul_apply]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Real.concaveOn_negMulLog.2 (Set.mem_Ici.2 (hx.1 i)) (Set.mem_Ici.2 (hy.1 i)) ha hb hab

end Chem

