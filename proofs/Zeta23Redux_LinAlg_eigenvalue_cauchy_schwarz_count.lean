import Mathlib

/-!
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- **Thresholded Cauchy–Schwarz count (Lemma 3.3, eigenvalue level).**
If `theta ≥ 0` and the total eigenvalue mass exceeds `theta * d`, then the excess mass squared is
bounded by the number `n` of eigenvalues exceeding `theta` times the sum of squares of all
eigenvalues. -/
theorem eigenvalue_cauchy_schwarz_count
    (d : ℕ) (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta)
    (s : Finset (Fin d)) (hs : s = Finset.univ.filter (fun i => theta < ev i))
    (n : ℕ) (hn : n = s.card)
    (hsum : theta * (d : ℝ) < ∑ i, ev i) :
    ((∑ i, ev i) - theta * (d : ℝ)) ^ 2 ≤ (n : ℝ) * ∑ i, (ev i) ^ 2 := by
  classical
  -- The excess mass is the sum of the shifted eigenvalues.
  have hshift : (∑ i, ev i) - theta * (d : ℝ) = ∑ i, (ev i - theta) := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  -- Eigenvalues below the threshold only decrease the sum.
  have hsplit : ∑ i, (ev i - theta) =
      (∑ i ∈ s, (ev i - theta)) + ∑ i ∈ sᶜ, (ev i - theta) := by
    rw [Finset.sum_add_sum_compl]
  have hcompl : ∑ i ∈ sᶜ, (ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have : ev i ≤ theta := by simp [hs] at hi; exact hi
    linarith
  -- Dropping the (nonnegative) threshold on the retained eigenvalues.
  have hdrop : ∑ i ∈ s, (ev i - theta) ≤ ∑ i ∈ s, ev i := by
    apply Finset.sum_le_sum
    intro i _
    linarith
  have hkey : (∑ i, ev i) - theta * (d : ℝ) ≤ ∑ i ∈ s, ev i := by
    rw [hshift, hsplit]; linarith
  have hpos : 0 < (∑ i, ev i) - theta * (d : ℝ) := by linarith
  -- Cauchy–Schwarz on the retained eigenvalues.
  have hCS : (∑ i ∈ s, ev i) ^ 2 ≤ (n : ℝ) * ∑ i ∈ s, (ev i) ^ 2 := by
    rw [hn]; exact sq_sum_le_card_mul_sum_sq
  have hsub : ∑ i ∈ s, (ev i) ^ 2 ≤ ∑ i, (ev i) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    intro i _ _
    positivity
  have hsq : ((∑ i, ev i) - theta * (d : ℝ)) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := by
    apply sq_le_sq' <;> linarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hsub hnn]

end Zeta23Redux.LinAlg

