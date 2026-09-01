import Mathlib

/-!
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Zeta23Redux
namespace LinAlg

/-- **Thresholded Cauchy–Schwarz count (Lemma 3.3, eigenvalue level).**

If `ev : Fin d → ℝ` is a family of eigenvalues, `θ ≥ 0` a threshold, `s` the set of indices
whose eigenvalue exceeds `θ`, and `n = #s`, then whenever `θ * d < ∑ ev`, we have
`(∑ ev - θ * d)^2 ≤ n * ∑ (ev i)^2`.

The proof: eigenvalues at or below the threshold only decrease `∑ (ev i - θ)`, so
`∑ ev - θ * d ≤ ∑_{i ∈ s} (ev i - θ) ≤ ∑_{i ∈ s} ev i`; then Cauchy–Schwarz on `s`. -/
theorem eigenvalue_cauchy_schwarz_count
    (d : Nat) (ev : Fin d → Real) (theta : Real) (htheta : 0 ≤ theta)
    (s : Finset (Fin d)) (hs : s = Finset.univ.filter (fun i => theta < ev i))
    (n : Nat) (hn : n = s.card)
    (hsum : theta * (d : Real) < Finset.univ.sum ev) :
    (Finset.univ.sum ev - theta * (d : Real)) ^ 2
      ≤ (n : Real) * Finset.univ.sum (fun i => (ev i) ^ 2) := by
  classical
  subst hs; subst hn
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hsdef
  -- Step 1: `∑ ev - θ * d = ∑ i, (ev i - θ)`
  have hsplit : Finset.univ.sum ev - theta * (d : Real)
      = Finset.univ.sum (fun i => ev i - theta) := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  -- Step 2: the terms outside `s` are nonpositive
  have hout : (Finset.univ.filter (fun i => ¬ theta < ev i)).sum (fun i => ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    simp only [Finset.mem_filter, not_lt] at hi
    linarith [hi.2]
  have hstep1 : Finset.univ.sum ev - theta * (d : Real) ≤ s.sum (fun i => ev i - theta) := by
    rw [hsplit, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => theta < ev i)]
    linarith
  -- Step 3: drop the `-θ` (using `θ ≥ 0`)
  have hstep2 : s.sum (fun i => ev i - theta) ≤ s.sum ev := by
    apply Finset.sum_le_sum
    intro i _
    linarith
  have hkey : Finset.univ.sum ev - theta * (d : Real) ≤ s.sum ev := le_trans hstep1 hstep2
  have hpos : 0 < Finset.univ.sum ev - theta * (d : Real) := by linarith
  -- Step 4: square and apply Cauchy–Schwarz on `s`
  have hsq : (Finset.univ.sum ev - theta * (d : Real)) ^ 2 ≤ (s.sum ev) ^ 2 := by
    apply pow_le_pow_left₀ (le_of_lt hpos) hkey
  have hcs : (s.sum ev) ^ 2 ≤ (s.card : Real) * s.sum (fun i => (ev i) ^ 2) :=
    sq_sum_le_card_mul_sum_sq
  have hmono : s.sum (fun i => (ev i) ^ 2) ≤ Finset.univ.sum (fun i => (ev i) ^ 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _
    positivity
  have hcard : (0 : Real) ≤ (s.card : Real) := by positivity
  calc (Finset.univ.sum ev - theta * (d : Real)) ^ 2
      ≤ (s.sum ev) ^ 2 := hsq
    _ ≤ (s.card : Real) * s.sum (fun i => (ev i) ^ 2) := hcs
    _ ≤ (s.card : Real) * Finset.univ.sum (fun i => (ev i) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hmono hcard

end LinAlg
end Zeta23Redux

