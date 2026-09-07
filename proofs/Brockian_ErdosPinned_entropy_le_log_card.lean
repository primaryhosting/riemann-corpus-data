/-
  Brockian/ErdosPinnedLemmas.lean

  Machine-check of the UNCONDITIONAL elementary lemmas underpinning
  "Pinned Distances, Radial Operators, and an Energy--Entropy Bridge for
  Erdős Problem #604" (C. Brock).

  The paper's whole conditional reduction rests on two elementary
  information-theoretic facts, both stated with omitted / one-line proofs:

    (1) Rényi-entropy monotonicity  H(μ) ≥ H₂(μ), equivalently
            e^{-H(μ)} ≤ ∑ μ_i²           (paper Lemma 3.2 — proof OMITTED)
    (2) Entropy ≤ log of support size
            H(μ) ≤ log D                 (paper Lemma 3.4)

  Both are consequences of Jensen's inequality for the (strictly) concave
  `Real.log` on `(0, ∞)`.  We prove them for a strictly-positive probability
  vector on a Finset (the essential support case; the 0·log 0 = 0 convention
  extends them but is not the mathematical content).

  Honest scope: this file proves (1) and (2) exactly.  It does NOT formalize
  the incidence-geometry structure theorem (paper §5), which the paper itself
  labels a sketch, nor the grid / Landau–Ramanujan count.

  No `sorry`, no `admit`, no new axioms.  Verify: AXLE @ lean-4.32.0.
-/
import Mathlib

open Finset
open scoped BigOperators

namespace Brockian.ErdosPinned

/-- **Rényi-entropy monotonicity** (paper Lemma 3.2, whose proof the paper omits).

For a strictly positive probability vector `μ` on a Finset `s`,
`exp(∑ μ_i log μ_i) ≤ ∑ μ_i²`, i.e. `e^{-H(μ)} ≤ ∑ μ_i²` since
`H(μ) = -∑ μ_i log μ_i`.  This is the exact inequality the Energy–Entropy
Bridge (Lemma 3.1) invokes. -/
theorem exp_neg_entropy_le_sum_sq
    {ι : Type*} (s : Finset ι) (μ : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < μ i) (hsum : ∑ i ∈ s, μ i = 1) :
    Real.exp (∑ i ∈ s, μ i * Real.log (μ i)) ≤ ∑ i ∈ s, (μ i) ^ 2 := by
  -- Jensen for the concave `log` on `Ioi 0`, with weights `μ` and points `μ`.
  have hconc : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have h0 : ∀ i ∈ s, 0 ≤ μ i := fun i hi => (hpos i hi).le
  have hmem : ∀ i ∈ s, μ i ∈ Set.Ioi (0 : ℝ) := fun i hi => hpos i hi
  have hjensen :
      (∑ i ∈ s, μ i • Real.log (μ i)) ≤ Real.log (∑ i ∈ s, μ i • μ i) :=
    hconc.le_map_sum h0 hsum hmem
  -- rewrite smul as mul, and μ_i • μ_i = μ_i²
  have hjensen' :
      (∑ i ∈ s, μ i * Real.log (μ i)) ≤ Real.log (∑ i ∈ s, (μ i) ^ 2) := by
    simpa [smul_eq_mul, sq] using hjensen
  -- the sum of squares is strictly positive
  have hne : s.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hsum]; norm_num)
  have hsq_pos : 0 < ∑ i ∈ s, (μ i) ^ 2 := by
    obtain ⟨j, hj⟩ := hne
    refine Finset.sum_pos' (fun i _ => sq_nonneg (μ i)) ⟨j, hj, ?_⟩
    exact pow_pos (hpos j hj) 2
  -- exp is monotone; exp (log x) = x for x > 0
  calc Real.exp (∑ i ∈ s, μ i * Real.log (μ i))
      ≤ Real.exp (Real.log (∑ i ∈ s, (μ i) ^ 2)) := Real.exp_le_exp.mpr hjensen'
    _ = ∑ i ∈ s, (μ i) ^ 2 := Real.exp_log hsq_pos

/-- **Entropy ≤ log of support size** (paper Lemma 3.4 / eq. (3.5)).

For a strictly positive probability vector `μ` on a Finset `s`,
the Shannon entropy `H(μ) = -∑ μ_i log μ_i` is at most `log |s|`.
Taking `s` to be the support (`|s| = d(x)`) gives the paper's `H_x ≤ log d(x)`. -/
theorem entropy_le_log_card
    {ι : Type*} (s : Finset ι) (μ : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < μ i) (hsum : ∑ i ∈ s, μ i = 1) :
    -(∑ i ∈ s, μ i * Real.log (μ i)) ≤ Real.log (s.card) := by
  have hconc : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have h0 : ∀ i ∈ s, 0 ≤ μ i := fun i hi => (hpos i hi).le
  -- points p_i = 1/μ_i ∈ Ioi 0
  have hmem : ∀ i ∈ s, (μ i)⁻¹ ∈ Set.Ioi (0 : ℝ) :=
    fun i hi => inv_pos.mpr (hpos i hi)
  have hjensen :
      (∑ i ∈ s, μ i • Real.log ((μ i)⁻¹)) ≤ Real.log (∑ i ∈ s, μ i • (μ i)⁻¹) :=
    hconc.le_map_sum h0 hsum hmem
  -- LHS: μ_i • log(μ_i⁻¹) = μ_i * (-log μ_i) = -(μ_i log μ_i)
  have hlhs :
      (∑ i ∈ s, μ i • Real.log ((μ i)⁻¹)) = -(∑ i ∈ s, μ i * Real.log (μ i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [smul_eq_mul, Real.log_inv]; ring
  -- RHS argument: ∑ μ_i * μ_i⁻¹ = ∑ 1 = |s|
  have hrhs : (∑ i ∈ s, μ i • (μ i)⁻¹) = (s.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [smul_eq_mul, mul_inv_cancel₀ (ne_of_gt (hpos i hi))])]
    simp
  rw [hlhs, hrhs] at hjensen
  exact hjensen

end Brockian.ErdosPinned
