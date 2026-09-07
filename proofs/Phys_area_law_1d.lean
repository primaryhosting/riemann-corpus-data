/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Real Finset

namespace Phys

/-- Pointwise bound on the entropy contribution `-x log x` of a weight `x ≥ 0`
in terms of *any* positive comparison value `q`:
`-x log x = x log (1/q) + x log (q/x) ≤ x (-log q) + (q - x) ≤ x (-log q) + q`,
using `log t ≤ t - 1`. -/
theorem neg_mul_log_le_of_pos {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    -(x * Real.log x) ≤ x * (-Real.log q) + q := by
  rcases eq_or_lt_of_le hx with h | hx0
  · simp [← h, le_of_lt hq]
  · have hlog : Real.log (q / x) ≤ q / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (q / x) = Real.log q - Real.log x :=
      Real.log_div (ne_of_gt hq) (ne_of_gt hx0)
    have hmul := mul_le_mul_of_nonneg_left hlog hx
    rw [h2] at hmul
    have hx' : x * (q / x - 1) = q - x := by field_simp
    rw [hx'] at hmul
    nlinarith

/-- **Entanglement-entropy area law in one dimension** (the entropy-bound content of
Hastings' theorem).

Physical setting: a pure state of a 1D spin chain is cut into a left and a right half.
Writing the Schmidt decomposition across the cut, `p i` denotes the squared Schmidt
coefficients (equivalently, the eigenvalues of the reduced density matrix of the left
half), so `p` is a probability vector of length `n`, where `n` grows with the system
size, and the entanglement entropy across the cut is the Shannon entropy
`S = -∑ i, p i * log (p i)`.

The physical input coming from the spectral gap — which we take here as the hypothesis
`hdecay` — is that a gapped ground state is approximated across the cut by a matrix
product state, so that the Schmidt spectrum decays exponentially:
`p i ≤ C * exp (-α * i)` with `C, α > 0` fixed by the gap and the interaction range,
independent of the system size.

Conclusion: the entanglement entropy is bounded by an explicit constant depending only
on `C` and `α` — in particular **independent of the number `n` of Schmidt coefficients,
i.e. of the length of the chain**. This "constant, not extensive" bound is precisely the
1D area law (the boundary of an interval is a single point, so the "area" is `O(1)`).

The proof: apply `neg_mul_log_le_of_pos` with comparison value `q i = C * exp (-α * i)`,
which gives `-p i log (p i) ≤ p i * (α i - log C) + C e^{-α i}`; summing, `∑ p i = 1`
handles the `-log C` term, the hypothesis `hdecay` bounds `∑ i * p i` by
`C ∑ i e^{-α i}`, and both geometric-type series are summed in closed form. -/
theorem area_law_1d {C α : ℝ} (hC : 0 < C) (hα : 0 < α) (n : ℕ) (p : ℕ → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i ∈ Finset.range n, p i = 1)
    (hdecay : ∀ i, p i ≤ C * Real.exp (-α * i)) :
    -∑ i ∈ Finset.range n, p i * Real.log (p i)
      ≤ α * C * (Real.exp (-α) / (1 - Real.exp (-α)) ^ 2)
        + C / (1 - Real.exp (-α)) - Real.log C := by
  set r := Real.exp (-α) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  have hpow : ∀ i : ℕ, C * Real.exp (-α * i) = C * r ^ i := by
    intro i
    rw [hr, ← Real.exp_nat_mul]
    ring_nf
  -- Termwise entropy bound coming from the exponential decay of the Schmidt spectrum.
  have key : ∀ i, -(p i * Real.log (p i)) ≤ p i * (α * i - Real.log C) + C * r ^ i := by
    intro i
    have hq : 0 < C * r ^ i := by positivity
    have hbd := neg_mul_log_le_of_pos (hp0 i) hq
    have hlog : Real.log (C * r ^ i) = Real.log C - α * i := by
      rw [Real.log_mul (ne_of_gt hC) (by positivity), Real.log_pow, hr, Real.log_exp]
      ring
    rw [hlog] at hbd
    calc -(p i * Real.log (p i)) ≤ p i * (-(Real.log C - α * i)) + C * r ^ i := hbd
      _ = p i * (α * i - Real.log C) + C * r ^ i := by ring
  have hsum : -∑ i ∈ Finset.range n, p i * Real.log (p i)
      ≤ ∑ i ∈ Finset.range n, (p i * (α * i - Real.log C) + C * r ^ i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => key i
  -- Closed-form bounds for the two geometric-type sums.
  have hgeo : ∑ i ∈ Finset.range n, r ^ i ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0.le hr1]
    exact Summable.sum_le_tsum _ (fun i _ => by positivity)
      (summable_geometric_of_lt_one hr0.le hr1)
  have hsummable : Summable (fun i : ℕ => (i : ℝ) * r ^ i) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := r) hrnorm
  have hgeo2 : ∑ i ∈ Finset.range n, (i : ℝ) * r ^ i ≤ r / (1 - r) ^ 2 := by
    rw [← tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hrnorm]
    exact Summable.sum_le_tsum _ (fun i _ => by positivity) hsummable
  have hpi : ∑ i ∈ Finset.range n, p i * (i : ℝ)
      ≤ C * ∑ i ∈ Finset.range n, (i : ℝ) * r ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hd : p i ≤ C * r ^ i := by rw [← hpow i]; exact hdecay i
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hexp : ∑ i ∈ Finset.range n, (p i * (α * i - Real.log C) + C * r ^ i)
      = α * (∑ i ∈ Finset.range n, p i * (i : ℝ))
        - Real.log C * (∑ i ∈ Finset.range n, p i)
        + C * ∑ i ∈ Finset.range n, r ^ i := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, hp1] at hsum
  have hA : α * (∑ i ∈ Finset.range n, p i * (i : ℝ))
      ≤ α * (C * ∑ i ∈ Finset.range n, (i : ℝ) * r ^ i) :=
    mul_le_mul_of_nonneg_left hpi hα.le
  have hB : α * (C * ∑ i ∈ Finset.range n, (i : ℝ) * r ^ i)
      ≤ α * (C * (r / (1 - r) ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeo2 hC.le) hα.le
  have hD : C * ∑ i ∈ Finset.range n, r ^ i ≤ C / (1 - r) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hgeo hC.le
  have : α * (C * (r / (1 - r) ^ 2)) = α * C * (r / (1 - r) ^ 2) := by ring
  linarith

end Phys

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

