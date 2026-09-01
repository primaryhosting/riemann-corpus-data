/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- Auxiliary tail estimate: for `1 ≤ Q` and any `n`, the finite sum
`∑_{k < n} C / (k + Q)^2` is at most `2 * C / Q`. -/
lemma finite_tail_inv_sq_le {C : ℝ} (hC : 0 ≤ C) {Q : ℕ} (hQ : 1 ≤ Q) (n : ℕ) :
    ∑ k ∈ range n, C / ((k + Q : ℕ) : ℝ) ^ 2 ≤ 2 * C / Q := by
  have hreindex :
      ∑ k ∈ range n, C / ((k + Q : ℕ) : ℝ) ^ 2
        = ∑ i ∈ Ico Q (n + Q), C / (i : ℝ) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  have hset : Ico Q (n + Q) = Ioo (Q - 1) (n + Q) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  have hkey : ∑ i ∈ Ioo (Q - 1) (n + Q), ((i : ℝ) ^ 2)⁻¹ ≤ 2 / (((Q - 1 : ℕ) : ℝ) + 1) :=
    sum_Ioo_inv_sq_le _ _
  have hcast : ((Q - 1 : ℕ) : ℝ) + 1 = (Q : ℝ) := by
    have : ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1 := by
      have : (1 : ℕ) ≤ Q := hQ
      push_cast [Nat.cast_sub this]
      ring
    rw [this]; ring
  rw [hcast] at hkey
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hQ
  calc ∑ k ∈ range n, C / ((k + Q : ℕ) : ℝ) ^ 2
      = C * ∑ i ∈ Ioo (Q - 1) (n + Q), ((i : ℝ) ^ 2)⁻¹ := by
        rw [hreindex, hset, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
    _ ≤ C * (2 / (Q : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hkey hC
    _ = 2 * C / Q := by ring

/-- **Effective convergence rate for a singular series.**

If the terms `a q` of a singular-series-type expansion satisfy the standard
majorization `|a q| ≤ C / q²` for all `q ≥ 1`, then the series converges and the
truncation at level `Q ≥ 1` incurs an error of at most `2 * C / Q`; that is, the
truncated singular series `∑_{q < Q} a q` approximates the full singular series
`∑' q, a q` with an explicit `O(1/Q)` rate. -/
theorem SingularSeriesConvergenceRate {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ q, 1 ≤ q → |a q| ≤ C / (q : ℝ) ^ 2) {Q : ℕ} (hQ : 1 ≤ Q) :
    Summable a ∧ |(∑' q, a q) - ∑ q ∈ range Q, a q| ≤ 2 * C / Q := by
  have hC : 0 ≤ C := by
    have h1 := ha 1 le_rfl
    have : |a 1| ≤ C := by simpa using h1
    exact le_trans (abs_nonneg _) this
  -- Summability by comparison with `C / q²`.
  have hsum : Summable a := by
    have hg : Summable fun q : ℕ => C / (q : ℝ) ^ 2 := by
      simpa [div_eq_mul_inv] using
        ((Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2)).mul_left C)
    refine Summable.of_norm_bounded_eventually_nat hg ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with q hq
    simpa [Real.norm_eq_abs] using ha q hq
  refine ⟨hsum, ?_⟩
  -- Split the series at `Q`.
  have hsplit : ∑ q ∈ range Q, a q + ∑' k, a (k + Q) = ∑' q, a q :=
    hsum.sum_add_tsum_nat_add Q
  have hdiff : (∑' q, a q) - ∑ q ∈ range Q, a q = ∑' k, a (k + Q) := by
    rw [← hsplit]; ring
  rw [hdiff]
  -- Bound the tail by the absolute tail, then by `2C/Q`.
  have habs : Summable fun k => |a (k + Q)| :=
    ((hsum.comp_injective (add_left_injective Q)).abs)
  have h1 : |∑' k, a (k + Q)| ≤ ∑' k, |a (k + Q)| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun k => a (k + Q)) (by simpa [Real.norm_eq_abs] using habs)
  refine h1.trans ?_
  refine Real.tsum_le_of_sum_range_le (fun k => abs_nonneg _) (fun n => ?_)
  refine le_trans (Finset.sum_le_sum (fun k _ => ha (k + Q) (by omega))) ?_
  exact finite_tail_inv_sq_le hC hQ n

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

