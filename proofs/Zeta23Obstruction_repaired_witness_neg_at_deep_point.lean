/-
# Repaired Witness Neg At Deep Point

Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_neg_at_deep_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Obstruction

open Real

/-- `cosh (6π) > 10`: from `exp (3π) ≥ 3π + 1 > 10` we get `exp (6π) = (exp (3π))^2 > 100`,
and `cosh (6π) ≥ exp (6π) / 2`. -/
theorem ten_lt_cosh_six_pi : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h1 : (10 : ℝ) < Real.exp (3 * Real.pi) := by
    have := Real.add_one_le_exp (3 * Real.pi)
    linarith
  have h2 : Real.exp (6 * Real.pi) = Real.exp (3 * Real.pi) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h3 : (100 : ℝ) < Real.exp (6 * Real.pi) := by
    rw [h2]; nlinarith
  have h4 : 0 < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  rw [Real.cosh_eq]
  linarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`:
`(sinh (2π) / (2π))^2 * (1 - cosh (6π) / 10) < 0`. -/
theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.sinh (2 * Real.pi) := Real.sinh_pos_iff.mpr (by linarith)
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 := by
    have : 0 < Real.sinh (2 * Real.pi) / (2 * Real.pi) := div_pos hs (by linarith)
    positivity
  have hc := ten_lt_cosh_six_pi
  have hbr : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by linarith
  exact mul_neg_of_pos_of_neg hsq hbr

end Zeta23Obstruction

