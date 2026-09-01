/-
# Repaired Witness Neg At Deep Point
Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_neg_at_deep_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repaired Witness Neg At Deep Point
Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_neg_at_deep_point
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

set_option grind.warning false

namespace Zeta23Obstruction

/-- `exp 18` is at least `343 = 7 ^ 3`, from `1 + x ≤ exp x`. -/
lemma exp_eighteen_ge : (343 : ℝ) ≤ Real.exp 18 := by
  have h6 : (7 : ℝ) ≤ Real.exp 6 := by
    have := Real.add_one_le_exp (6 : ℝ)
    linarith
  have hsplit : Real.exp 18 = Real.exp 6 * (Real.exp 6 * Real.exp 6) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (6 : ℝ)]

/-- `cosh (6π) > 10`. -/
lemma cosh_six_pi_gt_ten : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h1 : Real.exp 18 ≤ Real.exp (6 * Real.pi) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 := exp_eighteen_ge
  have h3 : 0 < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  rw [Real.cosh_eq]
  linarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`. -/
theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : 0 < Real.sinh (2 * Real.pi) / (2 * Real.pi) :=
    div_pos (Real.sinh_pos_iff.mpr (by linarith)) (by linarith)
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 := pow_pos hpos 2
  have hneg : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := cosh_six_pi_gt_ten
    linarith
  exact mul_neg_of_pos_of_neg hsq hneg

end Zeta23Obstruction

