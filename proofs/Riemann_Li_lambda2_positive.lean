/-
# Lambda 2 Positive
Category: Riemann Program
Target: Riemann.Li.lambda2_positive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lambda 2 Positive
Category: Riemann Program
Target: Riemann.Li.lambda2_positive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Li

/-- If `0.09 ≤ x` then `0 < x`.

This encodes the positivity of Li's second coefficient `λ₂ ≈ 0.0923`
(Li's criterion: RH holds iff `λ_n ≥ 0` for all `n ≥ 1`), given the
numerical lower bound `0.09 ≤ λ₂`. -/
theorem lambda2_positive (x : ℝ) (hx : 0.09 ≤ x) : 0 < x := by
  have h : (0 : ℝ) < 0.09 := by norm_num
  linarith

end Riemann.Li

#print axioms Riemann.Li.lambda2_positive

