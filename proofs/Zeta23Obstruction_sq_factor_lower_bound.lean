/-
# Sq Factor Lower Bound
Category: Brockian Corpus
Target: Zeta23Obstruction.sq_factor_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Obstruction

/-- The witness's modulation factor `1 - (1/10)·cos(3πx)` is bounded below by `9/10`
for every real `x`. -/
theorem sq_factor_lower_bound (x : ℝ) :
    (9 : ℝ) / 10 ≤ 1 - (1 / 10) * Real.cos (3 * Real.pi * x) := by
  have h : Real.cos (3 * Real.pi * x) ≤ 1 := Real.cos_le_one _
  linarith

end Zeta23Obstruction

