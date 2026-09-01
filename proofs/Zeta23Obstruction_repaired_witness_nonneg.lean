import Mathlib

/-!
# Repaired Witness Nonneg
Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Obstruction

/-- The repaired obstruction witness kernel
`(sin(π x) / (π x))^2 * (1 - (1/10) cos(3π x))` is nonnegative for every real `x`.

The first factor is a square, hence nonnegative (this also covers `x = 0`, where the
quotient is junk-valued but still squared). The second factor is at least `9/10 > 0`
by `Real.cos_le_one`. Multiplying nonnegatives gives the claim. -/
theorem repaired_witness_nonneg (x : ℝ) :
    0 ≤ (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 *
      (1 - (1 / 10) * Real.cos (3 * Real.pi * x)) := by
  have h1 : (0:ℝ) ≤ (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ 1 - (1 / 10) * Real.cos (3 * Real.pi * x) := by
    have := Real.cos_le_one (3 * Real.pi * x)
    linarith
  exact mul_nonneg h1 h2

end Zeta23Obstruction

