/-
# Exceeds Bound At 5040
Category: Riemann Program
Target: Riemann.Robin.exceeds_bound_at_5040
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.Robin

/-- For all real `E, LL` with `0 ≤ E ≤ 1.782` and `0 ≤ LL ≤ 2.143`, we have
`E * 5040 * LL < 19344`.

Combined with `σ(5040) = 19344`, `e^γ ≤ 1.782` and `log (log 5040) ≤ 2.143`, this shows that
Robin's bound `e^γ * n * log log n` is exceeded by `σ(n)` at `n = 5040`.

The hypothesis `0 ≤ E` is kept as stated, although the proof does not need it. -/
theorem exceeds_bound_at_5040 (E LL : ℝ) (hE0 : 0 ≤ E) (hE : E ≤ 1.782)
    (hLL0 : 0 ≤ LL) (hLL : LL ≤ 2.143) :
    E * 5040 * LL < 19344 := by
  have h1 : E * 5040 * LL ≤ 1.782 * 5040 * LL := by nlinarith
  have h2 : 1.782 * 5040 * LL ≤ 1.782 * 5040 * 2.143 := by nlinarith
  linarith

end Riemann.Robin

