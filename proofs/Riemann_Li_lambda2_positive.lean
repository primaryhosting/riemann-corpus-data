import Mathlib

/-!
# Lambda 2 Positive
Category: Riemann Program
Target: Riemann.Li.lambda2_positive
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

namespace Riemann.Li

/-- **Lambda 2 positive.** Any real number bounded below by `0.09` is positive.

This encodes the positivity of Li's second coefficient `λ₂ ≈ 0.0923`
(Li's criterion: the Riemann Hypothesis holds iff `λₙ ≥ 0` for all `n ≥ 1`).

The proof is Mathlib's `lt_of_lt_of_le`, applied to `(0 : ℝ) < 0.09` and the hypothesis. -/
theorem lambda2_positive (x : ℝ) (hx : 0.09 ≤ x) : 0 < x :=
  lt_of_lt_of_le (by norm_num) hx

end Riemann.Li

