/-
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.BaezDuarte

/-- Baez-Duarte / Nyman-Beurling shape: the squared distance between two reals
(e.g. a vector and its projection onto a subspace) is nonnegative. -/
theorem distance_nonneg (x y : ℝ) : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)

end Riemann.BaezDuarte

