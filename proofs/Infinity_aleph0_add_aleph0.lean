/-
# Aleph 0 Add Aleph 0
Category: Frontier — Set Theory
Target: Infinity.aleph0_add_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Aleph 0 Add Aleph 0
Category: Frontier — Set Theory
Target: Infinity.aleph0_add_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Infinity

/-- Cardinal arithmetic: `ℵ₀ + ℵ₀ = ℵ₀`. -/
theorem aleph0_add_aleph0 : Cardinal.aleph0 + Cardinal.aleph0 = Cardinal.aleph0 :=
  Cardinal.add_eq_self le_rfl

/-- Cardinal arithmetic: `ℵ₀ * ℵ₀ = ℵ₀`. -/
theorem aleph0_mul_aleph0 : Cardinal.aleph0 * Cardinal.aleph0 = Cardinal.aleph0 :=
  Cardinal.mul_eq_self le_rfl

end Infinity

