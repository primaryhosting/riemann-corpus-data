import Mathlib

/-!
# Sigma 5040
Category: Riemann Program
Target: Riemann.Robin.sigma_5040
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann.Robin

/-- The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` equals `19344`.

The proof uses the multiplicativity of `σ₁` to reduce to the prime-power factors:
`σ₁(16) * σ₁(9) * σ₁(5) * σ₁(7) = 31 * 13 * 6 * 8 = 19344`. -/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have hm := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have h1 : (5040 : ℕ) = 16 * (9 * (5 * 7)) := by norm_num
  rw [h1, hm.map_mul_of_coprime (by norm_num), hm.map_mul_of_coprime (by norm_num),
    hm.map_mul_of_coprime (by norm_num)]
  simp [ArithmeticFunction.sigma_apply]
  decide

end Riemann.Robin

