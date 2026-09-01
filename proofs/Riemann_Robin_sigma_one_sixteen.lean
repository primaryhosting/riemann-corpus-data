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

open ArithmeticFunction

/-- `σ₁(16) = 1 + 2 + 4 + 8 + 16 = 31`. -/
lemma sigma_one_sixteen : ArithmeticFunction.sigma 1 16 = 31 := by
  simp [ArithmeticFunction.sigma_one_apply]
  decide

/-- `σ₁(9) = 1 + 3 + 9 = 13`. -/
lemma sigma_one_nine : ArithmeticFunction.sigma 1 9 = 13 := by
  simp [ArithmeticFunction.sigma_one_apply]
  decide

/-- `σ₁(5) = 1 + 5 = 6`. -/
lemma sigma_one_five : ArithmeticFunction.sigma 1 5 = 6 := by
  simp [ArithmeticFunction.sigma_one_apply]
  decide

/-- `σ₁(7) = 1 + 7 = 8`. -/
lemma sigma_one_seven : ArithmeticFunction.sigma 1 7 = 8 := by
  simp [ArithmeticFunction.sigma_one_apply]
  decide

/-- The sum of divisors of `5040 = 2^4 * 3^2 * 5 * 7` is `19344`, computed via the
multiplicativity of `σ₁`:  `31 * 13 * 6 * 8 = 19344`. -/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  have hm := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have e : (5040 : ℕ) = 16 * (9 * (5 * 7)) := by norm_num
  rw [e, hm.map_mul_of_coprime (by decide), hm.map_mul_of_coprime (by decide),
    hm.map_mul_of_coprime (by decide), sigma_one_sixteen, sigma_one_nine, sigma_one_five,
    sigma_one_seven]
  norm_num

end Riemann.Robin

