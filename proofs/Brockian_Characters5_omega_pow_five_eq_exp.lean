import Mathlib

/-!
# Omega Pow Five
Category: Characters
Target: Brockian.Characters5.omega_pow_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Brockian.Characters5

/-- The Brockian ray rotation: the primitive fifth root of unity `e^{2πi/5}`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

@[inherit_doc] notation "ω" => omega

/-- Key intermediate lemma: multiplying the exponent by `5` gives `exp (2πi)`. -/
theorem omega_pow_five_eq_exp : ω ^ 5 = Complex.exp (2 * Real.pi * Complex.I) := by
  rw [omega, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The Brockian ray rotation returns to start after five steps: `ω ^ 5 = 1`. -/
theorem omega_pow_five : ω ^ 5 = 1 := by
  rw [omega_pow_five_eq_exp]
  exact Complex.exp_two_pi_mul_I

end Brockian.Characters5

import Mathlib

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

