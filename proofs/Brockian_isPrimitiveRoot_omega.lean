import Mathlib

/-!
# Sum Omega Pow
Category: Characters
Target: Brockian.Characters5.sum_omega_pow
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

namespace Brockian
namespace Characters5

/-- The primitive 5th root of unity `ω = exp(2πi/5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

local notation "ω" => omega

/-- `ω` is a primitive 5th root of unity. -/
theorem isPrimitiveRoot_omega : IsPrimitiveRoot ω 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- `ω ^ 5 = 1`. -/
theorem omega_pow_five : ω ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

/-- The sum of all five 5th roots of unity vanishes. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, ω ^ k = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

end Characters5
end Brockian

