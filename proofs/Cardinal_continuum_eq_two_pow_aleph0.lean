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

import Mathlib
/-!
# Continuum Eq Two Pow Aleph 0
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.continuum_eq_two_pow_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Cardinal

/-- The cardinality of the continuum equals `2 ^ ℵ₀`.

This is the symmetric form of Mathlib's `Cardinal.two_power_aleph0`
(`2 ^ ℵ₀ = 𝔠`), from `Mathlib/SetTheory/Cardinal/Continuum.lean`. -/
theorem continuum_eq_two_pow_aleph0 : Cardinal.continuum = 2 ^ Cardinal.aleph0 :=
  Cardinal.two_power_aleph0.symm

/-- The same statement phrased via `Cardinal.mk_real`: the cardinality of `ℝ` is `2 ^ ℵ₀`. -/
theorem mk_real_eq_two_pow_aleph0 : #ℝ = 2 ^ Cardinal.aleph0 := by
  rw [mk_real, continuum_eq_two_pow_aleph0]

end Cardinal

#print axioms Cardinal.continuum_eq_two_pow_aleph0
#print axioms Cardinal.mk_real_eq_two_pow_aleph0

