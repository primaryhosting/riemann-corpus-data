/-
# Value At Two
Category: Riemann Program
Target: Riemann.Zeta.value_at_two
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.Zeta

/-- Euler's evaluation of the Riemann zeta function at `2`: `ζ(2) = π² / 6`. -/
theorem value_at_two : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 :=
  riemannZeta_two

end Riemann.Zeta

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

