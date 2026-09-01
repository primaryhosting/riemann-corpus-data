import Mathlib

/-!
# Fundamental Theorem Of Algebra
Category: Frontier Wave 2 (deeper machinery)
Target: Algebra.fundamental_theorem_of_algebra
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

namespace Algebra

/-- **Fundamental theorem of algebra**: every non-constant complex polynomial has a root. -/
theorem fundamental_theorem_of_algebra (p : Polynomial Complex) (hp : 0 < p.degree) :
    ∃ z : Complex, p.eval z = 0 :=
  Complex.exists_root hp

end Algebra

