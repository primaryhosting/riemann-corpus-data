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
# Infinitude
Category: Frontier — Prime Numbers
Target: Primes.infinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Primes

/-- There are infinitely many primes: for every natural `n` there is a prime `p` with `n ≤ p`. -/
theorem infinitude : ∀ n : ℕ, ∃ p : ℕ, n ≤ p ∧ Nat.Prime p :=
  fun n => Nat.exists_infinite_primes n

end Primes

