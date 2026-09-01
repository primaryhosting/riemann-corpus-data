/-
# Pair 11 13
Category: Frontier — Prime Numbers
Target: Twin.pair_11_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pair 11 13
Category: Frontier — Prime Numbers
Target: Twin.pair_11_13
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

namespace Twin

/-- 11 and 13 are twin primes: both are prime and their difference is 2. -/
theorem pair_11_13 : Nat.Prime 11 ∧ Nat.Prime 13 ∧ 13 - 11 = 2 :=
  ⟨by norm_num, by norm_num, by norm_num⟩

end Twin

