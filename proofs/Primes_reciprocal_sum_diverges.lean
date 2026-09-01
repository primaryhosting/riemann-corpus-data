/-!
# Reciprocal Sum Diverges
Category: Frontier — Prime Numbers
Target: Primes.reciprocal_sum_diverges
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Primes

/-- **Euler's theorem on the divergence of the sum of prime reciprocals.**
The family `p ↦ 1 / p`, indexed by the primes, is not summable. -/
theorem reciprocal_sum_diverges : ¬ Summable (fun p : Nat.Primes ↦ (1 / p : ℝ)) :=
  Nat.Primes.not_summable_one_div

/-- Equivalent phrasing: the indicator function of the primes, `n ↦ 1/n` supported on primes,
is not summable over `ℕ`. -/
theorem reciprocal_sum_diverges' :
    ¬ Summable (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n)) :=
  Nat.not_summable_indicator_one_div_natCast Nat.setOf_prime_infinite 0

end Primes

