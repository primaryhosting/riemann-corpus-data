import Mathlib
/-!
# Reciprocal Sum Diverges
Category: Frontier — Prime Numbers
Target: Primes.reciprocal_sum_diverges
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

namespace Primes

/-- **Euler**: the sum of the reciprocals of the primes diverges, i.e. the family
`p ↦ 1 / p` indexed by the primes is not summable. -/
theorem reciprocal_sum_diverges : ¬ Summable (fun p : Nat.Primes => (1 : ℝ) / (p : ℕ)) := by
  intro h
  exact not_summable_one_div_on_primes
    ((summable_subtype_iff_indicator (s := {p : ℕ | Nat.Prime p})
      (f := fun n : ℕ => (1 : ℝ) / n)).mp h)

end Primes

