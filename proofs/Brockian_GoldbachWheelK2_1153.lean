/-
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian

/-- Auxiliary "wheel" fact for modulus `K = 2`: in any Goldbach decomposition
`r + s = 2 * 1153 = 2306` into primes, the summand `r` lies in the residue class `1 mod 2`.
The proof splits on the two cases of `r = 2` versus `r` odd: if `r = 2` then `s = 2304`,
which is not prime. -/
lemma odd_of_prime_summand_2306 {r s : ℕ} (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hsum : r + s = 2 * 1153) : r % 2 = 1 := by
  rcases hr.eq_two_or_odd with h2 | hodd
  · subst h2
    have hs' : s = 2304 := by omega
    subst hs'
    exact absurd hs (by norm_num)
  · exact hodd

/-- **Goldbach wheel (K = 2) at 1153.**  The even number `2 * 1153 = 2306` admits a
Goldbach decomposition into two primes (`2306 = 13 + 2293`), and *every* Goldbach
decomposition of `2306` uses only primes in the residue class `1 mod 2`, i.e. the
`K = 2` wheel. -/
theorem GoldbachWheelK2_1153 :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * 1153 ∧ p % 2 = 1 ∧ q % 2 = 1 ∧
      ∀ r s : ℕ, Nat.Prime r → Nat.Prime s → r + s = 2 * 1153 → r % 2 = 1 ∧ s % 2 = 1 := by
  refine ⟨13, 2293, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro r s hr hs hsum
  exact ⟨odd_of_prime_summand_2306 hr hs hsum,
    odd_of_prime_summand_2306 hs hr (by omega)⟩

end Brockian

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

