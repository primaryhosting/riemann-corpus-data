/-
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
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

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: they are distinct and each one's
sum of divisors equals the sum of the two numbers plus one. -/
def IsBetrothedPair (n m : ℕ) : Prop :=
  n ≠ m ∧ σ 1 n = n + m + 1 ∧ σ 1 m = n + m + 1

/-- The sum of divisors of a prime. -/
lemma sigma_one_prime {q : ℕ} (hq : q.Prime) : σ 1 q = q + 1 := by
  have := sigma_one_apply_prime_pow (p := q) (i := 1) hq
  simpa [Finset.sum_range_succ, add_comm] using this

/-- The sum of divisors of the square of a prime. -/
lemma sigma_one_prime_sq {q : ℕ} (hq : q.Prime) : σ 1 (q ^ 2) = 1 + q + q ^ 2 := by
  have := sigma_one_apply_prime_pow (p := q) (i := 2) hq
  simpa [Finset.sum_range_succ] using this

/-- The sum of divisors of a product of two distinct primes. -/
lemma sigma_one_mul_of_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    σ 1 (q * r) = (q + 1) * (r + 1) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_primes hq hr).2 hqr),
    sigma_one_prime hq, sigma_one_prime hr]

/-- The sum of divisors of `2 ^ k * p` for an odd prime `p`. -/
lemma sigma_one_two_pow_mul_odd_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.2 even_two) hodd
  rw [isMultiplicative_sigma.map_mul_of_coprime
      (Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))]
  have h1 : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
    rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq (by norm_num)]
    simp
  rw [h1, sigma_one_prime hp]

/-- **Unique partner.** If `m` satisfies the first betrothed equation with `n = 2 ^ k * p`
(`p` an odd prime), then necessarily `m = (2 ^ k - 1) * (p + 2)`. -/
lemma unique_partner {k p m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : σ 1 (2 ^ k * p) = 2 ^ k * p + m + 1) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, 2 ^ k = s + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  rw [sigma_one_two_pow_mul_odd_prime hp hodd, hs] at h
  have h2 : (2 : ℕ) ^ (k + 1) - 1 = 2 * s + 1 := by
    rw [pow_succ, hs]; ring_nf; omega
  rw [h2] at h
  have hm : m = s * (p + 2) := by nlinarith [h]
  rw [hm, hs]
  simp

/-- **Main theorem.** Let `k ≥ 2` and let `p` be an odd prime such that both `2 ^ k - 1` and
`p + 2` are prime. Then no natural number forms a betrothed pair with `2 ^ k * p`. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k)
    (hp : p.Prime) (hodd : Odd p) (hq : (2 ^ k - 1).Prime) (hr : (p + 2).Prime) :
    ¬ ∃ m : ℕ, IsBetrothedPair (2 ^ k * p) m := by
  rintro ⟨m, -, h1, h2⟩
  -- write `2 ^ k = s + 1`, so the Mersenne prime is `s`
  obtain ⟨s, hs⟩ : ∃ s : ℕ, 2 ^ k = s + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hs4 : 4 ≤ s + 1 := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    _ = s + 1 := hs
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.2 even_two) hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hqs : s.Prime := by rw [hs] at hq; simpa using hq
  -- the partner is forced
  have hm : m = s * (p + 2) := by
    have := unique_partner hp hodd h1
    rw [hs] at this; simpa using this
  subst hm
  rw [hs] at h2
  by_cases hcase : s = p + 2
  · -- the two auxiliary primes coincide: the partner is `(p + 2) ^ 2`
    subst hcase
    have hsq : (p + 2) * (p + 2) = (p + 2) ^ 2 := by ring
    rw [hsq, sigma_one_prime_sq hr] at h2
    nlinarith [h2, hp3]
  · rw [sigma_one_mul_of_distinct_primes hqs hr hcase] at h2
    nlinarith [h2, hs4, hp3]

end Brockian.BetrothedNumbers

