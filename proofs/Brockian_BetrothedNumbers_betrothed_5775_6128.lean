/-
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Two distinct positive naturals `m ≠ n` form a *betrothed* (quasi-amicable) pair when the
sum of the proper divisors of each, excluding `1`, gives the other; equivalently
`σ 1 m = σ 1 n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- `σ 1 5775 = 11904`, verified by kernel computation. -/
theorem sigma_one_5775 : σ 1 5775 = 11904 := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  decide

/-- `σ 1 6128 = 11904`, verified by kernel computation. -/
theorem sigma_one_6128 : σ 1 6128 = 11904 := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  decide

/-- **(5775, 6128) is a betrothed (quasi-amicable) pair.** -/
theorem betrothed_5775_6128 : IsBetrothedPair 5775 6128 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [sigma_one_5775]
  · rw [sigma_one_6128]

/-- The `σ`-value of `2 ^ k * p` for an odd prime `p`: `σ 1 (2 ^ k * p) = (2 ^ (k+1) - 1) * (p+1)`. -/
theorem sigma_one_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_apply_prime_pow Nat.prime_two, ← pow_one p,
    sigma_one_apply_prime_pow hp]
  simp only [Nat.geomSum_eq (le_refl 2), Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, zero_add]
  norm_num [Nat.add_comm 1 p]

/-- The pair `(5775, 6128)` arises from the `k = 4`, `p = 383` sigma criterion:
`383` is prime, `6128 = 2 ^ 4 * 383`, and the common value
`σ 1 6128 = (2 ^ 5 - 1) * (383 + 1) = 11904` equals `5775 + 6128 + 1 = σ 1 5775`. -/
theorem betrothed_5775_6128_sigma_criterion :
    Nat.Prime 383 ∧ (6128 : ℕ) = 2 ^ 4 * 383 ∧
      σ 1 6128 = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      σ 1 5775 = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      (2 ^ (4 + 1) - 1) * (383 + 1) = 5775 + 6128 + 1 := by
  have hp : Nat.Prime 383 := by norm_num
  refine ⟨hp, by norm_num, ?_, ?_, by norm_num⟩
  · have h := sigma_one_two_pow_mul_prime (k := 4) hp (by norm_num)
    rw [show (6128 : ℕ) = 2 ^ 4 * 383 by norm_num, h]
  · rw [sigma_one_5775]; norm_num

end Brockian.BetrothedNumbers

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

