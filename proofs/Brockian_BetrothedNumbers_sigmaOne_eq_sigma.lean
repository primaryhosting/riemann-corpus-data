import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

theorem sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = ArithmeticFunction.sigma 1 n := by
  rw [sigmaOne, ArithmeticFunction.sigma_one_apply]

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers each of whose
sum of divisors equals the sum of the two numbers plus one. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- Kernel-verified computation of `σ₁ 5775`. -/
theorem sigmaOne_5775 : sigmaOne 5775 = 11904 := by
  rw [sigmaOne]; decide

/-- Kernel-verified computation of `σ₁ 6128`. -/
theorem sigmaOne_6128 : sigmaOne 6128 = 11904 := by
  rw [sigmaOne]; decide

/-- `(5775, 6128)` is a betrothed pair. -/
theorem betrothed_5775_6128 : IsBetrothedPair 5775 6128 :=
  ⟨by norm_num, by norm_num, by norm_num, by rw [sigmaOne_5775], by rw [sigmaOne_6128]⟩

section Criterion

private theorem sum_range_two_pow (k : ℕ) : ∑ j ∈ range (k + 1), 2 ^ j = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      ring_nf
      omega

/-- `σ₁` of an odd prime times a power of two. -/
theorem sigmaOne_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    sigmaOne (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.coprime_primes Nat.prime_two hp]
    exact fun h => hp2 h.symm
  have hmul := ArithmeticFunction.isMultiplicative_sigma (k := 1) |>.map_mul_of_coprime hcop
  rw [sigmaOne_eq_sigma, hmul, ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
    sum_range_two_pow]
  congr 1
  rw [ArithmeticFunction.sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega

/-- The `σ`-criterion generating a betrothed pair whose even member is `2 ^ k * p`
for an odd prime `p`: if `m` is a positive number distinct from `2 ^ k * p` with
`σ₁ m = (2 ^ (k+1) - 1) * (p + 1)` and `m + 2 ^ k * p + 1` equals that same value,
then `(m, 2 ^ k * p)` is a betrothed pair. -/
theorem isBetrothedPair_of_sigma_criterion {k p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : 0 < m) (hne : m ≠ 2 ^ k * p)
    (hsm : sigmaOne m = (2 ^ (k + 1) - 1) * (p + 1))
    (hsum : m + 2 ^ k * p + 1 = (2 ^ (k + 1) - 1) * (p + 1)) :
    IsBetrothedPair m (2 ^ k * p) := by
  refine ⟨hm, ?_, hne, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.two_pow_pos k) hp.pos
  · rw [hsm, hsum]
  · rw [sigmaOne_two_pow_mul_prime hp hp2, hsum]

/-- The pair `(5775, 6128)` arises from the `σ`-criterion with `k = 4`, `p = 383`:
`6128 = 2 ^ 4 * 383` with `383` prime, and `σ₁ 5775 = (2 ^ 5 - 1) * (383 + 1) = 5775 + 6128 + 1`. -/
theorem betrothed_5775_6128_of_criterion : IsBetrothedPair 5775 6128 := by
  have hp : Nat.Prime 383 := by norm_num
  have h : IsBetrothedPair 5775 (2 ^ 4 * 383) := by
    refine isBetrothedPair_of_sigma_criterion hp (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · rw [sigmaOne_5775]; norm_num
    · norm_num
  norm_num at h
  exact h

/-- The generating data: `383` is prime, `6128 = 2 ^ 4 * 383`, and both members have
sum of divisors `(2 ^ 5 - 1) * (383 + 1) = 5775 + 6128 + 1`. -/
theorem betrothed_5775_6128_sigma_criterion_data :
    Nat.Prime 383 ∧ 6128 = 2 ^ 4 * 383 ∧
      sigmaOne (2 ^ 4 * 383) = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      sigmaOne 5775 = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      (2 ^ (4 + 1) - 1) * (383 + 1) = 5775 + 6128 + 1 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, by norm_num⟩
  · rw [sigmaOne_two_pow_mul_prime (by norm_num) (by norm_num)]
  · rw [sigmaOne_5775]; norm_num

end Criterion

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

