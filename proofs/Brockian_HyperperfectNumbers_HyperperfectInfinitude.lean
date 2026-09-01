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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is `k`-hyperperfect when `k > 0`, `n > 1` and `n = 1 + k * (σ(n) - n - 1)`.
The defining equation is written in subtraction-free form. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ 1 < n ∧ n + k * (n + 1) = 1 + k * sigmaOne n

/-- `n` is hyperperfect if it is `k`-hyperperfect for some `k ≥ 1`. -/
def IsHyperperfectNumber (n : ℕ) : Prop := ∃ k, IsHyperperfect k n

lemma sigmaOne_prime {p : ℕ} (hp : p.Prime) : sigmaOne p = p + 1 := by
  simp [sigmaOne, hp.divisors, Finset.sum_pair hp.one_lt.ne, Nat.add_comm]

lemma sigmaOne_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    sigmaOne (m * n) = sigmaOne m * sigmaOne n :=
  h.sum_divisors_mul

/-- Sanity check: `6` is `1`-hyperperfect (i.e. perfect). -/
lemma isHyperperfect_six : IsHyperperfect 1 6 := ⟨one_pos, by norm_num, by decide⟩

/-- Sanity check: `21` is `2`-hyperperfect. -/
lemma isHyperperfect_twentyOne : IsHyperperfect 2 21 := ⟨two_pos, by norm_num, by decide⟩

/-- **Key construction.** If `p` and `q = p² - p + 1` are both primes, then `p * q` is
`(p-1)`-hyperperfect. -/
lemma isHyperperfect_mul_of_prime_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqe : q + p = p * p + 1) : IsHyperperfect (p - 1) (p * q) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  have hk : 0 < k := by have := hp.two_le; omega
  have hqk : q = k * k + k + 1 := by nlinarith [hqe]
  have hne : k + 1 ≠ q := by
    subst hqk; nlinarith
  have hcop : (k + 1).Coprime q := (Nat.coprime_primes hp hq).mpr hne
  refine ⟨by omega, ?_, ?_⟩
  · have h1 := hp.two_le
    have h2 := hq.two_le
    nlinarith
  · rw [sigmaOne_mul_of_coprime hcop, sigmaOne_prime hp, sigmaOne_prime hq, hqk]
    simp only [Nat.add_sub_cancel]
    ring

/-- An instance of the construction: `301 = 7 * 43` is `6`-hyperperfect. -/
lemma isHyperperfect_threeHundredOne : IsHyperperfect 6 301 := by
  have h := isHyperperfect_mul_of_prime_pair (p := 7) (q := 43)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- The hypothesis that there are infinitely many primes `p` for which `p² - p + 1`
is also prime (`p = 2, 3, 7, 13, 19, 31, …`). This is an open problem. -/
def InfinitelyManyPrimePairs : Prop :=
  ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ q + p = p * p + 1

/-- **Conditional reduction of the Hyperperfect Infinitude conjecture.**
If there are infinitely many primes `p` such that `p² - p + 1` is prime, then there are
infinitely many hyperperfect numbers. -/
theorem HyperperfectInfinitude (h : InfinitelyManyPrimePairs) :
    {n : ℕ | IsHyperperfectNumber n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, q, hNp, hp, hq, hqe⟩ := h N
  refine ⟨p * q, ⟨p - 1, isHyperperfect_mul_of_prime_pair hp hq hqe⟩, ?_⟩
  have h2 := hq.two_le
  nlinarith [hp.two_le]

end Brockian.HyperperfectNumbers

