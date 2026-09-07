/-
  Brockian/DivisorSumStructure.lean — general structural theorems for the
  divisor-sum function σ.

  These are GENERAL σ-structure theorems (not concrete numerical instances):
  they constrain the whole perfect / abundant / deficient frontier by pinning
  down how the divisor sum `σ 1 n = ∑ d ∈ n.divisors, d` behaves relative to
  `n` itself. The concrete perfect/abundant/deficient classification of any
  particular `n` is a corollary of facts like these.

  Naming note: Mathlib does NOT expose a `Nat.sigma`. The divisor-power sum is
  `ArithmeticFunction.sigma` (with scoped notation `σ`), where
  `ArithmeticFunction.sigma 1 n = ∑ d ∈ n.divisors, d`
  (`ArithmeticFunction.sigma_one_apply`). We therefore phrase every theorem in
  terms of `ArithmeticFunction.sigma 1 n`; the mathematical content is exactly
  the divisor sum intended by the specification.

  Contents:
    * `sigma_ge_succ`            — σ(n) ≥ n + 1 for n ≥ 2 (1 and n are distinct divisors).
    * `sigma_eq_succ_iff_prime`  — σ(n) = n + 1 ⇔ n is prime (for n ≥ 2).
    * `prime_pow_deficient`      — σ(p^k) < 2·p^k: prime powers are deficient.
    * `perfect_not_prime`        — a perfect number is not prime.
    * `prime_pow_not_perfect`    — prime powers are never perfect.

  Verification:
    - AXLE independent : verified @ lean-4.32.0
  No `sorry`, `admit`, `native_decide`, or `axiom` is used anywhere in this file.
-/
import Mathlib

open Finset

namespace Brockian.DivisorSumStructure

/-- **Divisor sum lower bound.** For `n ≥ 2`, both `1` and `n` are divisors of
`n` and they are distinct, so the divisor sum is at least `n + 1`. -/
theorem sigma_ge_succ {n : ℕ} (hn : 2 ≤ n) :
    n + 1 ≤ ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply]
  have hn0 : n ≠ 0 := by omega
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.one_mem_divisors.mpr hn0
    · exact Nat.mem_divisors_self _ hn0
  have hpair : (∑ x ∈ ({1, n} : Finset ℕ), x) = 1 + n :=
    Finset.sum_pair (by omega : (1 : ℕ) ≠ n)
  have hle : (∑ x ∈ ({1, n} : Finset ℕ), x) ≤ ∑ x ∈ n.divisors, x :=
    Finset.sum_le_sum_of_subset hsub
  rw [hpair] at hle
  omega

/-- **Primes are exactly the `σ(n) = n + 1` case.** For `n ≥ 2`, the divisor sum
equals `n + 1` precisely when `n` is prime: the divisors of a prime are `{1, n}`
(⇐), and conversely if any nontrivial proper divisor `m` existed then
`{1, m, n}` would already force `σ(n) ≥ 1 + m + n > n + 1` (⇒). -/
theorem sigma_eq_succ_iff_prime {n : ℕ} (hn : 2 ≤ n) :
    ArithmeticFunction.sigma 1 n = n + 1 ↔ n.Prime := by
  rw [ArithmeticFunction.sigma_one_apply]
  have hn0 : n ≠ 0 := by omega
  constructor
  · intro hsum
    rw [Nat.prime_def_lt']
    refine ⟨hn, ?_⟩
    intro m hm2 hmn hmdvd
    have hmem : m ∈ n.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hn0⟩
    have hsub : ({1, m, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Nat.one_mem_divisors.mpr hn0
      · exact hmem
      · exact Nat.mem_divisors_self _ hn0
    have h1 : (1 : ℕ) ∉ ({m, n} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2 : m ∉ ({n} : Finset ℕ) := by
      simp only [Finset.mem_singleton]; omega
    have hcard : (∑ x ∈ ({1, m, n} : Finset ℕ), x) = 1 + m + n := by
      rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]; omega
    have hle : (∑ x ∈ ({1, m, n} : Finset ℕ), x) ≤ ∑ x ∈ n.divisors, x :=
      Finset.sum_le_sum_of_subset hsub
    rw [hsum, hcard] at hle
    omega
  · intro hp
    rw [Nat.Prime.divisors hp, Finset.sum_pair (by omega : (1 : ℕ) ≠ n)]
    omega

/-- **Prime powers are deficient.** For a prime `p` and `k ≥ 1`, the divisor sum
`σ(p^k) = 1 + p + ⋯ + p^k` is strictly below `2·p^k`. This is the σ-form of
`Nat.Prime.deficient_pow`. -/
theorem prime_pow_deficient {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ArithmeticFunction.sigma 1 (p ^ k) < 2 * p ^ k := by
  have hd : ∑ i ∈ (p ^ k).properDivisors, i < p ^ k := hp.deficient_pow
  rw [ArithmeticFunction.sigma_one_apply,
      Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- **A perfect number is not prime.** Immediate from `Nat.Prime.not_perfect`
(equivalently, `σ(prime) = prime + 1 ≠ 2·prime`). -/
theorem perfect_not_prime {n : ℕ} (hn : Nat.Perfect n) : ¬ n.Prime :=
  fun hp => hp.not_perfect hn

/-- **Prime powers are never perfect.** Deficiency (theorem `prime_pow_deficient`
in σ-form / `Nat.Prime.deficient_pow`) is incompatible with the perfect
condition `∑ properDivisors (p^k) = p^k`. -/
theorem prime_pow_not_perfect {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ¬ Nat.Perfect (p ^ k) := by
  intro hperf
  have hd : ∑ i ∈ (p ^ k).properDivisors, i < p ^ k := hp.deficient_pow
  have he : ∑ i ∈ (p ^ k).properDivisors, i = p ^ k := hperf.1
  omega

end Brockian.DivisorSumStructure
