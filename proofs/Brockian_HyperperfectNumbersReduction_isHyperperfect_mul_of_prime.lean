import Mathlib

/-!
# Hyperperfect Infinitude — conditional reduction module

CONDITIONAL: infinitude of hyperperfect numbers (`Hyperperfect.Infinite`) assuming
`H : {p : ℕ | p.Prime ∧ (p ^ 2 - p + 1).Prime}.Infinite` (there are infinitely many primes
`p` for which `p² - p + 1` is also prime — the Minoli–Bear construction family).

Graduated from AXLE-verified Aristotle reduction
`Brockian.HyperperfectNumbers.HyperperfectInfinitude`. Renamed namespace to avoid clashing
with the existing `Brockian/HyperperfectNumbers.lean` module.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbersReduction

/-- `n` is `k`-hyperperfect when `k ≥ 1`, `n > 1` and `n = 1 + k * (σ n - n - 1)`, i.e. `k`
times the sum of the divisors of `n` other than `1` and `n` equals `n - 1`.
The equation is written without truncated subtraction as `n + k * (n + 1) = 1 + k * σ n`. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  1 ≤ k ∧ 1 < n ∧ n + k * (n + 1) = 1 + k * (σ 1 n)

/-- The set of hyperperfect numbers (`k`-hyperperfect for some `k ≥ 1`). -/
def Hyperperfect : Set ℕ := {n | ∃ k, IsHyperperfect k n}

/-- The sum-of-divisors function on a product of two distinct primes. -/
theorem sigma_one_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    σ 1 (p * q) = (p + 1) * (q + 1) := by
  have hmul := (isMultiplicative_sigma (k := 1) :
      ArithmeticFunction.IsMultiplicative (σ 1 : ArithmeticFunction ℕ)).map_mul_of_coprime
      ((Nat.coprime_primes hp hq).mpr hpq)
  rw [hmul, sigma_one_apply, sigma_one_apply, hp.sum_divisors, hq.sum_divisors]

/-- **Key lemma.** If `p` and `q = p² - p + 1` are both prime, then `n = p * q` is
`(p-1)`-hyperperfect. (For `p = 2` this gives the perfect number `6`, for `p = 3` the
`2`-hyperperfect number `21`, for `p = 7` the `6`-hyperperfect number `301`.) -/
theorem isHyperperfect_mul_of_prime {p : ℕ} (hp : p.Prime) (hq : (p ^ 2 - p + 1).Prime) :
    IsHyperperfect (p - 1) (p * (p ^ 2 - p + 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hsq : (a + 2) ^ 2 = a ^ 2 + 4 * a + 4 := by ring
  have hq' : (a + 2) ^ 2 - (a + 2) + 1 = a ^ 2 + 3 * a + 3 := by omega
  rw [hq'] at hq ⊢
  have hlt : a + 2 < a ^ 2 + 3 * a + 3 := by nlinarith [sq_nonneg a]
  have hne : a + 2 ≠ a ^ 2 + 3 * a + 3 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · nlinarith [sq_nonneg a]
  · rw [sigma_one_mul_of_primes hp hq hne]
    have hk : a + 2 - 1 = a + 1 := by omega
    rw [hk]
    ring

/-- Each such `p * q` is at least `p`, so the family is unbounded. -/
theorem le_mul_of_prime {p : ℕ} (hp : p.Prime) : p ≤ p * (p ^ 2 - p + 1) := by
  have h2 := hp.two_le
  have h1 : 1 ≤ p ^ 2 - p + 1 := by omega
  nlinarith

/-- **Conditional reduction for the Brockian hyperperfect infinitude conjecture.**

If there are infinitely many primes `p` for which `p² - p + 1` is also prime, then there are
infinitely many hyperperfect numbers: indeed each such `p` produces the `(p-1)`-hyperperfect
number `p * (p² - p + 1)`. -/
theorem HyperperfectInfinitude
    (h : {p : ℕ | p.Prime ∧ (p ^ 2 - p + 1).Prime}.Infinite) :
    Hyperperfect.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨p, ⟨hp, hq⟩, hpN⟩ := h.exists_gt N
  have hmem : p * (p ^ 2 - p + 1) ∈ Hyperperfect :=
    ⟨p - 1, isHyperperfect_mul_of_prime hp hq⟩
  have h1 := hN hmem
  have h2 := le_mul_of_prime hp
  omega

end Brockian.HyperperfectNumbersReduction
