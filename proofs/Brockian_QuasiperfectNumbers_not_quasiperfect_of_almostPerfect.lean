import Mathlib

/-!
# Quasiperfect numbers and the three σ-regimes

Let `σ(n) = ∑_{d ∣ n} d` be the sum of **all** divisors of `n` (so `σ(n)` counts
`n` itself, unlike the aliquot / proper-divisor sum). Comparing `σ(n)` against `2n`
splits the positive integers into a clean three-regime picture at the boundary:

| regime            | defining equation | status                                   |
|-------------------|-------------------|------------------------------------------|
| **almost-perfect**| `σ(n) = 2n − 1`   | exist — exactly the powers of two        |
| **perfect**       | `σ(n) = 2n`       | exist — `6, 28, 496, …` (Euclid–Euler)   |
| **quasiperfect**  | `σ(n) = 2n + 1`   | **OPEN** — none is known to exist        |

## What is a theorem here vs. what is open

Proved below (kernel-verified, no `sorry`/`native_decide`/added axiom):

* `almostPerfect_pow_two` — the **general** theorem that every power of two `2^k`
  is almost-perfect, via `σ(2^k) = 2^{k+1} − 1 = 2·2^k − 1`;
* concrete almost-perfect instances `1, 2, 16` and perfect instances `6, 28`;
* the three regimes are **mutually exclusive**: an almost-perfect or perfect
  number is never quasiperfect (the σ-values `2n−1, 2n, 2n+1` are distinct).

What is genuinely **open** is whether any quasiperfect number exists at all. None
is known; if one exists it is an odd perfect square exceeding `10^35`. This open
statement is recorded only as an unproven `def` `QuasiperfectExists` of type `Prop`;
it is **neither asserted nor denied** anywhere in this file.

## References
* Quasiperfect number: <https://en.wikipedia.org/wiki/Quasiperfect_number>
* Almost perfect number: <https://en.wikipedia.org/wiki/Almost_perfect_number>
-/

namespace Brockian.QuasiperfectNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Sum of **all** divisors of `n` (the arithmetic `σ₁`, counting `n` itself). -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- **Almost-perfect**: `σ(n) = 2n − 1`. The powers of two are exactly these. -/
def AlmostPerfect (n : ℕ) : Prop := 0 < n ∧ sigma1 n = 2 * n - 1

/-- **Perfect** (via the σ-form): `σ(n) = 2n`. Same content as `Nat.Perfect n`. -/
def Perfectσ (n : ℕ) : Prop := 0 < n ∧ sigma1 n = 2 * n

/-- **Quasiperfect**: `σ(n) = 2n + 1`. -/
def Quasiperfect (n : ℕ) : Prop := 0 < n ∧ sigma1 n = 2 * n + 1

/-- OPEN: does a quasiperfect number exist? **None is known.** Recorded as an
unproven `def`; this file neither asserts nor denies it. -/
def QuasiperfectExists : Prop := ∃ n : ℕ, Quasiperfect n

/-! ## The flagship: powers of two are almost-perfect -/

/-- `σ(2^k) = 2^{k+1} − 1`. Proved from the geometric-sum identity for the divisor
sum of a prime power (this is the Mersenne value `mersenne (k+1)`; the Archive proof
of Theorem 70 uses the same step, reproduced here since the Archive is unavailable
under `import Mathlib`). -/
theorem sigma_two_pow (k : ℕ) : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  simp_rw [sigma_one_apply, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- **FLAGSHIP.** Every power of two is almost-perfect: `σ(2^k) = 2·2^k − 1`. -/
theorem almostPerfect_pow_two (k : ℕ) : AlmostPerfect (2 ^ k) := by
  refine ⟨by positivity, ?_⟩
  have h1 : sigma1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
    rw [show sigma1 (2 ^ k) = σ 1 (2 ^ k) from (sigma_one_apply _).symm, sigma_two_pow]
  rw [h1, pow_succ]
  omega

/-! ## Concrete verified instances -/

/-- `σ(1) = 1 = 2·1 − 1`. -/
theorem almostPerfect_1 : AlmostPerfect 1 := ⟨by decide, by decide⟩

/-- `σ(2) = 1 + 2 = 3 = 2·2 − 1`. -/
theorem almostPerfect_2 : AlmostPerfect 2 := ⟨by decide, by decide⟩

set_option maxRecDepth 8000 in
/-- `σ(16) = 1 + 2 + 4 + 8 + 16 = 31 = 2·16 − 1` (also an instance of the flagship). -/
theorem almostPerfect_16 : AlmostPerfect 16 := ⟨by decide, by decide⟩

/-- `σ(6) = 1 + 2 + 3 + 6 = 12 = 2·6` — the smallest perfect number. -/
theorem perfectσ_6 : Perfectσ 6 := ⟨by decide, by decide⟩

set_option maxRecDepth 8000 in
/-- `σ(28) = 1 + 2 + 4 + 7 + 14 + 28 = 56 = 2·28` — the second perfect number. -/
theorem perfectσ_28 : Perfectσ 28 := ⟨by decide, by decide⟩

/-! ## The three regimes are mutually exclusive -/

/-- An almost-perfect number (`σ = 2n − 1`) is never quasiperfect (`σ = 2n + 1`). -/
theorem not_quasiperfect_of_almostPerfect {n : ℕ} (h : AlmostPerfect n) :
    ¬ Quasiperfect n := by
  rintro ⟨_, hq⟩
  obtain ⟨hpos, ha⟩ := h
  omega

/-- A perfect number (`σ = 2n`) is never quasiperfect (`σ = 2n + 1`). -/
theorem not_quasiperfect_of_perfectσ {n : ℕ} (h : Perfectσ n) :
    ¬ Quasiperfect n := by
  rintro ⟨_, hq⟩
  obtain ⟨hpos, hp⟩ := h
  omega

end Brockian.QuasiperfectNumbers
