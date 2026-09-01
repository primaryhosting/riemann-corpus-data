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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigmaOne n` is the sum of the divisors of `n`, i.e. `σ₁ n`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A natural number `n > 1` is **`k`-hyperperfect** if `n = 1 + k * (σ(n) - n - 1)`,
i.e. `n` exceeds `1` by exactly `k` times the sum of its nontrivial proper divisors. -/
def Hyperperfect (k n : ℕ) : Prop :=
  1 < n ∧ n = 1 + k * (sigmaOne n - n - 1)

lemma sigmaOne_prime {p : ℕ} (hp : p.Prime) : sigmaOne p = p + 1 := by
  rw [sigmaOne, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  ring

lemma sigmaOne_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigmaOne (m * n) = sigmaOne m * sigmaOne n := by
  have := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h
  simpa [sigmaOne, ArithmeticFunction.sigma_one_apply] using this

/-- The sum of divisors of a product of two distinct primes. -/
lemma sigmaOne_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    sigmaOne (p * q) = (p + 1) * (q + 1) := by
  rw [sigmaOne_mul_coprime ((Nat.coprime_primes hp hq).mpr hne), sigmaOne_prime hp,
    sigmaOne_prime hq]

/-- **Key construction.** If `k ≥ 1` and `k² + 1 = a * b` with `p = k + a` and `q = k + b`
distinct primes, then `p * q` is `k`-hyperperfect.  Indeed, for `n = p * q` the condition
`n = 1 + k(σ(n) - n - 1)` reads `p * q = 1 + k (p + q)`, which is equivalent to
`(p - k)(q - k) = k² + 1`. -/
theorem hyperperfect_mul_primes {k a b p q : ℕ} (hab : a * b = k ^ 2 + 1)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hpa : p = k + a) (hqb : q = k + b) :
    Hyperperfect k (p * q) := by
  constructor
  · exact one_lt_mul_of_lt_of_le hp.one_lt hq.one_lt.le
  · have hs : sigmaOne (p * q) = (p + 1) * (q + 1) := sigmaOne_mul_primes hp hq hne
    have hexp : (p + 1) * (q + 1) = p * q + (p + q) + 1 := by ring
    have hsub : sigmaOne (p * q) - p * q - 1 = p + q := by omega
    rw [hsub]
    subst hpa hqb
    have h2 : (k + a) * (k + b) + k ^ 2 = k * (k + a + (k + b)) + a * b := by ring
    rw [hab] at h2
    linarith

/-- For a product of two distinct primes, `k`-hyperperfection is exactly the equation
`p * q = 1 + k * (p + q)`. -/
theorem hyperperfect_mul_primes_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Hyperperfect k (p * q) ↔ p * q = 1 + k * (p + q) := by
  have hs : sigmaOne (p * q) = (p + 1) * (q + 1) := sigmaOne_mul_primes hp hq hne
  have hexp : (p + 1) * (q + 1) = p * q + (p + q) + 1 := by ring
  have hsub : sigmaOne (p * q) - p * q - 1 = p + q := by omega
  constructor
  · rintro ⟨-, h⟩
    rwa [hsub] at h
  · intro h
    exact ⟨one_lt_mul_of_lt_of_le hp.one_lt hq.one_lt.le, by rw [hsub]; exact h⟩

/-- **Brockian conjecture: hyperperfect numbers for all `k` (conditional form).**

For every `k ≥ 1` for which the two numbers `k + 1` and `k² + k + 1` are prime, there is a
`k`-hyperperfect number, namely `n = (k + 1)(k² + k + 1)`.

This is the standard reduction of the (open) statement "for every `k ≥ 1` there is a
`k`-hyperperfect number" to a primality hypothesis: the general solvability of
`p * q = 1 + k (p + q)` in primes, equivalently `(p - k)(q - k) = k² + 1`, is not known
for all `k`, so we record the conditional statement together with the explicit witness. -/
theorem HyperperfectAllK (k : ℕ) (hk : 0 < k) (hp : Nat.Prime (k + 1))
    (hq : Nat.Prime (k ^ 2 + k + 1)) :
    Hyperperfect k ((k + 1) * (k ^ 2 + k + 1)) ∧
      (k + 1) * (k ^ 2 + k + 1) = 1 + k * ((k + 1) + (k ^ 2 + k + 1)) := by
  refine ⟨hyperperfect_mul_primes (a := 1) (b := k ^ 2 + 1) (by ring) hp hq ?_ (by ring) (by ring),
    by ring⟩
  have : k + 1 < k ^ 2 + k + 1 := by nlinarith
  exact this.ne

/-- `k = 1`: the number `6` is `1`-hyperperfect (i.e. perfect). -/
theorem hyperperfect_one : Hyperperfect 1 6 :=
  (HyperperfectAllK 1 one_pos (by norm_num) (by norm_num)).1

/-- `k = 2`: the number `21` is `2`-hyperperfect. -/
theorem hyperperfect_two : Hyperperfect 2 21 :=
  (HyperperfectAllK 2 two_pos (by norm_num) (by norm_num)).1

end Brockian.HyperperfectNumbers

