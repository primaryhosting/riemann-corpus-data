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

/-
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *`k`-hyperperfect* when `n = 1 + k * (σ n - n - 1)`, where `σ` is the
sum-of-divisors function.  For `k = 1` these are exactly the perfect numbers.  The conjecture
addressed here states that **for every `k ≥ 1` there exists a `k`-hyperperfect number**; this is
an open problem (no `5`-hyperperfect number is known, for instance).

This file contains:

* the basic theory (`sigma`, `IsHyperperfect`, and the usual integer form of the equation);
* an exact characterisation of the hyperperfect numbers of the shape `m * q` with `q` a prime not
  dividing `m` (`isHyperperfect_mul_prime_iff`), and the resulting construction
  (`isHyperperfect_of_seed`);
* the classical semiprime family: if `k + 1` and `k ^ 2 + k + 1` are prime then
  `(k + 1) * (k ^ 2 + k + 1)` is `k`-hyperperfect (`isHyperperfect_classical`), together with the
  full semiprime characterisation `(p - k) * (q - k) = k ^ 2 + 1`;
* unconditional witnesses for a number of small `k` (`exists_hyperperfect_of_small`);
* the main target `HyperperfectAllK`: a Lean-checked reduction of the conjecture to the
  arithmetic hypothesis `SeedHypothesis`.
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigma n` is the sum of the (positive) divisors of `n`, usually written `σ(n)`. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

lemma sigma_eq_sigmaOne (n : ℕ) : sigma n = ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply, sigma]

/-- `n` is **`k`-hyperperfect** when `n = 1 + k * (σ n - n - 1)`, i.e. `n` exceeds by `1` the
number `k` times the sum of its divisors other than `1` and `n`.  The defining equation is
written here in a subtraction-free form, valid in `ℕ`: `k * σ n + 1 = n + k * (n + 1)`. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  1 < n ∧ k * sigma n + 1 = n + k * (n + 1)

/-- The defining equation in its usual form, over the integers. -/
lemma isHyperperfect_iff_int (k n : ℕ) :
    IsHyperperfect k n ↔ 1 < n ∧ (n : ℤ) = 1 + k * ((sigma n : ℤ) - n - 1) := by
  unfold IsHyperperfect
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    have h' : ((k * sigma n + 1 : ℕ) : ℤ) = ((n + k * (n + 1) : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linarith
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    have h' : ((k : ℤ) * sigma n + 1) = ((n : ℤ) + k * (n + 1)) := by linarith
    exact_mod_cast h'

/-- `1` is `k`-perfect for no `k`: the perfect numbers are the `1`-hyperperfect numbers. -/
lemma isHyperperfect_one_iff_perfect (n : ℕ) (hn : 0 < n) :
    IsHyperperfect 1 n ↔ n.Perfect := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hn]
  unfold IsHyperperfect
  constructor
  · rintro ⟨hn1, h⟩
    have : sigma n = 2 * n := by omega
    simpa [sigma] using this
  · intro h
    have hs : sigma n = 2 * n := by simpa [sigma] using h
    refine ⟨?_, by omega⟩
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n
      · simp [sigma] at hs
    · omega

/-! ### Sum of divisors of the shapes we need -/

/-- The sum of divisors of a prime `p` is `p + 1`. -/
lemma sigma_prime {p : ℕ} (hp : p.Prime) : sigma p = p + 1 := by
  rw [sigma, hp.divisors, Finset.sum_insert (by simp [hp.one_lt.ne]), Finset.sum_singleton,
    add_comm]

/-- The sum of divisors of a prime power. -/
lemma sigma_prime_pow {p : ℕ} (hp : p.Prime) (s : ℕ) :
    sigma (p ^ s) = ∑ i ∈ Finset.range (s + 1), p ^ i := by
  rw [sigma, Nat.sum_divisors_prime_pow hp]

/-- `sigma` is multiplicative on coprime arguments. -/
lemma sigma_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigma (m * n) = sigma m * sigma n := by
  rw [sigma, h.sum_divisors_mul, ← sigma, ← sigma]

/-- The sum of divisors of a product of two distinct primes. -/
lemma sigma_prime_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    sigma (p * q) = (p + 1) * (q + 1) := by
  rw [sigma_mul_of_coprime ((Nat.coprime_primes hp hq).mpr hpq), sigma_prime hp, sigma_prime hq]

/-! ### Hyperperfect numbers with a prime factor of multiplicity one -/

/-- **Characterisation.**  For `m > 1` and a prime `q` not dividing `m`, the number `m * q` is
`k`-hyperperfect exactly when `k * σ m * (q + 1) + 1 = m * q * (1 + k) + k`. -/
theorem isHyperperfect_mul_prime_iff {k m q : ℕ} (hm : 1 < m) (hq : q.Prime) (hqm : ¬ q ∣ m) :
    IsHyperperfect k (m * q) ↔ k * sigma m * (q + 1) + 1 = m * q * (1 + k) + k := by
  have hcop : Nat.Coprime m q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqm).symm
  have hs : sigma (m * q) = sigma m * (q + 1) := by
    rw [sigma_mul_of_coprime hcop, sigma_prime hq]
  have hn : 1 < m * q := by
    have := hq.two_le
    nlinarith
  have harith : m * q + k * (m * q + 1) = m * q * (1 + k) + k := by ring
  unfold IsHyperperfect
  rw [hs, harith, ← mul_assoc]
  exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩

/-- **Main construction.**  A "seed" `m > 1` together with a prime `q ∤ m` satisfying the
displayed equation produces the `k`-hyperperfect number `m * q`. -/
theorem isHyperperfect_of_seed {k m q : ℕ} (hm : 1 < m) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (h : k * sigma m * (q + 1) + 1 = m * q * (1 + k) + k) :
    IsHyperperfect k (m * q) :=
  (isHyperperfect_mul_prime_iff hm hq hqm).mpr h

/-! ### The classical semiprime family -/

/-- **Characterisation of hyperperfect semiprimes.**  If `k + a` and `k + b` are distinct primes,
then `(k + a) * (k + b)` is `k`-hyperperfect if and only if `a * b = k ^ 2 + 1`.  (Equivalently,
for distinct primes `p, q > k`: `p * q` is `k`-hyperperfect iff `(p - k) * (q - k) = k ^ 2 + 1`.) -/
theorem isHyperperfect_prime_mul_prime_iff {k a b : ℕ} (ha : (k + a).Prime) (hb : (k + b).Prime)
    (hab : k + a ≠ k + b) :
    IsHyperperfect k ((k + a) * (k + b)) ↔ a * b = k ^ 2 + 1 := by
  have hs : sigma ((k + a) * (k + b)) = (k + a + 1) * (k + b + 1) :=
    sigma_prime_mul_prime ha hb hab
  have hn : 1 < (k + a) * (k + b) := by
    have h2a := ha.two_le
    have h2b := hb.two_le
    nlinarith
  unfold IsHyperperfect
  rw [hs]
  constructor
  · rintro ⟨-, h⟩
    zify at h ⊢
    linarith [h]
  · intro h
    refine ⟨hn, ?_⟩
    zify at h ⊢
    linear_combination -h

/-- A number of the shape `k ^ 2 + 1` is never a perfect square when `k ≥ 1`; hence in a
factorisation `a * b = k ^ 2 + 1` the two factors differ. -/
lemma ne_of_mul_eq_sq_add_one {k a b : ℕ} (hk : 1 ≤ k) (hab : a * b = k ^ 2 + 1) : a ≠ b := by
  rintro rfl
  rcases le_or_gt a k with h | h
  · nlinarith
  · nlinarith

/-- For any factorisation `a * b = k ^ 2 + 1` with `k ≥ 1` such that both `k + a` and `k + b` are
prime, the number `(k + a) * (k + b)` is `k`-hyperperfect. -/
theorem isHyperperfect_of_factorization {k a b : ℕ} (hk : 1 ≤ k) (hab : a * b = k ^ 2 + 1)
    (ha : (k + a).Prime) (hb : (k + b).Prime) :
    IsHyperperfect k ((k + a) * (k + b)) := by
  have hne : a ≠ b := ne_of_mul_eq_sq_add_one hk hab
  exact (isHyperperfect_prime_mul_prime_iff ha hb (by omega)).mpr hab

/-- The classical family: if `k + 1` and `k ^ 2 + k + 1` are both prime, then
`(k + 1) * (k ^ 2 + k + 1)` is `k`-hyperperfect. -/
theorem isHyperperfect_classical {k : ℕ} (hk : 1 ≤ k) (h1 : (k + 1).Prime)
    (h2 : (k ^ 2 + k + 1).Prime) :
    IsHyperperfect k ((k + 1) * (k ^ 2 + k + 1)) := by
  have e2 : k + (k ^ 2 + 1) = k ^ 2 + k + 1 := by ring
  have h2' : (k + (k ^ 2 + 1)).Prime := by rwa [e2]
  have h := isHyperperfect_of_factorization (a := 1) (b := k ^ 2 + 1) hk (by ring) h1 h2'
  rwa [e2] at h

/-! ### Unconditional witnesses for small `k` -/

/-- `6` is `1`-hyperperfect, i.e. perfect. -/
theorem isHyperperfect_1_6 : IsHyperperfect 1 6 := by
  have h := isHyperperfect_classical (k := 1) le_rfl (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `21 = 3 * 7` is `2`-hyperperfect. -/
theorem isHyperperfect_2_21 : IsHyperperfect 2 21 := by
  have h := isHyperperfect_classical (k := 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `325 = 5 ^ 2 * 13` is `3`-hyperperfect. -/
theorem isHyperperfect_3_325 : IsHyperperfect 3 325 := by
  have hs : sigma 25 = 31 := by
    rw [show (25 : ℕ) = 5 ^ 2 by norm_num, sigma_prime_pow (by norm_num)]
    decide
  have h := isHyperperfect_of_seed (k := 3) (m := 25) (q := 13) (by norm_num) (by norm_num)
    (by decide) (by rw [hs])
  norm_num at h
  exact h

/-- `1950625 = 5 ^ 4 * 3121` is `4`-hyperperfect. -/
theorem isHyperperfect_4_1950625 : IsHyperperfect 4 1950625 := by
  have hs : sigma 625 = 781 := by
    rw [show (625 : ℕ) = 5 ^ 4 by norm_num, sigma_prime_pow (by norm_num)]
    decide
  have h := isHyperperfect_of_seed (k := 4) (m := 625) (q := 3121) (by norm_num) (by norm_num)
    (by decide) (by rw [hs])
  norm_num at h
  exact h

/-- `301 = 7 * 43` is `6`-hyperperfect. -/
theorem isHyperperfect_6_301 : IsHyperperfect 6 301 := by
  have h := isHyperperfect_classical (k := 6) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `159841 = 11 ^ 2 * 1321` is `10`-hyperperfect. -/
theorem isHyperperfect_10_159841 : IsHyperperfect 10 159841 := by
  have hs : sigma 121 = 133 := by
    rw [show (121 : ℕ) = 11 ^ 2 by norm_num, sigma_prime_pow (by norm_num)]
    decide
  have h := isHyperperfect_of_seed (k := 10) (m := 121) (q := 1321) (by norm_num) (by norm_num)
    (by decide) (by rw [hs])
  norm_num at h
  exact h

/-- `10693 = 17 ^ 2 * 37` is `11`-hyperperfect. -/
theorem isHyperperfect_11_10693 : IsHyperperfect 11 10693 := by
  have hs : sigma 289 = 307 := by
    rw [show (289 : ℕ) = 17 ^ 2 by norm_num, sigma_prime_pow (by norm_num)]
    decide
  have h := isHyperperfect_of_seed (k := 11) (m := 289) (q := 37) (by norm_num) (by norm_num)
    (by decide) (by rw [hs])
  norm_num at h
  exact h

/-- `697 = 17 * 41` is `12`-hyperperfect. -/
theorem isHyperperfect_12_697 : IsHyperperfect 12 697 := by
  have h := isHyperperfect_of_seed (k := 12) (m := 17) (q := 41) (by norm_num) (by norm_num)
    (by decide) (by rw [sigma_prime (by norm_num)])
  norm_num at h
  exact h

/-- `1333 = 31 * 43` is `18`-hyperperfect. -/
theorem isHyperperfect_18_1333 : IsHyperperfect 18 1333 := by
  have h := isHyperperfect_of_seed (k := 18) (m := 31) (q := 43) (by norm_num) (by norm_num)
    (by decide) (by rw [sigma_prime (by norm_num)])
  norm_num at h
  exact h

/-- `51301 = 29 ^ 2 * 61` is `19`-hyperperfect. -/
theorem isHyperperfect_19_51301 : IsHyperperfect 19 51301 := by
  have hs : sigma 841 = 871 := by
    rw [show (841 : ℕ) = 29 ^ 2 by norm_num, sigma_prime_pow (by norm_num)]
    decide
  have h := isHyperperfect_of_seed (k := 19) (m := 841) (q := 61) (by norm_num) (by norm_num)
    (by decide) (by rw [hs])
  norm_num at h
  exact h

/-- **Unconditional partial result.**  A `k`-hyperperfect number exists for each `k` in the
explicit list `{1, 2, 3, 4, 6, 10, 11, 12, 18, 19}`. -/
theorem exists_hyperperfect_of_small {k : ℕ}
    (hk : k ∈ ({1, 2, 3, 4, 6, 10, 11, 12, 18, 19} : Finset ℕ)) :
    ∃ n : ℕ, IsHyperperfect k n := by
  fin_cases hk
  · exact ⟨6, isHyperperfect_1_6⟩
  · exact ⟨21, isHyperperfect_2_21⟩
  · exact ⟨325, isHyperperfect_3_325⟩
  · exact ⟨1950625, isHyperperfect_4_1950625⟩
  · exact ⟨301, isHyperperfect_6_301⟩
  · exact ⟨159841, isHyperperfect_10_159841⟩
  · exact ⟨10693, isHyperperfect_11_10693⟩
  · exact ⟨697, isHyperperfect_12_697⟩
  · exact ⟨1333, isHyperperfect_18_1333⟩
  · exact ⟨51301, isHyperperfect_19_51301⟩

/-! ### The conditional reduction -/

/-- The arithmetic hypothesis on which the reduction below is conditional: for every `k ≥ 1`
there are a "seed" `m > 1` and a prime `q` not dividing `m` with
`k * σ m * (q + 1) + 1 = m * q * (1 + k) + k`.

By `isHyperperfect_mul_prime_iff` this says exactly that for every `k ≥ 1` there is a
`k`-hyperperfect number possessing a prime factor of multiplicity one — a mild strengthening of
the conjecture that is satisfied by every hyperperfect number currently known. -/
def SeedHypothesis : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ m q : ℕ, 1 < m ∧ q.Prime ∧ ¬ q ∣ m ∧
    k * sigma m * (q + 1) + 1 = m * q * (1 + k) + k

/-- The seed hypothesis is non-vacuous: its defining condition holds for `k` in the explicit list
of small values treated above. -/
theorem seedHypothesis_holds_of_small {k : ℕ}
    (hk : k ∈ ({1, 2, 3, 4, 6, 10, 11, 12, 18, 19} : Finset ℕ)) :
    ∃ m q : ℕ, 1 < m ∧ q.Prime ∧ ¬ q ∣ m ∧
      k * sigma m * (q + 1) + 1 = m * q * (1 + k) + k := by
  have key : ∀ (m q : ℕ), 1 < m → q.Prime → ¬ q ∣ m → IsHyperperfect k (m * q) →
      ∃ m q : ℕ, 1 < m ∧ q.Prime ∧ ¬ q ∣ m ∧
        k * sigma m * (q + 1) + 1 = m * q * (1 + k) + k := by
    intro m q hm hq hqm h
    exact ⟨m, q, hm, hq, hqm, (isHyperperfect_mul_prime_iff hm hq hqm).mp h⟩
  fin_cases hk
  · exact key 2 3 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_1_6)
  · exact key 3 7 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_2_21)
  · exact key 25 13 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_3_325)
  · exact key 625 3121 (by norm_num) (by norm_num) (by decide)
      (by simpa using isHyperperfect_4_1950625)
  · exact key 7 43 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_6_301)
  · exact key 121 1321 (by norm_num) (by norm_num) (by decide)
      (by simpa using isHyperperfect_10_159841)
  · exact key 289 37 (by norm_num) (by norm_num) (by decide)
      (by simpa using isHyperperfect_11_10693)
  · exact key 17 41 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_12_697)
  · exact key 31 43 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_18_1333)
  · exact key 841 61 (by norm_num) (by norm_num) (by decide)
      (by simpa using isHyperperfect_19_51301)

/-- **Brockian conjecture (hyperperfect numbers, all `k`), conditional form.**

The conjecture asserts that for every `k ≥ 1` there exists a `k`-hyperperfect number; this is an
open problem.  The theorem below is a Lean-checked reduction: it derives the conjecture from the
arithmetic hypothesis `SeedHypothesis`, i.e. from the solvability, for each `k ≥ 1`, of
`k * σ m * (q + 1) + 1 = m * q * (1 + k) + k` in a seed `m > 1` and a prime `q ∤ m`.  The
resulting `k`-hyperperfect number is `m * q`.

Unconditional instances are provided by `exists_hyperperfect_of_small`. -/
theorem HyperperfectAllK (H : SeedHypothesis) :
    ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, IsHyperperfect k n := by
  intro k hk
  obtain ⟨m, q, hm, hq, hqm, h⟩ := H k hk
  exact ⟨m * q, isHyperperfect_of_seed hm hq hqm h⟩

end Brockian.HyperperfectNumbers

