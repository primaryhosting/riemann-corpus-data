import Mathlib
import PerfectNumbersEuler

namespace Brockian.EvenPerfectMod9

open Nat

/-- The modular-arithmetic consequence of the Euclid–Euler form of an even perfect number. -/
lemma euclidEuler_form_mod9 {k : ℕ} (hprime : Nat.Prime (mersenne (k + 1)))
    (hlarge : 6 < 2 ^ k * mersenne (k + 1)) :
    (2 ^ k * mersenne (k + 1)) % 9 = 1 := by
  have hmersenne_def : mersenne (k + 1) = 2 ^ (k + 1) - 1 := rfl
  -- Establish bounds on k
  have hk_pos : k ≠ 0 := by
    rintro rfl
    simp [mersenne] at hprime
    exact Nat.not_prime_one hprime
  have hk_ge_2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    interval_cases k <;> simp [mersenne] at hlarge hprime
  -- k+1 is odd (since k+1 ≥ 3 and prime implies k+1 is odd), so k is even
  have hk_even : Even k := by
    have hk1_ge_3 : 3 ≤ k + 1 := by omega
    -- If k is odd, then k+1 is even and ≥ 4, so 2^(k+1) - 1 is divisible by 3
    by_contra hk_odd
    have hk_mod : k % 2 = 1 := by
      have := Nat.even_or_odd k
      cases this with
      | inl heven => exact absurd heven hk_odd
      | inr hodd => exact Nat.odd_iff.mp hodd
    -- k+1 is even
    have hk1_even : Even (k + 1) := by
      rw [even_iff_two_dvd]
      omega
    -- mersenne(k+1) is divisible by 3 when k+1 is even
    have h3_div : 3 ∣ mersenne (k + 1) := by
      simp [mersenne]
      have hk1_eq : k + 1 = 2 * ((k + 1) / 2) := by omega
      rw [hk1_eq, pow_mul]
      have : 3 ∣ 2^2 - 1 := by norm_num
      have hfactor : (2^2 - 1) ∣ (2^2)^((k+1)/2) - 1 := by
        have := nat_sub_dvd_pow_sub_pow (2^2) 1 ((k+1)/2)
        simpa using this
      exact dvd_trans ‹3 ∣ 2^2 - 1› hfactor
    -- Since mersenne(k+1) is prime and divisible by 3, it must equal 3
    have hmersenne_eq_3 : mersenne (k + 1) = 3 := by
      have := hprime.dvd_iff_eq (by norm_num : 3 ≠ 1)
      exact this.mp h3_div
    -- But mersenne(k+1) = 3 implies k+1 = 2, contradicting k+1 ≥ 3
    rw [mersenne] at hmersenne_eq_3
    have h2k1 : 2^(k+1) = 2^2 := by norm_num at hmersenne_eq_3 ⊢; omega
    have : k + 1 = 2 := Nat.pow_right_injective (by norm_num : 1 < 2) h2k1
    omega
  -- Now use modular arithmetic: k is even, so k % 6 ∈ {0, 2, 4}
  -- For each case, 2^k * mersenne(k+1) ≡ 1 (mod 9)
  have hk_mod6 : k % 6 = 0 ∨ k % 6 = 2 ∨ k % 6 = 4 := by
    have := hk_even
    rw [even_iff_two_dvd] at this
    omega
  -- Reduce to finite computation using Nat.pow_mod
  rw [mersenne]
  have h2k_mod : 2 ^ k % 9 = 2 ^ (k % 6) % 9 := by
    conv_lhs => rw [← Nat.mod_add_div k 6, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have h2k1_mod : 2 ^ (k + 1) % 9 = 2 ^ ((k + 1) % 6) % 9 := by
    conv_lhs => rw [← Nat.mod_add_div (k + 1) 6, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  -- Do case analysis on k % 6
  rcases hk_mod6 with hk0 | hk2 | hk4
  · -- k % 6 = 0
    simp [hk0] at h2k_mod
    have hk1_mod : (k + 1) % 6 = 1 := by omega
    simp [hk1_mod] at h2k1_mod
    -- 2^(k+1) % 9 = 2, so (2^(k+1) - 1) % 9 = 1
    have hmersenne_mod : (2 ^ (k + 1) - 1) % 9 = 1 := by
      have : 2 ^ (k + 1) % 9 = 2 := h2k1_mod
      have hpos : 0 < 2 ^ (k + 1) := by positivity
      omega
    calc (2 ^ k * (2 ^ (k + 1) - 1)) % 9
        = ((2 ^ k % 9) * ((2 ^ (k + 1) - 1) % 9)) % 9 := by rw [Nat.mul_mod]
      _ = (1 * 1) % 9 := by rw [h2k_mod, hmersenne_mod]
      _ = 1 := by norm_num
  · -- k % 6 = 2
    simp [hk2] at h2k_mod
    have hk1_mod : (k + 1) % 6 = 3 := by omega
    simp [hk1_mod] at h2k1_mod
    -- 2^(k+1) % 9 = 8, so (2^(k+1) - 1) % 9 = 7
    have hmersenne_mod : (2 ^ (k + 1) - 1) % 9 = 7 := by
      have : 2 ^ (k + 1) % 9 = 8 := h2k1_mod
      have hpos : 0 < 2 ^ (k + 1) := by positivity
      omega
    calc (2 ^ k * (2 ^ (k + 1) - 1)) % 9
        = ((2 ^ k % 9) * ((2 ^ (k + 1) - 1) % 9)) % 9 := by rw [Nat.mul_mod]
      _ = (4 * 7) % 9 := by rw [h2k_mod, hmersenne_mod]
      _ = 1 := by norm_num
  · -- k % 6 = 4
    simp [hk4] at h2k_mod
    have hk1_mod : (k + 1) % 6 = 5 := by omega
    simp [hk1_mod] at h2k1_mod
    -- 2^(k+1) % 9 = 5, so (2^(k+1) - 1) % 9 = 4
    have hmersenne_mod : (2 ^ (k + 1) - 1) % 9 = 4 := by
      have : 2 ^ (k + 1) % 9 = 5 := h2k1_mod
      have hpos : 0 < 2 ^ (k + 1) := by positivity
      omega
    calc (2 ^ k * (2 ^ (k + 1) - 1)) % 9
        = ((2 ^ k % 9) * ((2 ^ (k + 1) - 1) % 9)) % 9 := by rw [Nat.mul_mod]
      _ = (7 * 4) % 9 := by rw [h2k_mod, hmersenne_mod]
      _ = 1 := by norm_num

/-- Every even perfect number greater than 6 is congruent to 1 modulo 9. -/
theorem even_perfect_mod9 {n : ℕ} (he : Even n) (hp : Nat.Perfect n) (h6 : 6 < n) : n % 9 = 1 := by
  obtain ⟨k, hprime, rfl⟩ :=
    PerfectNumbersEuler.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect he hp
  exact euclidEuler_form_mod9 hprime h6

end Brockian.EvenPerfectMod9

/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic.NormNum.Prime

/-!
# Perfect Numbers

This file proves Theorem 70 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The theorem characterizes even perfect numbers.

Euclid proved that if `2 ^ (k + 1) - 1` is prime (these primes are known as Mersenne primes),
  then `2 ^ k * (2 ^ (k + 1) - 1)` is perfect.

Euler proved the converse, that if `n` is even and perfect, then there exists `k` such that
  `n = 2 ^ k * (2 ^ (k + 1) - 1)` and `2 ^ (k + 1) - 1` is prime.

## References
https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem
-/


namespace PerfectNumbersEuler

namespace Nat

open ArithmeticFunction Finset

-- access notation `σ`
open scoped sigma

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- Euclid's theorem that Mersenne primes induce perfect numbers -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by simp [ne_zero_of_prime_mersenne k pr, parity_simps]

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- **Perfect Number Theorem**: Euler's theorem that even perfect numbers can be factored as a
  power of two times a Mersenne prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose! hm
    simp [hm]

/-- The Euclid-Euler theorem characterizing even perfect numbers -/
theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  constructor
  · rintro ⟨ev, perf⟩
    exact Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  · rintro ⟨k, pr, rfl⟩
    exact ⟨even_two_pow_mul_mersenne_of_prime k pr, perfect_two_pow_mul_mersenne_of_prime k pr⟩

end Nat

end PerfectNumbersEuler

