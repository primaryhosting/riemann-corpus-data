/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- Every natural number congruent to `3` modulo `4` has a prime divisor
that is itself congruent to `3` modulo `4`. -/
theorem exists_prime_dvd_mod_four_eq_three :
    ∀ n : ℕ, n % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
    by_cases hp4 : p % 4 = 3
    · exact ⟨p, hp, hpd, hp4⟩
    · -- `p` is odd, hence `p % 4 = 1`; peel it off and recurse.
      obtain ⟨m, rfl⟩ := hpd
      have hp2 : p ≠ 2 := by rintro rfl; omega
      have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      have hp41 : p % 4 = 1 := by omega
      have hmod : (p * m) % 4 = m % 4 := by
        conv_lhs => rw [Nat.mul_mod, hp41]
        simp [Nat.mod_mod_of_dvd]
      have hm : m % 4 = 3 := by omega
      have hmlt : m < p * m := by
        have hm0 : 0 < m := by omega
        have := hp.two_le
        calc m = 1 * m := (one_mul m).symm
          _ < p * m := by exact Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl hm0
      obtain ⟨q, hq, hqd, hq4⟩ := ih m hmlt hm
      exact ⟨q, hq, hqd.mul_left p, hq4⟩

/-- **Infinitude of primes congruent to 3 mod 4.**
For every `N` there is a prime `p` with `N < p` and `p % 4 = 3`. -/
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 4 = 3 := by
  -- Consider `M = 4 · N! - 1 ≡ 3 [MOD 4]`.
  have hfac : 0 < Nat.factorial N := Nat.factorial_pos N
  set M : ℕ := 4 * Nat.factorial N - 1 with hM
  have hM4 : M % 4 = 3 := by omega
  obtain ⟨p, hp, hpd, hp4⟩ := exists_prime_dvd_mod_four_eq_three M hM4
  refine ⟨p, hp, ?_, hp4⟩
  by_contra hle
  push_neg at hle
  -- Then `p ∣ N!`, and `p ∣ M`, so `p ∣ 1`, contradiction.
  have hdvdfac : p ∣ Nat.factorial N := Nat.dvd_factorial hp.pos hle
  have h1 : p ∣ 4 * Nat.factorial N := hdvdfac.mul_left 4
  have h2 : (4 * Nat.factorial N) - M = 1 := by omega
  have : p ∣ 1 := h2 ▸ Nat.dvd_sub h1 hpd
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp this)

end NumberTheory

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

