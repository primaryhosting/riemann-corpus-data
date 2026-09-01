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

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace SierpinskiCovering

/-- A *Sierpiński number* is an odd natural number `k` such that `k * 2 ^ n + 1` is composite
(never prime) for every `n ≥ 1`. -/
def IsSierpinskiNumber (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (k * 2 ^ n + 1)

/-- The covering set of primes used for `78557`: each of these primes divides `2 ^ 36 - 1`,
so `2 ^ n` is periodic modulo them with period dividing `36`. -/
def coveringPrimes : List ℕ := [3, 5, 7, 13, 19, 37, 73]

/-- Periodicity step: if `p` divides `2 ^ 36 - 1` and `p` divides `78557 * 2 ^ r + 1`,
then `p` divides `78557 * 2 ^ (36 * q + r) + 1`. -/
theorem dvd_of_covering (p r q : ℕ) (hp : p ∣ 2 ^ 36 - 1)
    (hd : p ∣ 78557 * 2 ^ r + 1) :
    p ∣ 78557 * 2 ^ (36 * q + r) + 1 := by
  have h1 : (2 : ℕ) ^ 36 ≡ 1 [MOD p] :=
    (((Nat.modEq_iff_dvd' (by norm_num)).2 hp)).symm
  have h2 : ((2 : ℕ) ^ 36) ^ q ≡ 1 [MOD p] := by
    simpa using h1.pow q
  have h3 : 78557 * 2 ^ (36 * q + r) + 1 ≡ 78557 * 2 ^ r + 1 [MOD p] := by
    have hpow : (2 : ℕ) ^ (36 * q + r) = ((2 : ℕ) ^ 36) ^ q * 2 ^ r := by
      rw [pow_add, pow_mul]
    rw [hpow]
    have := ((h2.mul_right (2 ^ r)).mul_left 78557).add_right 1
    simpa using this
  exact (Nat.modEq_zero_iff_dvd).1 (h3.trans ((Nat.modEq_zero_iff_dvd).2 hd))

/-- The covering table: for every residue `r < 36` there is a prime in `coveringPrimes`
dividing both `2 ^ 36 - 1` and `78557 * 2 ^ r + 1`. -/
theorem covering_table :
    ∀ r < 36, ∃ p ∈ coveringPrimes, p ∣ 2 ^ 36 - 1 ∧ p ∣ 78557 * 2 ^ r + 1 := by
  decide

/-- Every number of the form `78557 * 2 ^ n + 1` has a nontrivial divisor from the
covering set, hence is not prime. -/
theorem not_prime_78557 (n : ℕ) : ¬ Nat.Prime (78557 * 2 ^ n + 1) := by
  obtain ⟨p, hmem, hp36, hpr⟩ := covering_table (n % 36) (Nat.mod_lt _ (by norm_num))
  have hdvd : p ∣ 78557 * 2 ^ n + 1 := by
    have h := dvd_of_covering p (n % 36) (n / 36) hp36 hpr
    rwa [Nat.div_add_mod' n 36, Nat.mul_comm (n / 36) 36] at h
    -- (the rewrite turns `36 * (n / 36) + n % 36` into `n`)
  have hple : p ≤ 73 := by
    fin_cases hmem <;> norm_num
  have hp1 : p ≠ 1 := by
    fin_cases hmem <;> norm_num
  intro hN
  rcases hN.eq_one_or_self_of_dvd p hdvd with h | h
  · exact hp1 h
  · have h2 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    have : 78557 * 2 ^ n + 1 ≥ 78558 := by nlinarith
    omega

/-- **The Sierpiński problem (Selfridge's covering).**  `78557` is a Sierpiński number:
it is odd, and `78557 * 2 ^ n + 1` is composite for every `n ≥ 1`.  The proof uses the
covering set of primes `{3, 5, 7, 13, 19, 37, 73}`, each dividing `2 ^ 36 - 1`. -/
theorem SierpinskiProblem : IsSierpinskiNumber 78557 := by
  refine ⟨⟨39278, by norm_num⟩, fun n _ => not_prime_78557 n⟩

end SierpinskiCovering
end Brockian

