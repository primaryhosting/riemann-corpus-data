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
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PalindromicPrimes

open Nat

/-- A natural number is a *(decimal) palindrome* when its list of base-10 digits
reads the same forwards and backwards. -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).Palindrome

/-- The set of palindromic primes. -/
def palindromicPrimes : Set ℕ := {n | n.Prime ∧ IsPalindrome n}

/-- The set of palindromic primes having an odd number of decimal digits. -/
def oddLengthPalindromicPrimes : Set ℕ :=
  {n | n.Prime ∧ IsPalindrome n ∧ Odd (Nat.digits 10 n).length}

lemma oddLength_subset : oddLengthPalindromicPrimes ⊆ palindromicPrimes := by
  rintro n ⟨hp, hpal, -⟩
  exact ⟨hp, hpal⟩

/-- **Key intermediate lemma.** A palindromic prime with an even number of decimal
digits must be `11`: any even-length decimal palindrome is divisible by `11`. -/
theorem eq_eleven_of_even_length {n : ℕ} (hp : n.Prime) (hpal : IsPalindrome n)
    (hlen : Even (Nat.digits 10 n).length) : n = 11 :=
  ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp
    (Nat.eleven_dvd_of_palindrome hpal hlen)).symm

/-- `11` is itself a palindromic prime (with an even number of digits). -/
theorem eleven_mem_palindromicPrimes : 11 ∈ palindromicPrimes := by
  refine ⟨by norm_num, ?_⟩
  show (Nat.digits 10 11).Palindrome
  rw [show Nat.digits 10 11 = [1, 1] by norm_num]
  decide

/-- Every palindromic prime other than `11` has an odd number of digits. -/
theorem palindromicPrimes_subset :
    palindromicPrimes ⊆ oddLengthPalindromicPrimes ∪ {11} := by
  rintro n ⟨hp, hpal⟩
  rcases Nat.even_or_odd (Nat.digits 10 n).length with h | h
  · exact Or.inr (eq_eleven_of_even_length hp hpal h)
  · exact Or.inl ⟨hp, hpal, h⟩

/-- **Reduction of the palindromic prime infinitude conjecture.**

There are infinitely many palindromic primes if and only if there are infinitely many
palindromic primes with an *odd* number of decimal digits.

The nontrivial direction rests on the key lemma `eq_eleven_of_even_length`: `11` is the
only palindromic prime with an even number of decimal digits, since every even-length
decimal palindrome is divisible by `11`.  Thus the even-length case contributes exactly
one prime, and the whole conjecture is equivalent to its odd-length part. -/
theorem PalindromicPrimeInfinitude :
    palindromicPrimes.Infinite ↔ oddLengthPalindromicPrimes.Infinite := by
  constructor
  · intro h
    by_contra hfin
    rw [Set.not_infinite] at hfin
    exact h ((hfin.union (Set.finite_singleton 11)).subset palindromicPrimes_subset)
  · exact fun h => h.mono oddLength_subset

end Brockian.PalindromicPrimes

