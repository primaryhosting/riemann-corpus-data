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
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Whether there are infinitely many even perfect numbers is a well-known open problem: it is
equivalent to the existence of infinitely many Mersenne primes.  Accordingly we prove here a
Lean-checked *reduction*: the set of even perfect numbers is infinite **iff** the set of exponents
`k` with `mersenne (k+1) = 2 ^ (k+1) - 1` prime is infinite, and in particular the conditional
statement `EvenPerfectInfinitude`.

The mathematical input is the Euclid–Euler theorem, already available in Mathlib's archive as
`Theorems100.Nat.even_and_perfect_iff`
(`Archive/Wiedijk100Theorems/PerfectNumbers.lean`, theorem 70 of the 100 theorems list).
-/

namespace Brockian.MersennePerfect

open Nat

/-- The set of even perfect natural numbers. -/
def evenPerfectSet : Set ℕ := {n : ℕ | Even n ∧ Nat.Perfect n}

/-- The set of exponents `k` such that `mersenne (k + 1) = 2 ^ (k + 1) - 1` is prime. -/
def mersenneExponentSet : Set ℕ := {k : ℕ | Nat.Prime (mersenne (k + 1))}

/-- The Euclid map sending an exponent `k` to the number `2 ^ k * (2 ^ (k + 1) - 1)`. -/
def euclidNum (k : ℕ) : ℕ := 2 ^ k * mersenne (k + 1)

lemma mersenne_strictMono : StrictMono mersenne := by
  intro a b hab
  have h : (2 : ℕ) ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h1 : 1 ≤ (2 : ℕ) ^ a := Nat.one_le_two_pow
  simp only [mersenne]
  omega

lemma euclidNum_strictMono : StrictMono euclidNum := by
  intro a b hab
  have h1 : (2 : ℕ) ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab.le
  have h2 : mersenne (a + 1) < mersenne (b + 1) := mersenne_strictMono (by omega)
  have h3 : 0 < mersenne (a + 1) := by
    have : 1 < (2 : ℕ) ^ (a + 1) := Nat.one_lt_two_pow (by omega)
    simp only [mersenne]; omega
  exact Nat.mul_lt_mul_of_le_of_lt h1 h2 (by positivity)

lemma euclidNum_injective : Function.Injective euclidNum :=
  euclidNum_strictMono.injective

/-- Euclid's direction: the image of a Mersenne exponent is an even perfect number. -/
lemma euclidNum_mem_evenPerfectSet {k : ℕ} (hk : k ∈ mersenneExponentSet) :
    euclidNum k ∈ evenPerfectSet :=
  Theorems100.Nat.even_and_perfect_iff.2 ⟨k, hk, rfl⟩

/-- Euler's direction: every even perfect number is `euclidNum k` for some Mersenne exponent `k`. -/
lemma exists_mersenneExponent_of_mem_evenPerfectSet {n : ℕ} (hn : n ∈ evenPerfectSet) :
    ∃ k ∈ mersenneExponentSet, euclidNum k = n := by
  obtain ⟨k, hk, rfl⟩ := Theorems100.Nat.even_and_perfect_iff.1 hn
  exact ⟨k, hk, rfl⟩

/-- Sanity check: the set of even perfect numbers is nonempty (`6` and `28` belong to it). -/
lemma six_mem_evenPerfectSet : 6 ∈ evenPerfectSet := by
  refine ⟨by decide, ?_⟩
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (by norm_num)]
  decide

lemma twentyEight_mem_evenPerfectSet : 28 ∈ evenPerfectSet := by
  refine ⟨by decide, ?_⟩
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (by norm_num)]
  decide

/-- **Even Perfect Infinitude (conditional).**  If there are infinitely many Mersenne primes
`2 ^ (k + 1) - 1`, then there are infinitely many even perfect numbers. -/
theorem EvenPerfectInfinitude (h : mersenneExponentSet.Infinite) : evenPerfectSet.Infinite := by
  have himg : (euclidNum '' mersenneExponentSet).Infinite :=
    h.image (euclidNum_injective.injOn)
  refine himg.mono ?_
  rintro _ ⟨k, hk, rfl⟩
  exact euclidNum_mem_evenPerfectSet hk

/-- The converse reduction: infinitely many even perfect numbers force infinitely many
Mersenne primes. -/
theorem mersenneExponent_infinite_of_evenPerfect_infinite
    (h : evenPerfectSet.Infinite) : mersenneExponentSet.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  refine h ((hfin.image euclidNum).subset ?_)
  intro n hn
  obtain ⟨k, hk, rfl⟩ := exists_mersenneExponent_of_mem_evenPerfectSet hn
  exact ⟨k, hk, rfl⟩

/-- **Reduction theorem.**  There are infinitely many even perfect numbers if and only if there
are infinitely many Mersenne primes. -/
theorem evenPerfect_infinite_iff_mersenneExponent_infinite :
    evenPerfectSet.Infinite ↔ mersenneExponentSet.Infinite :=
  ⟨mersenneExponent_infinite_of_evenPerfect_infinite, EvenPerfectInfinitude⟩

end Brockian.MersennePerfect

