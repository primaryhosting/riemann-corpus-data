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

/-!
## Status and contents

The unconditional statement "there are infinitely many base-10 palindromic primes" is an open
problem, so this file provides a Lean-checked conditional reduction together with unconditional
partial results.

* `IsPalindrome`, `palindromicPrimes` : the basic definitions.
* `PalindromicPrimeInfinitude` : **the target**, a conditional reduction — if palindromic primes
  are unbounded then there are infinitely many of them (and `infinite_iff_unbounded` shows the
  two formulations are equivalent).
* `eleven_dvd_of_palindrome_even_length`, `eq_eleven_of_prime_palindrome_even_length` :
  unconditional results — a palindrome with an even number of digits is divisible by `11`
  (via the Mathlib lemma `Nat.eleven_dvd_iff`), hence `11` is the only palindromic prime with
  an even number of digits.
* `infinite_iff_oddDigit_infinite` : consequently the conjecture is equivalent to its
  odd-digit-count version.
-/

namespace Brockian.PalindromicPrimes

/-- `n` is a base-10 palindrome: its list of decimal digits is its own reversal. -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

instance : DecidablePred IsPalindrome :=
  fun n => inferInstanceAs (Decidable ((Nat.digits 10 n).reverse = Nat.digits 10 n))

/-- The set of palindromic primes. -/
def palindromicPrimes : Set ℕ := {p | Nat.Prime p ∧ IsPalindrome p}

/-! ### Auxiliary lemmas on alternating sums -/

theorem alternatingSum_append (l m : List ℤ) :
    (l ++ m).alternatingSum = l.alternatingSum + (-1) ^ l.length * m.alternatingSum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.cons_append, List.alternatingSum_cons, ih, List.length_cons, pow_succ]
      ring

/-- The alternating sum of a palindromic list of even length vanishes. -/
theorem alternatingSum_eq_zero_of_palindrome_even {l : List ℤ} (hp : l.Palindrome)
    (he : Even l.length) : l.alternatingSum = 0 := by
  induction hp with
  | nil => simp
  | singleton x => simp at he
  | @cons_concat x l hl ih =>
      have hlen : (x :: (l ++ [x])).length = l.length + 2 := by simp
      have hel : Even l.length := by
        rw [hlen] at he
        rcases he with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      have := ih hel
      simp [List.alternatingSum_cons, alternatingSum_append, this, hel.neg_one_pow]

/-! ### Even-length palindromes are divisible by 11 -/

/-- A base-10 palindrome with an even number of digits is divisible by `11`. -/
theorem eleven_dvd_of_palindrome_even_length {n : ℕ} (hpal : IsPalindrome n)
    (he : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  rw [Nat.eleven_dvd_iff]
  have hpal' : ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).Palindrome := by
    rw [List.Palindrome.iff_reverse_eq, ← List.map_reverse, hpal]
  have he' : Even ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).length := by
    simpa using he
  rw [alternatingSum_eq_zero_of_palindrome_even hpal' he']
  exact dvd_zero _

/-- The only palindromic prime with an even number of decimal digits is `11`. -/
theorem eq_eleven_of_prime_palindrome_even_length {p : ℕ} (hp : Nat.Prime p)
    (hpal : IsPalindrome p) (he : Even (Nat.digits 10 p).length) : p = 11 := by
  have h11 : (11 : ℕ) ∣ p := eleven_dvd_of_palindrome_even_length hpal he
  exact ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h11).symm

/-! ### Examples -/

theorem two_mem_palindromicPrimes : 2 ∈ palindromicPrimes :=
  ⟨by norm_num, by decide⟩

theorem eleven_mem_palindromicPrimes : 11 ∈ palindromicPrimes :=
  ⟨by norm_num, by decide⟩

theorem hundredone_mem_palindromicPrimes : 101 ∈ palindromicPrimes :=
  ⟨by norm_num, by decide⟩

/-! ### Reduction to the odd-digit case -/

/-- Palindromic primes whose decimal expansion has an odd number of digits. -/
def oddDigitPalindromicPrimes : Set ℕ :=
  {p | Nat.Prime p ∧ IsPalindrome p ∧ Odd (Nat.digits 10 p).length}

theorem oddDigitPalindromicPrimes_subset :
    oddDigitPalindromicPrimes ⊆ palindromicPrimes := fun _ hp => ⟨hp.1, hp.2.1⟩

theorem palindromicPrimes_diff_subset :
    palindromicPrimes \ {11} ⊆ oddDigitPalindromicPrimes := by
  rintro p ⟨⟨hp, hpal⟩, hne⟩
  refine ⟨hp, hpal, ?_⟩
  rcases Nat.even_or_odd (Nat.digits 10 p).length with he | ho
  · exact absurd (eq_eleven_of_prime_palindrome_even_length hp hpal he) hne
  · exact ho

/-- Every palindromic prime other than `11` has an odd number of decimal digits, so the
conjecture is equivalent to its odd-digit version. -/
theorem infinite_iff_oddDigit_infinite :
    palindromicPrimes.Infinite ↔ oddDigitPalindromicPrimes.Infinite := by
  constructor
  · intro h
    exact (h.diff (Set.finite_singleton 11)).mono palindromicPrimes_diff_subset
  · intro h
    exact h.mono oddDigitPalindromicPrimes_subset

/-- Any base-10 palindrome with an even number of digits and more than two digits is composite
(it is a proper multiple of `11`). -/
theorem not_prime_of_palindrome_even_length_of_lt {n : ℕ} (hpal : IsPalindrome n)
    (he : Even (Nat.digits 10 n).length) (hn : 11 < n) : ¬ Nat.Prime n := by
  intro hp
  exact absurd (eq_eleven_of_prime_palindrome_even_length hp hpal he) (by omega)

/-! ### The conditional reduction -/

/-- **Conditional reduction.** If palindromic primes are unbounded, there are infinitely many
of them. -/
theorem PalindromicPrimeInfinitude
    (h : ∀ N : ℕ, ∃ p, N < p ∧ Nat.Prime p ∧ IsPalindrome p) :
    palindromicPrimes.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  obtain ⟨p, hN, hp, hpal⟩ := h N
  exact ⟨p, ⟨hp, hpal⟩, hN⟩

/-- The infinitude of palindromic primes is *equivalent* to their unboundedness. -/
theorem infinite_iff_unbounded :
    palindromicPrimes.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ Nat.Prime p ∧ IsPalindrome p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hN⟩ := h.exists_gt N
    exact ⟨p, hN, hp.1, hp.2⟩
  · exact PalindromicPrimeInfinitude

end Brockian.PalindromicPrimes

