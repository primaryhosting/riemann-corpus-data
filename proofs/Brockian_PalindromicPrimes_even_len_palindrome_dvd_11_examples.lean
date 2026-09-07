/-
  Brockian/PalindromicPrimes.lean — base-10 palindromic primes.

  A *palindromic prime* is a prime whose base-10 digit list reads the same forwards
  and backwards (`Nat.digits 10 n = (Nat.digits 10 n).reverse`). This module records:

    1. concrete palindromic primes (2, 11, 101, 131, 151, 313, 353, 727, 757, 919),
       each an independently-checkable `Nat.Prime ∧ IsPalindrome` bundle;
    2. the STRUCTURAL gem — every base-10 palindrome with an *even* number of digits is
       divisible by 11 (`even_palindrome_dvd_11`), whence 11 is the *only* even-length
       palindromic prime (`eleven_unique_even_palindromic_prime`);
    3. the OPEN problem — it is unknown whether there are infinitely many base-10
       palindromic primes. This is recorded as an unproven `def`
       (`PalindromicPrimeInfinitude`); NOTHING in this file asserts or resolves it.

  Verification (spec §2A triple verification):
    - `#print axioms`  : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent : verified @ lean-4.32.0

  The even-length divisibility argument: 10 ≡ -1 (mod 11), so the alternating digit sum
  ≡ n (mod 11); for an even-length palindrome the alternating sum cancels in pairs
  (position i and position (len-1-i) carry the same digit but opposite signs), giving
  11 ∣ n. Formalized here by induction on `List.Palindrome`, using
  1 + 10^(2k+1) ≡ 0 (mod 11) for the outer digit and the inductive hypothesis for the
  inner (even-length) palindrome.
-/
import Mathlib

namespace Brockian.PalindromicPrimes

set_option maxRecDepth 4000

/-- `n` is a base-10 palindrome: its digit list equals its own reverse. -/
def IsPalindrome (n : ℕ) : Prop := Nat.digits 10 n = (Nat.digits 10 n).reverse

/-- A palindromic prime: a prime whose base-10 digits form a palindrome. -/
def PalindromicPrime (n : ℕ) : Prop := n.Prime ∧ IsPalindrome n

/-- **OPEN.** Infinitely many base-10 palindromic primes exist. It is a genuine open
problem whether this holds; this `def` merely *names* the statement — it is UNPROVEN and
is never asserted or used as a hypothesis anywhere below. -/
def PalindromicPrimeInfinitude : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ PalindromicPrime n

/-! ### (1) Concrete palindromic primes -/

theorem palindromic_2   : PalindromicPrime 2 :=
  ⟨by norm_num, by unfold IsPalindrome; decide⟩

theorem palindromic_11  : PalindromicPrime 11 :=
  ⟨by norm_num, by unfold IsPalindrome; decide⟩

theorem palindromic_101 : PalindromicPrime 101 :=
  ⟨by norm_num, by unfold IsPalindrome; decide⟩

theorem palindromic_131 : PalindromicPrime 131 :=
  ⟨by norm_num, by unfold IsPalindrome; decide⟩

theorem palindromic_151 : PalindromicPrime 151 :=
  ⟨by norm_num, by unfold IsPalindrome; decide⟩

theorem palindromic_313 : PalindromicPrime 313 :=
  ⟨by norm_num, by unfold IsPalindrome; decide⟩

theorem palindromic_353 : PalindromicPrime 353 :=
  ⟨by norm_num, by unfold IsPalindrome; decide⟩

theorem palindromic_727 : PalindromicPrime 727 :=
  ⟨by norm_num, by unfold IsPalindrome; decide⟩

theorem palindromic_757 : PalindromicPrime 757 :=
  ⟨by norm_num, by unfold IsPalindrome; decide⟩

theorem palindromic_919 : PalindromicPrime 919 :=
  ⟨by norm_num, by unfold IsPalindrome; decide⟩

/-! ### (2) Structural: even-length palindromes are divisible by 11 -/

/-- Concrete illustrations of the even-length rule: 1001 = 11·91, 1221 = 11·111,
123321 = 11·11211, 246642 = 11·22422. -/
theorem even_len_palindrome_dvd_11_examples :
    (11 ∣ 1001) ∧ (11 ∣ 1221) ∧ (11 ∣ 123321) ∧ (11 ∣ 246642) := by decide

/-- Every 2-digit palindrome `dd` (digit list `[d, d]`) is divisible by 11, for an
*arbitrary* digit `d`: `Nat.ofDigits 10 [d, d] = d + 10·d = 11·d`. -/
theorem two_digit_palindrome_dvd_11 (d : ℕ) : 11 ∣ Nat.ofDigits 10 [d, d] := by
  refine ⟨d, ?_⟩
  simp [Nat.ofDigits]
  ring

/-- Auxiliary modular fact: `1 + 10^(2k+1) ≡ 0 (mod 11)`. Since `10^2 = 100 ≡ 1`, an odd
power `10^(2k+1) ≡ 10`, so `1 + 10^(2k+1) ≡ 11 ≡ 0`. This supplies the "outer digit"
cancellation in the even-length palindrome induction. -/
theorem eleven_dvd_one_add_odd_pow (k : ℕ) : 11 ∣ 1 + 10 ^ (2 * k + 1) := by
  have key : (10 : ℕ) ^ (2 * k + 1) ≡ 10 [MOD 11] := by
    calc (10 : ℕ) ^ (2 * k + 1) = (10 ^ 2) ^ k * 10 := by rw [← pow_mul, ← pow_succ]
      _ ≡ 1 ^ k * 10 [MOD 11] := Nat.ModEq.mul_right 10 (Nat.ModEq.pow k (by decide))
      _ = 10 := by ring
  have h0 : 1 + 10 ^ (2 * k + 1) ≡ 0 [MOD 11] :=
    (Nat.ModEq.add_left 1 key).trans (by decide)
  exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using h0)

/-- **STRUCTURAL GEM (general form).** Any base-10 palindrome digit list of *even* length
represents a number divisible by 11. Stated for an arbitrary list `L` that equals its own
reverse and has even length; `Nat.ofDigits 10 L` is then a multiple of 11. Proved by
induction on the `List.Palindrome` structure: the empty list gives `0`; the inductive step
peels a matching outer digit `x` off a shorter even-length palindrome `l`, and
`Nat.ofDigits 10 (x :: (l ++ [x])) = 10 · Nat.ofDigits 10 l + x · (1 + 10^(2k+1))`, both
summands divisible by 11 (inductive hypothesis; `eleven_dvd_one_add_odd_pow`). -/
theorem even_palindrome_dvd_11 (L : List ℕ) (hpal : L.reverse = L)
    (heven : Even L.length) : 11 ∣ Nat.ofDigits 10 L := by
  have hp : List.Palindrome L := List.Palindrome.of_reverse_eq hpal
  clear hpal
  revert heven
  induction hp with
  | nil => intro _; simp
  | singleton x => intro h; simp at h
  | cons_concat x hl ih =>
      rename_i l
      intro heven
      have hlen : (x :: (l ++ [x])).length = l.length + 2 := by simp
      have hle : Even l.length := by
        rw [Nat.even_iff] at heven ⊢
        rw [hlen] at heven; omega
      obtain ⟨k, hk⟩ := hle
      have hk2 : l.length = 2 * k := by omega
      have hdl : 11 ∣ Nat.ofDigits 10 l := ih ⟨k, hk⟩
      have hexp : Nat.ofDigits 10 (x :: (l ++ [x]))
          = 10 * Nat.ofDigits 10 l + x * (1 + 10 ^ (2 * k + 1)) := by
        rw [Nat.ofDigits_cons, Nat.ofDigits_append]
        simp [Nat.ofDigits_singleton, hk2]
        ring
      rw [hexp]
      exact Nat.dvd_add (Dvd.dvd.mul_left hdl 10)
        (Dvd.dvd.mul_left (eleven_dvd_one_add_odd_pow k) x)

/-- The even-length rule at the level of a natural number: if `n` is a base-10 palindrome
and its digit list has even length, then `11 ∣ n`. -/
theorem even_digit_palindrome_dvd_11 (n : ℕ) (hpal : IsPalindrome n)
    (heven : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  have h := even_palindrome_dvd_11 (Nat.digits 10 n) hpal.symm heven
  rwa [Nat.ofDigits_digits] at h

/-- **CAPSTONE.** `11` is the *only* even-length base-10 palindromic prime: any
palindromic prime whose digit list has even length must equal 11. (A prime divisible by
11 is 11 itself.) Combined with the concrete odd-length examples above, this pins down the
entire even-length case while leaving the odd-length infinitude open. -/
theorem eleven_unique_even_palindromic_prime (n : ℕ) (hpp : PalindromicPrime n)
    (heven : Even (Nat.digits 10 n).length) : n = 11 := by
  obtain ⟨hprime, hpal⟩ := hpp
  have hdvd : 11 ∣ n := even_digit_palindrome_dvd_11 n hpal heven
  rcases (hprime.eq_one_or_self_of_dvd 11 hdvd) with h | h
  · exact absurd h (by norm_num)
  · exact h.symm

/-! ### (3) Contrast: a non-palindrome -/

/-- `13` is not a palindrome: its digit list is `[3, 1] ≠ [1, 3]`. -/
theorem not_palindromic_13 : ¬ IsPalindrome 13 := by unfold IsPalindrome; decide

end Brockian.PalindromicPrimes
