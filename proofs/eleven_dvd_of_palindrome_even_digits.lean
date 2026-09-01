import Mathlib

/-- `n` is a base-10 palindrome: its digit list equals its reverse. -/
def IsPalindrome10 (n : ℕ) : Prop :=
  Nat.digits 10 n = (Nat.digits 10 n).reverse

/-- The palindromic-primes conjecture (**OPEN**), recorded as an unproven
`def`: infinitely many primes are base-10 palindromes. -/
def PalindromicPrimesInfinite : Prop :=
  {p : ℕ | p.Prime ∧ IsPalindrome10 p}.Infinite

/-- Every base-10 palindrome with an even number of digits is divisible by 11. -/
theorem eleven_dvd_of_palindrome_even_digits {n : ℕ}
    (h : IsPalindrome10 n) (he : Even (Nat.digits 10 n).length) :
    11 ∣ n :=
  Nat.eleven_dvd_of_palindrome (List.Palindrome.of_reverse_eq h.symm) he

