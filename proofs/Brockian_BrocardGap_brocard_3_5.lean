/-
  Brocard's conjecture (the PRIME-GAP one — NOT Brocard's problem n! + 1 = m²,
  which lives in `Brockian/BrocardProblem.lean`).

  Brocard's conjecture (OPEN): for consecutive primes p < q with p ≥ 3, there are
  at least 4 primes strictly between p² and q².

  This file:
    (1) verifies concrete instances (flagship) by exhibiting, for consecutive
        prime pairs (3,5), (5,7), (7,11), (11,13), (13,17), four increasing
        primes strictly between the two prime squares;
  and records Brocard's (gap) conjecture as an UNPROVEN `def`.

  HONEST: `BrocardGapConjecture` is an open problem. Nothing here asserts,
  discharges, or claims to resolve it. It is a `def` of type `Prop`, never a
  theorem, and is never proved.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.BrocardGap

/-- `p, q` are consecutive primes: both prime, `p < q`, and no prime strictly
    between them. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬ r.Prime

/-- There are ≥ 4 primes strictly between `p²` and `q²`, exhibited as four
    strictly increasing primes `a < b < c < d` with `p² < a` and `d < q²`. -/
def FourPrimesBetweenSquares (p q : ℕ) : Prop :=
  ∃ a b c d : ℕ, p ^ 2 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < q ^ 2 ∧
    a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime

/-- Brocard's conjecture (OPEN): for consecutive primes `p < q` with `p ≥ 3`,
    there are at least four primes strictly between `p²` and `q²`.
    Recorded as an UNPROVEN `def` — this file never asserts or discharges it. -/
def BrocardGapConjecture : Prop :=
  ∀ p q : ℕ, 3 ≤ p → ConsecutivePrimes p q → FourPrimesBetweenSquares p q

/-! ## (1) Concrete instances (flagship) -/

/-- `(3, 5)`: consecutive primes, and `9 < 11 < 13 < 17 < 19 < 25`
    are four primes strictly between `3² = 9` and `5² = 25`. -/
theorem brocard_3_5 : ConsecutivePrimes 3 5 ∧ FourPrimesBetweenSquares 3 5 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩,
    ⟨11, 13, 17, 19, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr hr'; interval_cases r <;> norm_num
  all_goals norm_num

/-- `(5, 7)`: consecutive primes, and `25 < 29 < 31 < 37 < 41 < 49`
    are four primes strictly between `5² = 25` and `7² = 49`. -/
theorem brocard_5_7 : ConsecutivePrimes 5 7 ∧ FourPrimesBetweenSquares 5 7 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩,
    ⟨29, 31, 37, 41, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr hr'; interval_cases r <;> norm_num
  all_goals norm_num

/-- `(7, 11)`: consecutive primes, and `49 < 53 < 59 < 61 < 67 < 121`
    are four primes strictly between `7² = 49` and `11² = 121`. -/
theorem brocard_7_11 : ConsecutivePrimes 7 11 ∧ FourPrimesBetweenSquares 7 11 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩,
    ⟨53, 59, 61, 67, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr hr'; interval_cases r <;> norm_num
  all_goals norm_num

/-- `(11, 13)`: consecutive primes, and `121 < 127 < 131 < 137 < 139 < 169`
    are four primes strictly between `11² = 121` and `13² = 169`. -/
theorem brocard_11_13 :
    ConsecutivePrimes 11 13 ∧ FourPrimesBetweenSquares 11 13 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩,
    ⟨127, 131, 137, 139, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr hr'; interval_cases r <;> norm_num
  all_goals norm_num

/-- `(13, 17)`: consecutive primes, and `169 < 173 < 179 < 181 < 191 < 289`
    are four primes strictly between `13² = 169` and `17² = 289`. -/
theorem brocard_13_17 :
    ConsecutivePrimes 13 17 ∧ FourPrimesBetweenSquares 13 17 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩,
    ⟨173, 179, 181, 191, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr hr'; interval_cases r <;> norm_num
  all_goals norm_num

end Brockian.BrocardGap
