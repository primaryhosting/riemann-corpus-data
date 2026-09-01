/-
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian

/-- `wheelWitnessK2` is a table of small "wheel" primes: entry `i` is the least prime `p`
such that both `p` and `2 * i - p` are prime (and `0` for `i < 2`). -/
def wheelWitnessK2 : List Nat :=
 [
  0, 0, 2, 3, 3, 3, 5, 3, 3, 5, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7,
  3, 3, 5, 7, 3, 5, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 3, 5, 3, 3, 5, 3, 5, 7,
  13, 11, 13, 19, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5,
  7, 3, 3, 5, 7, 11, 11, 3, 3, 5, 3, 3, 5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 13, 3, 5, 3, 3, 5,
  3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 5, 7, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11,
  3, 5, 7, 19, 11, 13, 31, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 7, 3, 5, 7, 29, 11, 3,
  3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 5, 7, 13,
  3, 5, 7, 17, 11, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 3, 5,
  3, 5, 7, 13, 11, 13, 3, 5, 7, 31, 3, 5, 3, 5, 7, 13, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 3,
  3, 5, 7, 11, 11, 13, 17, 17, 19, 3, 5, 7, 3, 5, 7, 47, 11, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3,
  5, 7, 17, 11, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13, 3, 5, 7,
  23, 11, 3, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 11, 11, 13, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5,
  7, 17, 11, 3, 5, 7, 19, 3, 5, 7, 17, 11, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 13, 3,
  5, 7, 3, 5, 3, 5, 7, 13, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 7, 23, 11, 3, 5, 7, 19, 11, 13,
  3, 3, 5, 7, 11, 11, 3, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 31, 3, 5, 3, 3, 5, 3,
  5, 7, 13, 11, 13, 19, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 17, 19, 31, 3, 5, 3, 5, 7, 13,
  3, 5, 7, 17, 11, 3, 5, 7, 19, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 43, 11, 13, 31, 3, 5, 3, 5, 7,
  3, 5, 7, 3, 5, 7, 73, 3, 5, 7, 3, 5, 7, 23, 11, 13, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 3,
  5, 7, 3, 5, 7, 17, 11
 ]

/-- The table entry attached to an even number `n`. -/
def wheelSmallK2 (n : Nat) : Nat := wheelWitnessK2.getD (n / 2) 0

/-- Certified check of the whole table: for every index `2 ≤ i < 526`, the tabulated value
`p` is prime, `2 * i - p` is prime, `p ≤ 2 * i`, and `p ≤ 73`. -/
theorem wheelWitnessK2_spec : ∀ i < 526, 2 ≤ i →
    Nat.Prime (wheelWitnessK2.getD i 0) ∧ Nat.Prime (2 * i - wheelWitnessK2.getD i 0) ∧
      wheelWitnessK2.getD i 0 ≤ 2 * i ∧ wheelWitnessK2.getD i 0 ≤ 73 := by decide

/-- **Goldbach wheel, `K = 2`, modulus `1051`.**
Every even number `n` with `4 ≤ n ≤ 1051` is a sum of two primes, and moreover the smaller
prime can always be taken from the wheel of primes below `74`. -/
theorem GoldbachWheelK2_1051 (n : Nat) (h4 : 4 ≤ n) (hn : n ≤ 1051) (he : Even n) :
    ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ 73 ∧ p + q = n := by
  obtain ⟨m, hm⟩ := he
  have hlt : n / 2 < 526 := by omega
  have hge : 2 ≤ n / 2 := by omega
  obtain ⟨hp, hq, hle, h73⟩ := wheelWitnessK2_spec (n / 2) hlt hge
  exact ⟨wheelWitnessK2.getD (n / 2) 0, 2 * (n / 2) - wheelWitnessK2.getD (n / 2) 0,
    hp, hq, h73, by omega⟩

end Brockian

