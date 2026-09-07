import Mathlib

/-!
# Primes of the form `n² + 1`: concrete instances, the parity constraint, and Landau's open problem

**Landau's fourth problem** (Edmund Landau, 1912 ICM, still **OPEN**): are there
infinitely many primes of the form `n² + 1`? This module records the **concrete,
fully verified** facts that surround this question and isolates — as an *unproven
definition* — the genuinely open conjecture itself.

## What is a theorem (settled) vs. what is open

The **concrete witnesses** below (`n = 1, 2, 4, 6, 10, 14, 16, 20, 24, 26`, giving
the primes `2, 5, 17, 37, 101, 197, 257, 401, 577, 677`) are each verified by
`decide`/`norm_num` on the decidable predicate `Nat.Prime`.

The **structural constraint** `nsq_even_of_prime` is a genuine elementary theorem:
for `n > 1`, if `n² + 1` is prime then `n` must be *even*. (If `n` were odd then
`n²` is odd, so `n² + 1` is even and `≥ 4 > 2`, hence composite — contradicting
primality, since the only even prime is `2`.)

What is genuinely **open** is the infinitude claim: whether there are arbitrarily
large `n` with `n² + 1` prime. This is recorded below as `LandauFourthConjecture`.
It is a `def` of type `Prop`; it is **never asserted**, proved, or refuted anywhere
in this file. Nothing here resolves Landau's problem.

None of the proofs below use `sorry`, `admit`, `native_decide`, or any added axiom.

## References
* Landau's problems: <https://en.wikipedia.org/wiki/Landau%27s_problems>
* Primes of the form `n²+1` (OEIS A002496): <https://oeis.org/A002496>
-/

namespace Brockian.LandauNSquaredPlusOne

/-- `n² + 1` is prime. Since `Nat.Prime` is decidable, this predicate is decidable. -/
def NSqPlusOnePrime (n : ℕ) : Prop := (n ^ 2 + 1).Prime

/-- **Landau's fourth problem (OPEN)**: there are infinitely many primes of the
form `n² + 1`, phrased as "beyond every bound there is another such `n`". This is
an *unproven definition*; it is never asserted, proved, or refuted in this file. -/
def LandauFourthConjecture : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ NSqPlusOnePrime n

/-! ## (1) FLAGSHIP — concrete primes of the form `n² + 1`

Each proof reduces to the decidable primality of the literal value `n² + 1`. -/

/-- `1² + 1 = 2` is prime. -/
theorem nsq_1  : NSqPlusOnePrime 1  := by norm_num [NSqPlusOnePrime]

/-- `2² + 1 = 5` is prime. -/
theorem nsq_2  : NSqPlusOnePrime 2  := by norm_num [NSqPlusOnePrime]

/-- `4² + 1 = 17` is prime. -/
theorem nsq_4  : NSqPlusOnePrime 4  := by norm_num [NSqPlusOnePrime]

/-- `6² + 1 = 37` is prime. -/
theorem nsq_6  : NSqPlusOnePrime 6  := by norm_num [NSqPlusOnePrime]

/-- `10² + 1 = 101` is prime. -/
theorem nsq_10 : NSqPlusOnePrime 10 := by norm_num [NSqPlusOnePrime]

/-- `14² + 1 = 197` is prime. -/
theorem nsq_14 : NSqPlusOnePrime 14 := by norm_num [NSqPlusOnePrime]

/-- `16² + 1 = 257` is prime. -/
theorem nsq_16 : NSqPlusOnePrime 16 := by norm_num [NSqPlusOnePrime]

/-- `20² + 1 = 401` is prime. -/
theorem nsq_20 : NSqPlusOnePrime 20 := by norm_num [NSqPlusOnePrime]

/-- `24² + 1 = 577` is prime. -/
theorem nsq_24 : NSqPlusOnePrime 24 := by norm_num [NSqPlusOnePrime]

/-- `26² + 1 = 677` is prime. -/
theorem nsq_26 : NSqPlusOnePrime 26 := by norm_num [NSqPlusOnePrime]

/-! ## (2) FLAGSHIP STRUCTURAL — the parity constraint

For `n > 1`, if `n² + 1` is prime then `n` is **even**. -/

/-- **Structural constraint.** If `n > 1` and `n² + 1` is prime, then `n` is even.
Proof: were `n` odd, `n²` would be odd, making `n² + 1` even; but `n > 1` forces
`n² + 1 ≥ 5 > 2`, and the only even prime is `2` — contradiction. -/
theorem nsq_even_of_prime {n : ℕ} (h : NSqPlusOnePrime n) (hn : 1 < n) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · -- `n` odd ⇒ `n²` odd ⇒ `n² + 1` even, and `≥ 4`, contradicting primality.
    exfalso
    have hsq_odd : Odd (n ^ 2) := ho.pow
    have heven : Even (n ^ 2 + 1) := by
      rcases hsq_odd with ⟨k, hk⟩
      exact ⟨k + 1, by omega⟩
    have hp : (n ^ 2 + 1).Prime := h
    have h2 : n ^ 2 + 1 = 2 := (Nat.Prime.even_iff hp).mp heven
    have hge : 4 ≤ n ^ 2 := by nlinarith [hn]
    omega

/-! ## (3) BONUS — the parity constraint as a modular statement

A direct corollary of `nsq_even_of_prime`: under the same hypotheses, `n % 2 = 0`. -/

/-- **Corollary.** For `n > 1`, if `n² + 1` is prime then `n % 2 = 0`. -/
theorem nsq_mod_two_of_prime {n : ℕ} (h : NSqPlusOnePrime n) (hn : 1 < n) : n % 2 = 0 :=
  Nat.even_iff.mp (nsq_even_of_prime h hn)

end Brockian.LandauNSquaredPlusOne
