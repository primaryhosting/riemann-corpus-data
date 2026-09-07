import Mathlib

/-!
# Necessary conditions for odd perfect numbers

It is one of the oldest open problems in mathematics whether an **odd perfect number**
exists.  This file does *not* resolve that question.  Instead it proves genuine,
unconditional *necessary conditions*: true theorems of the shape

> IF an odd perfect number exists, THEN it must satisfy `P`.

Every result here is a real proof.  Nothing here asserts either the existence or the
non-existence of an odd perfect number.

We use Mathlib's `Nat.Perfect`, defined by
`Nat.Perfect n ↔ (∑ i ∈ n.properDivisors, i = n ∧ 0 < n)`, equivalently
`∑ d ∈ n.divisors, d = 2 * n` for `0 < n`.

## Main results

* `oddPerfect_not_square` — **flagship**: an odd perfect number is never a perfect square.
* `oddPerfect_pos`, `oddPerfect_one_lt`, `oddPerfect_not_two_dvd` — sanity constraints.
-/

namespace Brockian.OddPerfectConstraints

open Finset

/-- `n` is an *odd perfect number* if it is odd and perfect (in Mathlib's sense). -/
def OddPerfect (n : ℕ) : Prop := Odd n ∧ Nat.Perfect n

/-! ### Basic sanity constraints -/

/-- An odd perfect number is positive. -/
theorem oddPerfect_pos {n : ℕ} (h : OddPerfect n) : 0 < n := h.2.2

/-- An odd perfect number is not divisible by `2` (it is genuinely odd). -/
theorem oddPerfect_not_two_dvd {n : ℕ} (h : OddPerfect n) : ¬ 2 ∣ n := by
  have hmod : n % 2 = 1 := Nat.odd_iff.mp h.1
  omega

/-- An odd perfect number is strictly greater than `1` (`1` is not perfect). -/
theorem oddPerfect_one_lt {n : ℕ} (h : OddPerfect n) : 1 < n := by
  have hpos : 0 < n := h.2.2
  have hne1 : n ≠ 1 := by
    rintro rfl
    have hsum : ∑ i ∈ Nat.properDivisors 1, i = 1 := h.2.1
    simp [Nat.properDivisors_one] at hsum
  exact lt_of_le_of_ne hpos (Ne.symm hne1)

/-! ### Flagship: an odd perfect number is not a perfect square

The engine is the classical parity computation for the sum of divisors.  For an odd
square `n`, Mathlib's `Nat.sum_divisors` expresses `σ(n) = ∑_{d ∣ n} d` as a product,
over the prime factors `p` of `n`, of the geometric sums `∑_{k=0}^{v_p(n)} p^k`.  When
`n` is odd every such `p` is odd, and when `n` is a square every exponent `v_p(n)` is
even, so each geometric sum has an *odd* number of *odd* terms and is therefore odd;
the product of odd numbers is odd.  Hence `σ(n)` is odd.  But perfection forces
`σ(n) = 2n`, which is even — contradiction.
-/

/-- If `n` is a perfect square then every prime-factorization exponent of `n` is even. -/
theorem even_factorization_of_isSquare {n : ℕ} (hsq : IsSquare n) (p : ℕ) :
    Even (n.factorization p) := by
  obtain ⟨r, hr⟩ := hsq
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
      exact hn0 hr
    have : n.factorization p = r.factorization p + r.factorization p := by
      rw [hr, Nat.factorization_mul hr0 hr0, Finsupp.add_apply]
    exact ⟨r.factorization p, this⟩

/-- A prime divisor of an odd number is odd. -/
theorem odd_of_prime_dvd_odd {n p : ℕ} (hodd : Odd n) (hp : p.Prime) (hdvd : p ∣ n) :
    Odd p := by
  apply hp.odd_of_ne_two
  rintro rfl
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  omega

/-- **Flagship necessary condition.** An odd perfect number is never a perfect square.

This is a genuine constraint on the (open) existence problem: any odd perfect number,
should one exist, must fail to be a perfect square. -/
theorem oddPerfect_not_square {n : ℕ} (h : OddPerfect n) : ¬ IsSquare n := by
  obtain ⟨hodd, hperf⟩ := h
  intro hsq
  have hpos : 0 < n := hperf.2
  have hn0 : n ≠ 0 := hpos.ne'
  -- Perfection: the sum of divisors equals `2 * n`, hence is even.
  have hsum : ∑ d ∈ n.divisors, d = 2 * n :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hperf
  have heven : Even (∑ d ∈ n.divisors, d) := by
    rw [hsum]; exact even_two_mul n
  -- But the sum of divisors is odd.
  have hoddsum : Odd (∑ d ∈ n.divisors, d) := by
    rw [Nat.sum_divisors hn0]
    -- Product over prime factors of a geometric sum; show each factor is odd.
    apply Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpodd : Odd p := odd_of_prime_dvd_odd hodd hpp hpdvd
    have hfeven : Even (n.factorization p) := even_factorization_of_isSquare hsq p
    -- The geometric sum `∑_{k=0}^{v_p(n)} p^k` has an odd count of odd terms.
    rw [Finset.odd_sum_iff_odd_card_odd,
      Finset.filter_true_of_mem (fun x _ => hpodd.pow), Finset.card_range]
    exact hfeven.add_one
  have h1 : (∑ d ∈ n.divisors, d) % 2 = 1 := Nat.odd_iff.mp hoddsum
  have h2 : (∑ d ∈ n.divisors, d) % 2 = 0 := Nat.even_iff.mp heven
  omega

/-! ### An odd perfect number is not a prime power

Every power of a prime is *deficient* (`Nat.Prime.deficient_pow`): the sum of its proper
divisors is strictly less than the number itself.  A perfect number has that sum equal to
itself, so no prime power is perfect.  In particular an odd perfect number, if it exists,
must have at least two distinct prime factors — another genuine necessary condition,
consistent with (indeed weaker than) Euler's classical form `n = p^k · m²`. -/
theorem oddPerfect_not_prime_pow {n : ℕ} (h : OddPerfect n) :
    ¬ ∃ p k : ℕ, p.Prime ∧ n = p ^ k := by
  rintro ⟨p, k, hp, rfl⟩
  have hdef : ∑ i ∈ (p ^ k).properDivisors, i < p ^ k := hp.deficient_pow
  have hperf : ∑ i ∈ (p ^ k).properDivisors, i = p ^ k := h.2.1
  omega

end Brockian.OddPerfectConstraints
