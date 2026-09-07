import Mathlib

/-!
# Carmichael numbers via Korselt's criterion, and the three-prime open sub-problem

A **Carmichael number** is a composite `n` that is a Fermat pseudoprime to every base
coprime to it (`a^n ≡ a (mod n)` for all `a`).  **Korselt's criterion** (1899) gives a
purely arithmetic characterisation: `n` is a Carmichael number **iff** `n` is composite,
squarefree, and `(p − 1) ∣ (n − 1)` for every prime `p ∣ n`.  The smallest Carmichael
number is `561 = 3 · 11 · 17`; the next are `1105`, `1729`, `2465`, …

This file works with the Korselt property directly (see `Korselt` below), which by
Korselt's criterion is equivalent to being a Carmichael number.  It

* verifies the three classical Carmichael numbers `561`, `1105`, `1729` as Korselt numbers,
  kernel-checked (each factorisation pinned via `Nat.Prime.dvd_mul`, avoiding a
  `decide`/`interval_cases` blow-up over the full range);
* proves the elementary **necessary condition** that every Korselt (Carmichael) number is
  **odd**; and
* records the genuinely **OPEN** three-prime refinement as an unproven `def`.

## Honesty note on what is and is not open

That there are **infinitely many** Carmichael numbers is a **theorem** (Alford–Granville–
Pomerance, 1994) — it is *not* recorded here as open.  What remains **open** is whether
there are infinitely many Carmichael numbers with **exactly three prime factors**; that
refinement is the `def` `ThreePrimeCarmichaelInfinitude` below, and this file makes **no
claim** to resolve it.

Mathlib's `ArithmeticFunction.carmichael` is the *Carmichael function* `λ` (the reduced
totient), an unrelated object; Mathlib has no Carmichael-number / Korselt predicate, so the
`Korselt` predicate here is developed from first principles.
-/

namespace Brockian.CarmichaelKorselt

/-- The Korselt property: `n` is `> 1`, composite (not prime), squarefree, and
`(p − 1) ∣ (n − 1)` for every prime `p ∣ n`.  By Korselt's criterion this is equivalent to
`n` being a Carmichael number. -/
def Korselt (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- OPEN: are there infinitely many Carmichael (Korselt) numbers with **exactly three**
prime factors?  Recorded as an unproven `def`; this file does **not** resolve it.  (The
*general* infinitude of Carmichael numbers is a theorem of Alford–Granville–Pomerance 1994 —
this three-prime refinement is the part that is open.) -/
def ThreePrimeCarmichaelInfinitude : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Korselt n ∧ n.primeFactors.card = 3

/-! ## Concrete verified Carmichael (Korselt) numbers -/

/-- Helper: a product `a * (b * c)` of three pairwise-distinct primes is squarefree.
`Squarefree` of a numeral is not kernel-`decide`-able (its instance goes through the
well-founded `Nat.minSqFac`), so we build squarefreeness structurally from
`Nat.squarefree_mul_iff` and `Nat.Prime.prime.squarefree`. -/
private theorem sqfree_prod3 {a b c : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (habc : a.Coprime (b * c)) (hbc : b.Coprime c) :
    Squarefree (a * (b * c)) := by
  rw [Nat.squarefree_mul_iff]
  refine ⟨habc, ha.prime.squarefree, ?_⟩
  rw [Nat.squarefree_mul_iff]
  exact ⟨hbc, hb.prime.squarefree, hc.prime.squarefree⟩

/-- FLAGSHIP — `561 = 3 · 11 · 17` is a Carmichael number (Korselt number), the smallest one.
Here `n − 1 = 560`, and the prime divisors are exactly `{3, 11, 17}`, with
`3 − 1 = 2 ∣ 560`, `11 − 1 = 10 ∣ 560`, `17 − 1 = 16 ∣ 560`.
The universally-quantified prime `p` is pinned to one of the three factors via
`Nat.Prime.dvd_mul`, so each divisibility obligation is a single `decide`. -/
theorem korselt_561 : Korselt 561 := by
  refine ⟨by norm_num, by norm_num, ?_, fun p hp hpd => ?_⟩
  · rw [show (561 : ℕ) = 3 * (11 * 17) from by norm_num]
    exact sqfree_prod3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h : (561 : ℕ) = 3 * (11 * 17) := by norm_num
  rw [h] at hpd
  rcases hp.dvd_mul.1 hpd with h3 | h1117
  · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3
    subst this; decide
  · rcases hp.dvd_mul.1 h1117 with h11 | h17
    · have : p = 11 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h11
      subst this; decide
    · have : p = 17 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h17
      subst this; decide

/-- BONUS — `1105 = 5 · 13 · 17` is a Carmichael number.
Here `n − 1 = 1104`, with `5 − 1 = 4 ∣ 1104`, `13 − 1 = 12 ∣ 1104`, `17 − 1 = 16 ∣ 1104`. -/
theorem korselt_1105 : Korselt 1105 := by
  refine ⟨by norm_num, by norm_num, ?_, fun p hp hpd => ?_⟩
  · rw [show (1105 : ℕ) = 5 * (13 * 17) from by norm_num]
    exact sqfree_prod3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h : (1105 : ℕ) = 5 * (13 * 17) := by norm_num
  rw [h] at hpd
  rcases hp.dvd_mul.1 hpd with h5 | h1317
  · have : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5
    subst this; decide
  · rcases hp.dvd_mul.1 h1317 with h13 | h17
    · have : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h13
      subst this; decide
    · have : p = 17 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h17
      subst this; decide

/-- BONUS — `1729 = 7 · 13 · 19`, the Hardy–Ramanujan taxicab number, is a Carmichael number.
Here `n − 1 = 1728`, with `7 − 1 = 6 ∣ 1728`, `13 − 1 = 12 ∣ 1728`, `19 − 1 = 18 ∣ 1728`. -/
theorem korselt_1729 : Korselt 1729 := by
  refine ⟨by norm_num, by norm_num, ?_, fun p hp hpd => ?_⟩
  · rw [show (1729 : ℕ) = 7 * (13 * 19) from by norm_num]
    exact sqfree_prod3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h : (1729 : ℕ) = 7 * (13 * 19) := by norm_num
  rw [h] at hpd
  rcases hp.dvd_mul.1 hpd with h7 | h1319
  · have : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7
    subst this; decide
  · rcases hp.dvd_mul.1 h1319 with h13 | h19
    · have : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h13
      subst this; decide
    · have : p = 19 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h19
      subst this; decide

/-! ## The necessary condition: every Carmichael (Korselt) number is odd -/

/-- FLAGSHIP NECESSARY CONDITION — every Korselt (Carmichael) number is **odd**.

Suppose `n` were even.  Write `n = 2 · m`.  Squarefreeness forbids `4 ∣ n`, so `m` is odd,
and `m > 1` (else `n = 2` is prime, contradicting compositeness).  Let `p = m.minFac`, an
**odd** prime dividing `m` and hence `n`.  The Korselt condition gives `(p − 1) ∣ (n − 1)`;
since `p` is odd, `p − 1` is even, so `2 ∣ (n − 1)`.  But `n` is even, so `n − 1` is odd —
contradiction. -/
theorem korselt_odd {n : ℕ} (h : Korselt n) : Odd n := by
  obtain ⟨hn1, hnp, hsf, hkor⟩ := h
  -- `n` cannot be `2`, since `2` is prime and `n` is composite.
  have hne2 : n ≠ 2 := by rintro rfl; exact hnp Nat.prime_two
  rw [Nat.odd_iff]
  by_contra hodd
  -- `n` even: from `¬ (n % 2 = 1)` and `n % 2 < 2`, get `2 ∣ n`.
  have h2n : 2 ∣ n := by omega
  obtain ⟨m, hm⟩ := h2n
  -- Squarefreeness forbids `4 ∣ n`, so `m` is odd.
  have h2m : ¬ (2 ∣ m) := by
    rintro ⟨k, hk⟩
    have h4 : 2 * 2 ∣ n := ⟨k, by rw [hm, hk]; ring⟩
    exact (Nat.squarefree_iff_prime_squarefree.1 hsf) 2 Nat.prime_two h4
  -- `m > 1`: `m = 0` gives `n = 0`, `m = 1` gives `n = 2`; both excluded.
  have hm1 : 1 < m := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m <;> omega
    · omega
  -- `p := m.minFac` is an odd prime dividing `n`.
  have hp : (m.minFac).Prime := Nat.minFac_prime (by omega)
  have hpm : m.minFac ∣ m := Nat.minFac_dvd m
  have hpn : m.minFac ∣ n := hpm.trans ⟨2, by rw [hm]; ring⟩
  have hpne2 : m.minFac ≠ 2 := by rintro he; rw [he] at hpm; exact h2m hpm
  have hpodd : Odd (m.minFac) := hp.odd_of_ne_two hpne2
  -- Korselt at `p`, then `p − 1` even gives `2 ∣ (n − 1)`.
  have hkp : (m.minFac - 1) ∣ (n - 1) := hkor m.minFac hp hpn
  obtain ⟨j, hj⟩ := hpodd
  have h2p : 2 ∣ (m.minFac - 1) := ⟨j, by omega⟩
  have h2sub : 2 ∣ (n - 1) := h2p.trans hkp
  -- `n` even but `n − 1` even is impossible.
  omega

end Brockian.CarmichaelKorselt
