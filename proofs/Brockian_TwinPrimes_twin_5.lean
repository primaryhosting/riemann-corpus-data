/-
  Brockian/TwinPrimes.lean — twin primes: concrete pairs, the structural
  "middle divisible by 6" law, and the OPEN conjecture (recorded, never asserted).

  The twin prime conjecture — that there are infinitely many primes `p` with `p + 2`
  also prime — is OPEN. This module does NOT resolve it. It:
    - verifies concrete twin pairs (3,5) … (71,73) by `decide`/`norm_num`;
    - proves the elementary structural fact that for a twin pair with `p ≥ 5` the
      middle number `p + 1` is divisible by 6 (equivalently the pair is `(6k−1, 6k+1)`);
    - records `TwinPrimeConjecture` as an UNPROVEN `def` — a statement, not a theorem.

  Verification (spec §2A triple verification):
    - local `lake build`  : not authoritative here (see PORT-QUEUE.md)
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0
-/
import Mathlib

namespace Brockian.TwinPrimes

/-- `p` is the smaller of a twin prime pair: both `p` and `p + 2` are prime. -/
def TwinPrime (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

/-- The twin prime conjecture (**OPEN**): there are infinitely many twin primes,
phrased as "for every bound `N` there is a twin prime larger than `N`". This is an
UNPROVEN `def` recording the statement — it is never asserted as a theorem here. -/
def TwinPrimeConjecture : Prop := ∀ N : ℕ, ∃ p : ℕ, N < p ∧ TwinPrime p

/-! ## (1) Concrete twin prime pairs -/

/-- (3, 5) is a twin prime pair. -/
theorem twin_3 : TwinPrime 3 := ⟨by norm_num, by norm_num⟩

/-- (5, 7) is a twin prime pair. -/
theorem twin_5 : TwinPrime 5 := ⟨by norm_num, by norm_num⟩

/-- (11, 13) is a twin prime pair. -/
theorem twin_11 : TwinPrime 11 := ⟨by norm_num, by norm_num⟩

/-- (17, 19) is a twin prime pair. -/
theorem twin_17 : TwinPrime 17 := ⟨by norm_num, by norm_num⟩

/-- (29, 31) is a twin prime pair. -/
theorem twin_29 : TwinPrime 29 := ⟨by norm_num, by norm_num⟩

/-- (41, 43) is a twin prime pair. -/
theorem twin_41 : TwinPrime 41 := ⟨by norm_num, by norm_num⟩

/-- (59, 61) is a twin prime pair. -/
theorem twin_59 : TwinPrime 59 := ⟨by norm_num, by norm_num⟩

/-- (71, 73) is a twin prime pair. -/
theorem twin_71 : TwinPrime 71 := ⟨by norm_num, by norm_num⟩

/-! ## (2) Structural law: the middle of a twin pair (p ≥ 5) is divisible by 6 -/

/-- **Twin-pair middle law.** For a twin prime pair with `p ≥ 5`, the middle
number `p + 1` is divisible by `6`.

Proof: `p` prime and `> 2` is odd, so `2 ∣ (p + 1)`. Neither `p` nor `p + 2`
is divisible by `3` (each would force it to *equal* `3`, impossible for `p ≥ 5`),
so among `p, p+1, p+2` the one divisible by `3` is the middle, i.e. `3 ∣ (p + 1)`.
Being divisible by both `2` and `3` gives `6 ∣ (p + 1)`. -/
theorem twin_middle_div_six {p : ℕ} (h : TwinPrime p) (hp : 5 ≤ p) : 6 ∣ (p + 1) := by
  obtain ⟨hp1, hp2⟩ := h
  -- `p` is odd (prime and ≥ 5 ⇒ ≠ 2)
  have hodd : p % 2 = 1 := by
    rcases hp1.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  -- `3 ∤ p` : else `p = 3`, contradicting `p ≥ 5`
  have h3p : ¬ (3 ∣ p) := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp1).mp hd
    omega
  -- `3 ∤ (p + 2)` : else `p + 2 = 3`, contradicting `p ≥ 5`
  have h3p2 : ¬ (3 ∣ (p + 2)) := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp2).mp hd
    omega
  -- `p` odd ⇒ `2 ∣ (p+1)`
  have h2 : 2 ∣ (p + 1) := by omega
  -- `3 ∤ p` and `3 ∤ (p+2)` in mod form ⇒ `3 ∣ (p+1)`, by cases on `p % 3`
  have e1 : p % 3 ≠ 0 := fun hh => h3p (Nat.dvd_of_mod_eq_zero hh)
  have e2 : (p + 2) % 3 ≠ 0 := fun hh => h3p2 (Nat.dvd_of_mod_eq_zero hh)
  have h3 : 3 ∣ (p + 1) := by
    have hr : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · exact absurd hr e1
    · exact absurd (by omega : (p + 2) % 3 = 0) e2  -- p % 3 = 1 ⇒ (p+2) % 3 = 0
    · omega                                           -- p % 3 = 2 ⇒ 3 ∣ (p+1)
  -- combine via coprimality `2 ⟂ 3`
  have key : 2 * 3 ∣ (p + 1) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  simpa using key

/-! ## (3) Corollary: a twin pair with p ≥ 5 has the form (6k − 1, 6k + 1) -/

/-- Every twin prime pair with `p ≥ 5` has the shape `(6k − 1, 6k + 1)`. -/
theorem twin_form_6k {p : ℕ} (h : TwinPrime p) (hp : 5 ≤ p) :
    ∃ k, p = 6 * k - 1 ∧ p + 2 = 6 * k + 1 := by
  obtain ⟨k, hk⟩ := twin_middle_div_six h hp
  exact ⟨k, by omega, by omega⟩

end Brockian.TwinPrimes
