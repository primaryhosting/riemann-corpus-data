/-
  Brockian/PolignacPrimes.lean — de Polignac's conjecture (OPEN): concrete cousin
  primes (gap 4) and sexy primes (gap 6), their elementary residue constraints, and
  the conjecture itself recorded as an UNPROVEN `def` — never asserted as a theorem.

  De Polignac's conjecture states that for every positive even `k` there are infinitely
  many prime pairs `(p, p + k)`. It is OPEN for every `k` (the twin case `k = 2` is banked
  separately in `Brockian/TwinPrimes.lean`). This module does NOT resolve it. It:
    - verifies concrete cousin pairs (3,7) … (79,83) for gap `4` by `norm_num`;
    - verifies concrete sexy pairs (5,11) … (47,53) for gap `6` by `norm_num`;
    - proves the elementary structural fact that a cousin prime `p > 3` satisfies
      `p ≡ 1 (mod 6)` (so the pair is `(6k+1, 6k+5)`);
    - proves that a sexy prime `p > 3` shares its residue mod 6 with `p + 6`, that
      residue lying in `{1, 5}`;
    - records `PolignacConjecture` as an UNPROVEN `def` — a statement, not a theorem.

  Verification (spec §2A triple verification):
    - local `lake build`  : not authoritative here (see PORT-QUEUE.md)
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0
-/
import Mathlib

namespace Brockian.PolignacPrimes

/-- A prime pair with gap `k`: both `p` and `p + k` are prime. -/
def PrimeGapPair (k p : ℕ) : Prop := p.Prime ∧ (p + k).Prime

/-- de Polignac's conjecture (**OPEN**): every positive even gap `k` occurs infinitely
often — for each such `k` and every bound `N` there is a prime pair `(p, p + k)` with
`p > N`. This is an UNPROVEN `def` recording the statement; it is never asserted as a
theorem here, and this module does not resolve it for any `k`. -/
def PolignacConjecture : Prop :=
  ∀ k : ℕ, Even k → 0 < k → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ PrimeGapPair k p

/-! ## (1) Concrete cousin prime pairs (gap 4) -/

/-- (3, 7) is a cousin prime pair. -/
theorem cousin_3 : PrimeGapPair 4 3 := ⟨by norm_num, by norm_num⟩

/-- (7, 11) is a cousin prime pair. -/
theorem cousin_7 : PrimeGapPair 4 7 := ⟨by norm_num, by norm_num⟩

/-- (13, 17) is a cousin prime pair. -/
theorem cousin_13 : PrimeGapPair 4 13 := ⟨by norm_num, by norm_num⟩

/-- (19, 23) is a cousin prime pair. -/
theorem cousin_19 : PrimeGapPair 4 19 := ⟨by norm_num, by norm_num⟩

/-- (37, 41) is a cousin prime pair. -/
theorem cousin_37 : PrimeGapPair 4 37 := ⟨by norm_num, by norm_num⟩

/-- (43, 47) is a cousin prime pair. -/
theorem cousin_43 : PrimeGapPair 4 43 := ⟨by norm_num, by norm_num⟩

/-- (67, 71) is a cousin prime pair. -/
theorem cousin_67 : PrimeGapPair 4 67 := ⟨by norm_num, by norm_num⟩

/-- (79, 83) is a cousin prime pair. -/
theorem cousin_79 : PrimeGapPair 4 79 := ⟨by norm_num, by norm_num⟩

/-! ## (2) Concrete sexy prime pairs (gap 6) -/

/-- (5, 11) is a sexy prime pair. -/
theorem sexy_5 : PrimeGapPair 6 5 := ⟨by norm_num, by norm_num⟩

/-- (7, 13) is a sexy prime pair. -/
theorem sexy_7 : PrimeGapPair 6 7 := ⟨by norm_num, by norm_num⟩

/-- (11, 17) is a sexy prime pair. -/
theorem sexy_11 : PrimeGapPair 6 11 := ⟨by norm_num, by norm_num⟩

/-- (13, 19) is a sexy prime pair. -/
theorem sexy_13 : PrimeGapPair 6 13 := ⟨by norm_num, by norm_num⟩

/-- (17, 23) is a sexy prime pair. -/
theorem sexy_17 : PrimeGapPair 6 17 := ⟨by norm_num, by norm_num⟩

/-- (23, 29) is a sexy prime pair. -/
theorem sexy_23 : PrimeGapPair 6 23 := ⟨by norm_num, by norm_num⟩

/-- (31, 37) is a sexy prime pair. -/
theorem sexy_31 : PrimeGapPair 6 31 := ⟨by norm_num, by norm_num⟩

/-- (47, 53) is a sexy prime pair. -/
theorem sexy_47 : PrimeGapPair 6 47 := ⟨by norm_num, by norm_num⟩

/-! ## (3) Structural law: a cousin prime `p > 3` satisfies `p ≡ 1 (mod 6)` -/

/-- **Cousin-prime residue law.** For a cousin prime pair `(p, p + 4)` with `p > 3`,
the smaller prime satisfies `p % 6 = 1` (equivalently the pair is `(6k + 1, 6k + 5)`).

Proof: `p` prime and `> 3` is odd (`p % 2 = 1`) and not divisible by `3` (else `p = 3`).
Hence `p % 6 ∈ {1, 5}`. If `p % 6 = 5` then `(p + 4) % 6 = 3`, so `3 ∣ (p + 4)`; but
`p + 4` is prime and `≥ 7 > 3`, so `3 ∣ (p + 4)` forces `p + 4 = 3`, impossible. Thus
`p % 6 = 1`. -/
theorem cousin_mod_six {p : ℕ} (h : PrimeGapPair 4 p) (hp : 3 < p) : p % 6 = 1 := by
  obtain ⟨hp1, hp2⟩ := h
  -- `p` is odd: prime and `> 3` ⇒ `≠ 2`
  have hodd : p % 2 = 1 := by
    rcases hp1.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  -- `3 ∤ p` : else `p = 3`, contradicting `p > 3`
  have h3p : ¬ (3 ∣ p) := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp1).mp hd
    omega
  -- `3 ∤ (p + 4)` : else `p + 4 = 3`, contradicting `p > 3`
  have h3p4 : ¬ (3 ∣ (p + 4)) := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp2).mp hd
    omega
  have e1 : p % 3 ≠ 0 := fun hh => h3p (Nat.dvd_of_mod_eq_zero hh)
  have e2 : (p + 4) % 3 ≠ 0 := fun hh => h3p4 (Nat.dvd_of_mod_eq_zero hh)
  -- case on `p % 3`; only `p % 3 = 1` survives, and with `p % 2 = 1` gives `p % 6 = 1`
  have hr : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · exact absurd hr e1
  · omega                                            -- p % 3 = 1, p % 2 = 1 ⇒ p % 6 = 1
  · exact absurd (by omega : (p + 4) % 3 = 0) e2     -- p % 3 = 2 ⇒ (p + 4) % 3 = 0

/-! ## (3′) Corollary: a cousin pair with `p > 3` has the form `(6k + 1, 6k + 5)` -/

/-- Every cousin prime pair with `p > 3` has the shape `(6k + 1, 6k + 5)`. -/
theorem cousin_form_6k {p : ℕ} (h : PrimeGapPair 4 p) (hp : 3 < p) :
    ∃ k, p = 6 * k + 1 ∧ p + 4 = 6 * k + 5 := by
  have hm := cousin_mod_six h hp
  exact ⟨p / 6, by omega, by omega⟩

/-! ## (4) Bonus: sexy primes preserve residue mod 6 -/

/-- **Sexy-prime residue law.** For a sexy prime pair `(p, p + 6)` with `p > 3`, the two
primes share the same residue mod 6, and that residue lies in `{1, 5}`.

Proof: `(p + 6) % 6 = p % 6` is immediate. For the residue itself, `p` prime and `> 3` is
odd (`p % 2 = 1`) and not divisible by `3`, so `p % 6 ∈ {1, 5}`. -/
theorem sexy_same_mod_six {p : ℕ} (h : PrimeGapPair 6 p) (hp : 3 < p) :
    (p + 6) % 6 = p % 6 ∧ (p % 6 = 1 ∨ p % 6 = 5) := by
  obtain ⟨hp1, _⟩ := h
  have hodd : p % 2 = 1 := by
    rcases hp1.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  have h3p : ¬ (3 ∣ p) := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp1).mp hd
    omega
  have e1 : p % 3 ≠ 0 := fun hh => h3p (Nat.dvd_of_mod_eq_zero hh)
  exact ⟨by omega, by omega⟩

end Brockian.PolignacPrimes
