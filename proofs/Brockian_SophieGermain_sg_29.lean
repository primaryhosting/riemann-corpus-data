/-
  Brockian/SophieGermain.lean — Sophie Germain primes: concrete instances, the
  structural "p ≡ 5 (mod 6)" law, the safe-prime "≡ 11 (mod 12)" refinement, and
  the OPEN infinitude conjecture (recorded, never asserted).

  A Sophie Germain prime is a prime `p` such that `2p + 1` is also prime
  (the resulting prime `2p + 1` is the associated *safe prime*). Whether there are
  infinitely many Sophie Germain primes is a famous OPEN problem. This module does
  NOT resolve it. It:
    - verifies concrete Sophie Germain primes 2, 3, 5, 11, 23, 29, 41, 53 by `norm_num`;
    - proves the elementary structural fact that a Sophie Germain prime `p > 3`
      satisfies `p ≡ 5 (mod 6)`;
    - refines this to `2p + 1 ≡ 11 (mod 12)` for the safe prime when `p > 3`;
    - records `SophieGermainInfinitude` as an UNPROVEN `def` — a statement, not a
      theorem.

  Verification (spec §2A triple verification):
    - local `lake build`  : not authoritative here (see PORT-QUEUE.md)
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0
-/
import Mathlib

namespace Brockian.SophieGermain

/-- A Sophie Germain prime: `p` and `2 * p + 1` are both prime. The associated
prime `2 * p + 1` is the *safe prime*. -/
def SophieGermain (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-- The Sophie Germain infinitude conjecture (**OPEN**): there are infinitely many
Sophie Germain primes, phrased as "for every bound `N` there is a Sophie Germain
prime larger than `N`". This is an UNPROVEN `def` recording the statement — it is
never asserted as a theorem here. -/
def SophieGermainInfinitude : Prop := ∀ N : ℕ, ∃ p : ℕ, N < p ∧ SophieGermain p

/-! ## (1) Concrete Sophie Germain primes -/

/-- 2 is a Sophie Germain prime (2·2 + 1 = 5 is prime). -/
theorem sg_2 : SophieGermain 2 := ⟨by norm_num, by norm_num⟩

/-- 3 is a Sophie Germain prime (2·3 + 1 = 7 is prime). -/
theorem sg_3 : SophieGermain 3 := ⟨by norm_num, by norm_num⟩

/-- 5 is a Sophie Germain prime (2·5 + 1 = 11 is prime). -/
theorem sg_5 : SophieGermain 5 := ⟨by norm_num, by norm_num⟩

/-- 11 is a Sophie Germain prime (2·11 + 1 = 23 is prime). -/
theorem sg_11 : SophieGermain 11 := ⟨by norm_num, by norm_num⟩

/-- 23 is a Sophie Germain prime (2·23 + 1 = 47 is prime). -/
theorem sg_23 : SophieGermain 23 := ⟨by norm_num, by norm_num⟩

/-- 29 is a Sophie Germain prime (2·29 + 1 = 59 is prime). -/
theorem sg_29 : SophieGermain 29 := ⟨by norm_num, by norm_num⟩

/-- 41 is a Sophie Germain prime (2·41 + 1 = 83 is prime). -/
theorem sg_41 : SophieGermain 41 := ⟨by norm_num, by norm_num⟩

/-- 53 is a Sophie Germain prime (2·53 + 1 = 107 is prime). -/
theorem sg_53 : SophieGermain 53 := ⟨by norm_num, by norm_num⟩

/-! ## (2) Structural law: a Sophie Germain prime p > 3 satisfies p ≡ 5 (mod 6) -/

/-- **Sophie Germain residue law.** A Sophie Germain prime `p > 3` satisfies
`p ≡ 5 (mod 6)`.

Proof: `p` prime and `> 2` is odd, so `p % 2 = 1`. Also `3 ∤ p` (else `p = 3`,
contradicting `p > 3`), so `p % 6 ∈ {1, 5}`. If `p % 6 = 1` then `2p + 1 ≡ 0
(mod 3)`, so `3 ∣ (2p + 1)`; but `2p + 1` is prime, forcing `2p + 1 = 3`, which is
impossible since `p > 3` gives `2p + 1 ≥ 9`. Hence `p % 6 = 5`. -/
theorem sg_mod_six {p : ℕ} (h : SophieGermain p) (hp : 3 < p) : p % 6 = 5 := by
  obtain ⟨hp1, hq1⟩ := h
  -- `p` is odd (prime and > 3 ⇒ ≠ 2)
  have hodd : p % 2 = 1 := by
    rcases hp1.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  -- `3 ∤ p` : else `p = 3`, contradicting `p > 3`
  have h3p : ¬ (3 ∣ p) := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp1).mp hd
    omega
  have e1 : p % 3 ≠ 0 := fun hh => h3p (Nat.dvd_of_mod_eq_zero hh)
  -- `p` odd and `3 ∤ p` ⇒ `p % 6 ∈ {1, 5}`
  have hsix : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rcases hsix with h1 | h5
  · -- `p % 6 = 1` ⇒ `3 ∣ (2p + 1)`; prime ⇒ `2p + 1 = 3`, impossible
    exfalso
    have hdvd : 3 ∣ (2 * p + 1) := by
      have : (2 * p + 1) % 3 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq1).mp hdvd
    omega
  · exact h5

/-! ## (3) Safe-prime refinement: 2p + 1 ≡ 11 (mod 12) for p > 3 -/

/-- **Safe-prime residue law.** For a Sophie Germain prime `p > 3`, the associated
safe prime `2 * p + 1` satisfies `2 * p + 1 ≡ 11 (mod 12)`.

Proof: from `p % 6 = 5` (the residue law) and `p % 2 = 1` (`p` odd) we get
`p % 12 ∈ {5, 11}`; in either case `2 * p + 1 ≡ 11 (mod 12)`. -/
theorem sg_safe_mod {p : ℕ} (h : SophieGermain p) (hp : 3 < p) :
    (2 * p + 1) % 12 = 11 := by
  have hmod6 : p % 6 = 5 := sg_mod_six h hp
  obtain ⟨hp1, _⟩ := h
  have hodd : p % 2 = 1 := by
    rcases hp1.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  omega

end Brockian.SophieGermain
