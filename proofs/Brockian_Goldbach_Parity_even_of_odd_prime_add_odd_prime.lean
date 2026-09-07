/-
  Brockian/GoldbachParity.lean — unconditional parity lemmas for binary Goldbach.

  HONEST SCOPE: this module does NOT prove the Goldbach conjecture. It records
  elementary, hole-free facts about parity, the local count at the prime 2, and
  the odd-target obstruction. All statements are algebraic or combinatorial
  over Mathlib; none assert a global representation theorem for even integers.

  Contents (PROVED, axiom-clean):
    * Local count at p = 2: g₂(0) = 1, g₂(1) = 0 — only even targets are
      locally representable by nonzero residues mod 2.
    * Local covariance factor K₂: equals 2 on even shifts, 0 on odd shifts.
    * Odd Goldbach obstruction: an odd n that is a sum of two primes must be
      of the form 2 + q with q prime (and conversely).
    * Even scaffolding: even n ≥ 4 is 2 + (n−2) with n−2 even ≥ 2 (no
      primality claim on n−2).
    * Link gCount ↔ gResidues.card (Comb ↔ Lemmas local counts agree).
    * Residue-class candidate counts mod 5 via gResidues (p−1 / p−2 law).

  Verification: AXLE `check` @ lean-4.32.0; #print axioms ⊆
  {propext, Classical.choice, Quot.sound}. No sorry / admit / axiom /
  native_decide.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachLemmas
import Brockian.GoldbachSchema

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Brockian.Goldbach.Parity

open Finset
open Brockian.GoldbachComb
open Brockian.GoldbachLemmas
open Brockian.GoldbachSchema

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ## Local Goldbach count at the prime 2 -/

/-- At `p = 2` and even target `c = 0`, the local count is `1` (the single
ordered pair `(1,1)` of nonzero residues). -/
theorem gCount_two_zero : gCount 2 (0 : ZMod 2) = 1 := by
  rw [gCount_eq]
  simp

/-- At `p = 2` and odd target `c = 1`, the local count is `0`: there is no
ordered pair of nonzero residues mod 2 summing to 1. -/
theorem gCount_two_one : gCount 2 (1 : ZMod 2) = 0 := by
  rw [gCount_eq]
  simp

/-- Closed form of the local count at the prime 2: one representation when the
target is even mod 2, none when it is odd. (`2 - 1` / `2 - 2` reduce definitionally.) -/
theorem gCount_two (c : ZMod 2) : gCount 2 c = if c = 0 then 1 else 0 :=
  gCount_eq 2 c

/-- **Local parity obstruction.** Every nonzero residue mod 2 has local Goldbach
count zero. Binary Goldbach pairs of nonzero residues exist only for even
targets at the prime 2. -/
theorem gCount_two_of_ne_zero {c : ZMod 2} (hc : c ≠ 0) : gCount 2 c = 0 := by
  rw [gCount_two, if_neg hc]

/-! ## Local covariance factor at the prime 2 -/

/-- On even integer shifts the p=2 local covariance kernel equals `2`. -/
theorem Kp_two_of_dvd {h : ℤ} (hh : (2 : ℤ) ∣ h) : Kp 2 h = 2 := by
  simp [Kp, hh]
  norm_num

/-- On odd integer shifts the p=2 local covariance kernel vanishes. -/
theorem Kp_two_of_not_dvd {h : ℤ} (hh : ¬(2 : ℤ) ∣ h) : Kp 2 h = 0 := by
  simp [Kp, hh]
  norm_num

/-- Closed form: `K₂(h) = 2` if `2 ∣ h`, else `0`. Exact local identity; not a
transfer statement about the global Goldbach residual. -/
theorem Kp_two (h : ℤ) : Kp 2 h = if (2 : ℤ) ∣ h then (2 : ℚ) else 0 := by
  split_ifs with hh
  · exact Kp_two_of_dvd hh
  · exact Kp_two_of_not_dvd hh

/-! ## Odd Goldbach obstruction (elementary, unconditional) -/

/-- Sum of two odd primes is even. -/
theorem even_of_odd_prime_add_odd_prime {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    Even (p + q) := by
  have hop : Odd p := hp.odd_of_ne_two hp2
  have hoq : Odd q := hq.odd_of_ne_two hq2
  exact hop.add_odd hoq

/-- If an odd integer is a sum of two primes, one summand must be the prime 2
(the only even prime). Equivalently: odd Goldbach representations are exactly
of the form `2 + q` with `q` prime. -/
theorem hasGoldbachRep_odd_imp_two {n : ℕ} (hodd : Odd n)
    (h : HasGoldbachRep n) : ∃ q : ℕ, Nat.Prime q ∧ 2 + q = n := by
  obtain ⟨p, q, hp, hq, hsum⟩ := h
  rcases hp.eq_two_or_odd' with rfl | hop
  · exact ⟨q, hq, hsum⟩
  · rcases hq.eq_two_or_odd' with rfl | hoq
    · exact ⟨p, hp, by rw [← hsum, add_comm]⟩
    · have hev : Even (p + q) := hop.add_odd hoq
      rw [hsum] at hev
      exact (Nat.not_even_iff_odd.mpr hodd hev).elim

/-- Converse direction: `2 + q` with `q` prime is always a Goldbach
representation (model-free witness). -/
theorem hasGoldbachRep_two_plus_prime {q : ℕ} (hq : Nat.Prime q) :
    HasGoldbachRep (2 + q) :=
  ⟨2, q, Nat.prime_two, hq, rfl⟩

/-- Biconditional form of the odd-target obstruction for `n ≥ 2`. -/
theorem hasGoldbachRep_odd_iff {n : ℕ} (hodd : Odd n) (hn : 2 ≤ n) :
    HasGoldbachRep n ↔ Nat.Prime (n - 2) := by
  constructor
  · intro h
    obtain ⟨q, hq, hsum⟩ := hasGoldbachRep_odd_imp_two hodd h
    have hq' : q = n - 2 := by
      have : q + 2 = n := by rw [← hsum, add_comm]
      omega
    rwa [← hq']
  · intro hp
    have hsum : 2 + (n - 2) = n := Nat.add_sub_cancel' hn
    rw [← hsum]
    exact hasGoldbachRep_two_plus_prime hp

/-! ## Even scaffolding (no primality claim) -/

/-- Every even `n ≥ 4` decomposes as `2 + (n − 2)` with `n − 2` even and
at least `2`. Elementary scaffolding for binary Goldbach; does **not** assert
that `n − 2` is prime. -/
theorem even_ge_four_eq_two_plus_even {n : ℕ} (hev : Even n) (hn : 4 ≤ n) :
    n = 2 + (n - 2) ∧ Even (n - 2) ∧ 2 ≤ n - 2 := by
  have hn2 : 2 ≤ n := by omega
  refine ⟨(Nat.add_sub_cancel' hn2).symm, ?_, by omega⟩
  -- `Even n` and `Even 2` ⇒ `Even (n - 2)` for `n ≥ 2`.
  rw [even_iff_two_dvd] at hev ⊢
  exact Nat.dvd_sub hev (by decide : 2 ∣ 2)

/-- For even `n`, if `p` is an odd prime with `p ≤ n`, then `n − p` is odd.
Parity-compatible candidates for a two-odd-prime Goldbach pair. -/
theorem odd_sub_of_even_sub_odd_prime {n p : ℕ} (hev : Even n)
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hple : p ≤ n) : Odd (n - p) := by
  have hop : Odd p := hp.odd_of_ne_two hp2
  -- Even − Odd = Odd (on ℕ when p ≤ n).
  exact Nat.Even.sub_odd hple hev hop

/-! ## Comb ↔ Lemmas: local counts agree -/

/-- The ordered-pair local count `gCount` equals the first-coordinate count
`gResidues.card`: both enumerate nonzero residues `a` with `c − a ≠ 0`. -/
theorem gCount_eq_gResidues_card (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    gCount p c = (gResidues p c).card := by
  -- Both equal the closed form from `gCount_eq` / residue-card lemmas.
  by_cases hc : c = 0
  · subst hc
    rw [gCount_eq, gResidues_card_zero]
    simp
  · rw [gCount_eq, gResidues_card_ne_zero hc]
    simp [hc]

/-! ## Residue-class candidate counts mod 5 -/

/-- Local Goldbach candidate count mod 5: `4` when `5 ∣ n` (residue 0), else
`3`. Specialisation of the `p−1` / `p−2` law at `p = 5`. -/
theorem gResidues_five_card (n : ZMod 5) :
    (gResidues 5 n).card = if n = 0 then 4 else 3 := by
  by_cases hn : n = 0
  · subst hn
    rw [gResidues_card_zero]
    simp
  · rw [gResidues_card_ne_zero hn]
    simp [hn]

/-- Same count via the Comb local formula. (`5 - 1` / `5 - 2` reduce definitionally.) -/
theorem gCount_five (c : ZMod 5) :
    gCount 5 c = if c = 0 then 4 else 3 :=
  gCount_eq 5 c

end Brockian.Goldbach.Parity
