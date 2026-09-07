import Mathlib

/-!
# Fermat "prime beyond four" reduction via Pépin's test

REDUCTION-EQUIVALENCE (CONDITIONAL): the main theorem below proves an unconditional
equivalence `A ↔ B`; **both sides remain OPEN** — this is a Lean-checked reduction of the
"is there a Fermat prime beyond `F_4`?" question to Pépin's criterion, **NOT** a resolution
of it.

The existence of a Fermat prime `F_n = 2^(2^n) + 1` with `n > 4` (i.e. beyond `F_4 = 65537`)
is an open problem.  What is proved here is a *complete, unconditional reduction* of that
statement to Pépin's criterion: for every `n ≥ 1`,

  `F_n` is prime  ↔  `3 ^ ((F_n - 1)/2) = -1` in `ZMod (F_n)`.

The `←` direction is Mathlib's `Nat.pepin_primality`; the `→` direction (that `3` is a
quadratic non-residue modulo a Fermat prime) is proved here from quadratic reciprocity
and Euler's criterion.  Both sides of `FermatPrimeBeyondFour` are open.
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace Brockian.FermatNumbersReduction

open Nat

/-- `F_n % 4 = 1` for `n ≥ 1`. -/
lemma fermatNumber_mod_four (n : ℕ) (hn : 1 ≤ n) : fermatNumber n % 4 = 1 := by
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 2 := ⟨2 ^ n - 2, by omega⟩
  unfold fermatNumber
  rw [hk, pow_add]
  omega

/-- `F_n % 3 = 2` for `n ≥ 1`. -/
lemma fermatNumber_mod_three (n : ℕ) (hn : 1 ≤ n) : fermatNumber n % 3 = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = 2 * m := ⟨2 ^ (n - 1), by
    rw [← pow_succ']
    congr 1
    omega⟩
  have h : 2 ^ (2 ^ n) % 3 = 1 := by
    rw [hm, pow_mul]
    have h4 : (2 : ℕ) ^ 2 = 3 + 1 := by norm_num
    rw [h4]
    simpa using Nat.pow_mod (3 + 1) m 3
  unfold fermatNumber
  omega

/-- Euler's criterion applied to a Fermat prime: `3` is a quadratic non-residue modulo
`F_n` for `n ≥ 1`, hence the converse direction of Pépin's test. -/
lemma pepin_converse (n : ℕ) (hn : 1 ≤ n) (hp : (fermatNumber n).Prime) :
    (3 : ZMod (fermatNumber n)) ^ (2 ^ (2 ^ n - 1)) = -1 := by
  haveI : Fact (fermatNumber n).Prime := ⟨hp⟩
  have h4 : fermatNumber n % 4 = 1 := fermatNumber_mod_four n hn
  have h3 : fermatNumber n % 3 = 2 := fermatNumber_mod_three n hn
  -- Quadratic reciprocity: since `F_n ≡ 1 [MOD 4]`, `(3 | F_n) = (F_n | 3)`.
  have hqr : legendreSym 3 (fermatNumber n : ℤ) = legendreSym (fermatNumber n) 3 :=
    legendreSym.quadratic_reciprocity_one_mod_four h4 (by norm_num)
  -- and `F_n ≡ 2 [MOD 3]`, while `2` is a non-residue mod `3`.
  have hleft : legendreSym 3 (fermatNumber n : ℤ) = -1 := by
    rw [legendreSym.mod 3 (fermatNumber n : ℤ)]
    have h : ((fermatNumber n : ℤ) % ((3 : ℕ) : ℤ)) = 2 := by omega
    rw [h]
    exact (by decide : legendreSym 3 2 = -1)
  -- Euler's criterion turns this into the Pépin congruence.
  have heuler := legendreSym.eq_pow (fermatNumber n) (3 : ℤ)
  rw [hqr.symm.trans hleft] at heuler
  have hdiv : fermatNumber n / 2 = 2 ^ (2 ^ n - 1) := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : (2 : ℕ) ^ (2 ^ n) = 2 * 2 ^ (2 ^ n - 1) := by
      rw [← _root_.pow_succ']
      congr 1
      omega
    unfold fermatNumber
    omega
  rw [hdiv] at heuler
  push_cast at heuler
  exact heuler.symm

/-- **Pépin's test**, as an equivalence: for `n ≥ 1`, the Fermat number `F_n` is prime
iff `3 ^ (2 ^ (2 ^ n - 1)) = -1` in `ZMod (F_n)`. -/
theorem pepin_iff (n : ℕ) (hn : 1 ≤ n) :
    (fermatNumber n).Prime ↔ (3 : ZMod (fermatNumber n)) ^ (2 ^ (2 ^ n - 1)) = -1 :=
  ⟨pepin_converse n hn, fun h => Nat.pepin_primality n h⟩

/-- **Conditional reduction of the "Fermat prime beyond four" conjecture.**
There is a Fermat prime `F_n` with `n > 4` if and only if Pépin's criterion
`3 ^ (2 ^ (2 ^ n - 1)) = -1 (mod F_n)` holds for some `n > 4`. -/
theorem FermatPrimeBeyondFour :
    (∃ n, 4 < n ∧ Nat.Prime (fermatNumber n)) ↔
      (∃ n, 4 < n ∧ (3 : ZMod (fermatNumber n)) ^ (2 ^ (2 ^ n - 1)) = -1) := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, (pepin_iff n (by omega)).1 hp⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, (pepin_iff n (by omega)).2 h⟩

/-- Sanity check that the criterion is satisfiable: `F_4 = 65537` is prime, so Pépin's
congruence holds for `n = 4` (the largest currently known Fermat prime). -/
lemma pepin_at_four : (3 : ZMod (fermatNumber 4)) ^ (2 ^ (2 ^ 4 - 1)) = -1 :=
  (pepin_iff 4 (by norm_num)).1 (by norm_num [fermatNumber])

end Brockian.FermatNumbersReduction
