import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FermatNumbers

private instance factPrimeThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The Pépin condition for the `n`-th Fermat number `Fₙ = 2 ^ 2 ^ n + 1`:
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/
def PepinCondition (n : ℕ) : Prop :=
  (3 : ZMod (Nat.fermatNumber n)) ^ 2 ^ (2 ^ n - 1) = -1

/-- `Fₙ ≡ 1 [MOD 4]` for `n ≥ 1`. -/
lemma fermatNumber_mod_four (n : ℕ) (hn : 1 ≤ n) : Nat.fermatNumber n % 4 = 1 := by
  have h2 : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h : (2 : ℕ) ^ 2 ^ n = 4 * 2 ^ (2 ^ n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    omega
  simp [Nat.fermatNumber, h, Nat.add_mod, Nat.mul_mod_right]

/-- `Fₙ ≡ 2 [MOD 3]` for `n ≥ 1`. -/
lemma fermatNumber_mod_three (n : ℕ) (hn : 1 ≤ n) : Nat.fermatNumber n % 3 = 2 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 2 * k := ⟨2 ^ (n - 1), by
    rw [show (2 : ℕ) * 2 ^ (n - 1) = 2 ^ (n - 1 + 1) by ring]
    congr 1
    omega⟩
  have h : (2 : ℕ) ^ 2 ^ n % 3 = 1 := by
    rw [hk, pow_mul, show (2 : ℕ) ^ 2 = 3 + 1 by norm_num]
    simpa using Nat.pow_mod (3 + 1) k 3
  simp [Nat.fermatNumber, Nat.add_mod, h]

/-- `3` is a quadratic non-residue modulo a prime Fermat number `Fₙ` with `n ≥ 1`. -/
lemma legendreSym_three_fermatNumber (n : ℕ) (hn : 1 ≤ n)
    (hp : Fact (Nat.Prime (Nat.fermatNumber n))) :
    legendreSym (Nat.fermatNumber n) 3 = -1 := by
  have hrec : legendreSym 3 (Nat.fermatNumber n : ℤ) = legendreSym (Nat.fermatNumber n) (3 : ℤ) :=
    legendreSym.quadratic_reciprocity_one_mod_four (fermatNumber_mod_four n hn) (by norm_num)
  have hmod : (Nat.fermatNumber n : ℤ) % ((3 : ℕ) : ℤ) = 2 := by
    have h := fermatNumber_mod_three n hn
    push_cast
    omega
  rw [← hrec, legendreSym.mod, hmod]
  decide

/-- **Converse of Pépin's test.** If the Fermat number `Fₙ` (`n ≥ 1`) is prime, then it satisfies
the Pépin condition `3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/
theorem pepinCondition_of_prime (n : ℕ) (hn : 1 ≤ n) (hp : Nat.Prime (Nat.fermatNumber n)) :
    PepinCondition n := by
  haveI : Fact (Nat.Prime (Nat.fermatNumber n)) := ⟨hp⟩
  have hhalf : Nat.fermatNumber n / 2 = 2 ^ (2 ^ n - 1) := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h : (2 : ℕ) ^ 2 ^ n = 2 * 2 ^ (2 ^ n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    simp [Nat.fermatNumber, h, Nat.mul_add_div]
  have heuler : ((legendreSym (Nat.fermatNumber n) 3 : ℤ) : ZMod (Nat.fermatNumber n))
      = ((3 : ℤ) : ZMod (Nat.fermatNumber n)) ^ (Nat.fermatNumber n / 2) :=
    legendreSym.eq_pow (Nat.fermatNumber n) 3
  rw [legendreSym_three_fermatNumber n hn ⟨hp⟩, hhalf] at heuler
  unfold PepinCondition
  push_cast at heuler
  exact heuler.symm

/-- **Pépin's test**: for `n ≥ 1`, the Fermat number `Fₙ` is prime if and only if the Pépin
condition holds. -/
theorem prime_fermatNumber_iff_pepinCondition (n : ℕ) (hn : 1 ≤ n) :
    Nat.Prime (Nat.fermatNumber n) ↔ PepinCondition n :=
  ⟨pepinCondition_of_prime n hn, fun h => Nat.pepin_primality n h⟩

/-- **Reduction of the "Fermat prime beyond four" problem.**
There is a Fermat prime `Fₙ` with `n > 4` if and only if some `n > 4` passes Pépin's test.
(Whether either side holds is a famous open problem.) -/
theorem FermatPrimeBeyondFour :
    (∃ n, 4 < n ∧ Nat.Prime (Nat.fermatNumber n)) ↔ (∃ n, 4 < n ∧ PepinCondition n) := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, pepinCondition_of_prime n (by omega) hp⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, Nat.pepin_primality n h⟩

end Brockian.FermatNumbers

