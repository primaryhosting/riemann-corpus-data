import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- `IsGoldbachK2 n` : `n` is a sum of `K = 2` primes. -/
def IsGoldbachK2 (n : ℕ) : Prop := ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- The wheel-spoke core of the verification, in the equivalent bounded/decidable form:
for every even `n` in the window `[4, 631]` there is a prime `p < 48` (a spoke of the
wheel) with `n - p` prime. -/
theorem goldbachWheelK2_631_decidable_core :
    ∀ n ∈ Finset.range 632, 4 ≤ n → n % 2 = 0 →
      ∃ p ∈ Finset.range 48, Nat.Prime p ∧ Nat.Prime (n - p) ∧ p + (n - p) = n := by
  decide

/-- **Goldbach wheel, `K = 2`, modulus `631`.**
Every even natural number `n` with `4 ≤ n ≤ 631` is a sum of two primes; moreover a witness
can always be taken with the smaller prime below `48`. -/
theorem GoldbachWheelK2_631 :
    ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 631 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ 47 ∧ p + q = n := by
  intro n hn h4 h631
  obtain ⟨p, hp, hp1, hp2, hp3⟩ :=
    goldbachWheelK2_631_decidable_core n (Finset.mem_range.mpr (by omega)) h4
      (Nat.even_iff.mp hn)
  have hp' : p < 48 := Finset.mem_range.mp hp
  exact ⟨p, n - p, hp1, hp2, by omega, hp3⟩

/-- The same statement in the language of `IsGoldbachK2`. -/
theorem isGoldbachK2_of_even_le_631 (n : ℕ) (hn : Even n) (h4 : 4 ≤ n) (h631 : n ≤ 631) :
    IsGoldbachK2 n := by
  obtain ⟨p, q, hp, hq, _, hpq⟩ := GoldbachWheelK2_631 n hn h4 h631
  exact ⟨p, q, hp, hq, hpq⟩

/-- Contrapositive form: there is no counterexample to Goldbach's conjecture in the
window `[4, 631]`. -/
theorem no_goldbachK2_counterexample_le_631 :
    ¬ ∃ n : ℕ, Even n ∧ 4 ≤ n ∧ n ≤ 631 ∧ ¬ IsGoldbachK2 n := by
  rintro ⟨n, hn, h4, h631, hbad⟩
  exact hbad (isGoldbachK2_of_even_le_631 n hn h4 h631)

end Brockian

