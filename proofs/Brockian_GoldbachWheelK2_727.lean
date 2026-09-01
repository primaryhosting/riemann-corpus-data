/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
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

namespace Brockian

/-- A trial-division primality test, valid for `n ≤ 727` (since `27 * 27 = 729 > 727`,
it suffices to rule out divisors `d` with `2 ≤ d < 27`). -/
def wheelPrimeTest (n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    (List.range 27).all (fun d => decide (d < 2) || decide (d = n) || decide (¬ (d ∣ n)))

/-- A search for a Goldbach partition of `n` using a first summand below `100`. -/
def wheelGoldbachTest (n : ℕ) : Bool :=
  (List.range 100).any (fun p => wheelPrimeTest p && wheelPrimeTest (n - p))

theorem wheelPrimeTest_sound {n : ℕ} (hn : n ≤ 727) (h : wheelPrimeTest n = true) :
    Nat.Prime n := by
  rw [wheelPrimeTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h2, hd⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, ?_⟩
  intro m hm hms hmd
  have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
  have hm27 : m < 27 := by nlinarith
  have := hd m (List.mem_range.mpr hm27)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with (h1 | h1) | h1
  · omega
  · subst h1
    -- `m = n` would force `n ≤ Nat.sqrt n`, impossible for `2 ≤ n`
    have : Nat.sqrt m < m := Nat.sqrt_lt_self (by omega)
    omega
  · exact h1 hmd

theorem wheelGoldbachTest_sound {n : ℕ} (hn : n ≤ 727) (h : wheelGoldbachTest n = true) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  rw [wheelGoldbachTest, List.any_eq_true] at h
  obtain ⟨p, hp, hpq⟩ := h
  rw [Bool.and_eq_true] at hpq
  obtain ⟨hp1, hp2⟩ := hpq
  have hple : p < 100 := List.mem_range.mp hp
  have hq2 : 2 ≤ n - p := by
    have := hp2
    rw [wheelPrimeTest, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  refine ⟨p, n - p, wheelPrimeTest_sound (by omega) hp1,
    wheelPrimeTest_sound (by omega) hp2, by omega⟩

/-- **Goldbach wheel, K = 2, modulus 727.**  Every even number `n` with `4 ≤ n ≤ 727`
is a sum of two primes. -/
theorem GoldbachWheelK2_727 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 727 → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  have key : (List.range 728).all
      (fun n => !(decide (4 ≤ n) && decide (n % 2 = 0)) || wheelGoldbachTest n) = true := by
    decide
  rw [List.all_eq_true] at key
  intro n h4 h727 hev
  have hmem : n ∈ List.range 728 := List.mem_range.mpr (by omega)
  have h := key n hmem
  have hpar : n % 2 = 0 := Nat.even_iff.mp hev
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq,
    decide_eq_false_iff_not, hpar, h4, not_true_eq_false, false_and, false_or] at h
  exact wheelGoldbachTest_sound h727 h

end Brockian

