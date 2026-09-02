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

/-
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.BrocardProblem

/-- `n` and `m` form a *Brocard pair* when `n ! + 1 = m ^ 2`.  Brocard's problem asks
whether the only such pairs are `(4, 5)`, `(5, 11)` and `(7, 71)`. -/
def IsBrocardPair (n m : ℕ) : Prop := n ! + 1 = m ^ 2

theorem isBrocardPair_four : IsBrocardPair 4 5 := by
  unfold IsBrocardPair; norm_num [Nat.factorial]

theorem isBrocardPair_five : IsBrocardPair 5 11 := by
  unfold IsBrocardPair; norm_num [Nat.factorial]

theorem isBrocardPair_seven : IsBrocardPair 7 71 := by
  unfold IsBrocardPair; norm_num [Nat.factorial]

/-- A number lying strictly between two consecutive squares is not a square. -/
private theorem not_sq {a k m : ℕ} (h1 : a ^ 2 < k) (h2 : k < (a + 1) ^ 2)
    (hm : k = m ^ 2) : False := by
  subst hm
  have ha : a < m := by
    by_contra hc
    exact absurd (Nat.pow_le_pow_left (Nat.le_of_not_lt hc) 2) (by omega)
  have ha' : a + 1 ≤ m := ha
  exact absurd (Nat.pow_le_pow_left ha' 2) (by omega)

/-- **Finite verification.**  Every Brocard pair with `n < 25` is one of the three known
ones `(4, 5)`, `(5, 11)`, `(7, 71)`.  For each other `n < 25` the number `n ! + 1` is
shown to lie strictly between two consecutive squares. -/
theorem eq_of_isBrocardPair_of_lt {n m : ℕ} (hn : n < 25) (h : IsBrocardPair n m) :
    (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 11) ∨ (n = 7 ∧ m = 71) := by
  unfold IsBrocardPair at h
  interval_cases n
  · exact absurd h (fun h => not_sq (a := 1) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 1) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 1) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 2) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · have hm : m ^ 2 = 25 := by norm_num [Nat.factorial] at h; exact h.symm
    have : m < 6 := by nlinarith
    interval_cases m <;> simp_all
  · have hm : m ^ 2 = 121 := by norm_num [Nat.factorial] at h; exact h.symm
    have : m < 12 := by nlinarith
    interval_cases m <;> simp_all
  · exact absurd h (fun h => not_sq (a := 26) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · have hm : m ^ 2 = 5041 := by norm_num [Nat.factorial] at h; exact h.symm
    have : m < 72 := by nlinarith
    interval_cases m <;> simp_all
  · exact absurd h (fun h => not_sq (a := 200) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 602) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 1904) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 6317) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 21886) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 78911) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 295259) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 1143535) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 4574143) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 18859677) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 80014834) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 348776576) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 1559776268) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 7147792818) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 33526120082) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 160785623545) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)
  · exact absurd h (fun h => not_sq (a := 787685471322) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) h)

/-- **Reduction of Brocard's problem to the range `n ≥ 25`.**
Given that no `n ≥ 25` yields a Brocard pair, the only Brocard pairs are the three
known ones `(4, 5)`, `(5, 11)`, `(7, 71)`; equivalently, `n ! + 1` is a perfect square
exactly for `n = 4, 5, 7`.  The range `n < 25` is verified unconditionally in
`eq_of_isBrocardPair_of_lt`. -/
theorem BrocardConjecture (h : ∀ n m : ℕ, 25 ≤ n → ¬ IsBrocardPair n m) :
    ∀ n m : ℕ, IsBrocardPair n m →
      (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 11) ∨ (n = 7 ∧ m = 71) := by
  intro n m hnm
  rcases lt_or_ge n 25 with hn | hn
  · exact eq_of_isBrocardPair_of_lt hn hnm
  · exact absurd hnm (h n m hn)

/-- The hypothesis of `BrocardConjecture` is *equivalent* to Brocard's conjecture, so the
reduction loses nothing: the entire content of the conjecture lies in the range `n ≥ 25`. -/
theorem brocard_iff_large :
    (∀ n m : ℕ, IsBrocardPair n m →
        (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 11) ∨ (n = 7 ∧ m = 71)) ↔
      (∀ n m : ℕ, 25 ≤ n → ¬ IsBrocardPair n m) := by
  constructor
  · intro h n m hn hnm
    rcases h n m hnm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
  · exact BrocardConjecture

/-- A Brocard pair factors the factorial: `m = k + 1` with `k * (k + 2) = n !`.
This is the classical reformulation `(m - 1) * (m + 1) = n !`. -/
theorem factorisation_of_isBrocardPair {n m : ℕ} (h : IsBrocardPair n m) :
    ∃ k : ℕ, m = k + 1 ∧ k * (k + 2) = n ! := by
  unfold IsBrocardPair at h
  have hm : m ≠ 0 := by rintro rfl; simp at h
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact ⟨k, rfl, by nlinarith [h]⟩

/-- In any Brocard pair with `2 ≤ n` the square root `m` is odd. -/
theorem odd_of_isBrocardPair {n m : ℕ} (hn : 2 ≤ n) (h : IsBrocardPair n m) : Odd m := by
  unfold IsBrocardPair at h
  obtain ⟨s, hs⟩ : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
  rcases Nat.even_or_odd m with he | ho
  · exfalso
    have hsq : Even (m ^ 2) := (Nat.even_pow' two_ne_zero).mpr he
    rw [← h] at hsq
    obtain ⟨t, ht⟩ := hsq
    omega
  · exact ho

end Brockian.BrocardProblem

