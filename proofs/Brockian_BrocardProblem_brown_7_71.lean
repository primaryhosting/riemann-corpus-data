/-
  Brocard's problem: for which n is n! + 1 a perfect square?

  A pair (n, m) with n! + 1 = m² is called a Brown number. Only THREE are known:
  (4, 5), (5, 11), (7, 71). It is OPEN whether any others exist (conjectured none).

  This file:
    (1) verifies the three known Brown pairs (flagship),
    (2) proves structural necessary conditions every Brown pair must satisfy,
    (3) narrows the finite search: n! + 1 is not a square for n ∈ {8, 9, 10},
  and records Brocard's conjecture as an UNPROVEN `def`. We do NOT resolve it.

  HONEST: `BrocardConjecture` is an open problem. Nothing here claims to prove it.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.BrocardProblem

/-- A Brown number pair: `n! + 1 = m²`. -/
def BrownPair (n m : ℕ) : Prop := Nat.factorial n + 1 = m ^ 2

/-- Brocard's conjecture (OPEN): the only Brown pairs have `n ∈ {4, 5, 7}`.
    Recorded as an UNPROVEN `def` — this file never asserts or discharges it. -/
def BrocardConjecture : Prop := ∀ n m : ℕ, BrownPair n m → n = 4 ∨ n = 5 ∨ n = 7

/-! ## (1) The three known Brown pairs -/

/-- `4! + 1 = 25 = 5²`. -/
theorem brown_4_5 : BrownPair 4 5 := by unfold BrownPair; decide

/-- `5! + 1 = 121 = 11²`. -/
theorem brown_5_11 : BrownPair 5 11 := by unfold BrownPair; decide

/-- `7! + 1 = 5041 = 71²`. -/
theorem brown_7_71 : BrownPair 7 71 := by unfold BrownPair; decide

/-! ## (2) Structural necessary conditions -/

/-- In any Brown pair with `n ≥ 2`, the root `m` is odd: `n!` is even, so
    `m² = n! + 1` is odd, whence `m` is odd. -/
theorem brown_m_odd {n m : ℕ} (hn : 2 ≤ n) (h : BrownPair n m) : Odd m := by
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (by norm_num) hn
  have hfe : Even (Nat.factorial n) := ⟨k, by rw [hk]; ring⟩
  have hsq : Odd (m ^ 2) := by
    rw [← h]; exact hfe.add_one
  rw [pow_two] at hsq
  exact (Nat.odd_mul.mp hsq).1

/-- The factorial factorizes across a Brown pair: `n! = (m - 1)(m + 1)`
    (a difference of squares, since `n! = m² - 1`). -/
theorem brown_factorization {n m : ℕ} (h : BrownPair n m) :
    Nat.factorial n = (m - 1) * (m + 1) := by
  have hpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · exfalso
      have hz : Nat.factorial n + 1 = 0 := by simpa [BrownPair] using h
      omega
    · exact h0
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, (Nat.sub_add_cancel hpos).symm⟩
  simp only [BrownPair] at h
  simp only [Nat.add_sub_cancel]
  have hexp : (d + 1) ^ 2 = d * (d + 1 + 1) + 1 := by ring
  omega

/-! ## (3) Finite search narrowing (stretch) -/

/-- If `a² < N < (a+1)²` then `N` is strictly between consecutive squares, so `N`
    is not a perfect square. A reusable no-square-in-a-gap lemma. -/
private theorem not_square_between (a : ℕ) {N : ℕ}
    (hlo : a ^ 2 < N) (hhi : N < (a + 1) ^ 2) : ¬ ∃ m, N = m ^ 2 := by
  rintro ⟨m, rfl⟩
  have ha : a < m := by
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_left hc 2
    omega
  have hb : m < a + 1 := by
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_left hc 2
    omega
  omega

/-- `n! + 1` is not a perfect square for `n ∈ {8, 9, 10}`, since in each case it
    falls strictly between two consecutive squares:
    `200² < 40321 < 201²`, `602² < 362881 < 603²`, `1904² < 3628801 < 1905²`. -/
theorem no_brown_8_9_10 :
    (¬ ∃ m, BrownPair 8 m) ∧ (¬ ∃ m, BrownPair 9 m) ∧ (¬ ∃ m, BrownPair 10 m) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨m, hm⟩ := h
    have hm2 : Nat.factorial 8 + 1 = m ^ 2 := hm
    norm_num [Nat.factorial] at hm2
    have key : ∃ m', (40321 : ℕ) = m' ^ 2 := ⟨m, by omega⟩
    exact not_square_between 200 (by norm_num) (by norm_num) key
  · obtain ⟨m, hm⟩ := h
    have hm2 : Nat.factorial 9 + 1 = m ^ 2 := hm
    norm_num [Nat.factorial] at hm2
    have key : ∃ m', (362881 : ℕ) = m' ^ 2 := ⟨m, by omega⟩
    exact not_square_between 602 (by norm_num) (by norm_num) key
  · obtain ⟨m, hm⟩ := h
    have hm2 : Nat.factorial 10 + 1 = m ^ 2 := hm
    norm_num [Nat.factorial] at hm2
    have key : ∃ m', (3628801 : ℕ) = m' ^ 2 := ⟨m, by omega⟩
    exact not_square_between 1904 (by norm_num) (by norm_num) key

end Brockian.BrocardProblem
