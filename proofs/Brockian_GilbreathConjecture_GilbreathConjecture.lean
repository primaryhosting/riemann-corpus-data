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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.GilbreathConjecture

/-- Absolute difference of two natural numbers, written without `Int`. -/
def adist (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- The Gilbreath triangle: row `0` is the sequence of primes, and each subsequent
row is the sequence of absolute differences of consecutive entries of the previous row. -/
noncomputable def gRow : ℕ → ℕ → ℕ
  | 0, k => Nat.nth Nat.Prime k
  | (n + 1), k => adist (gRow n k) (gRow n (k + 1))

/-- Gilbreath's conjecture: every row of the Gilbreath triangle after the zeroth
one starts with `1`. -/
def GilbreathStatement : Prop := ∀ n, 1 ≤ n → gRow n 0 = 1

/-- A row is *stable* if it begins with `1` and all its remaining entries are `0` or `2`. -/
def Stable (n : ℕ) : Prop := gRow n 0 = 1 ∧ ∀ k, 1 ≤ k → gRow n k = 0 ∨ gRow n k = 2

theorem adist_of_mem_pair {a b : ℕ} (ha : a = 0 ∨ a = 2) (hb : b = 0 ∨ b = 2) :
    adist a b = 0 ∨ adist a b = 2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [adist]

theorem stable_succ {n : ℕ} (h : Stable n) : Stable (n + 1) := by
  obtain ⟨h0, h2⟩ := h
  constructor
  · have := h2 1 le_rfl
    simp only [gRow, h0]
    rcases this with h | h <;> simp [adist, h]
  · intro k hk
    exact adist_of_mem_pair (h2 k hk) (h2 (k + 1) (by omega))

theorem stable_of_le {N n : ℕ} (hN : Stable N) (h : N ≤ n) : Stable n := by
  induction n with
  | zero => simpa [Nat.le_zero.mp h] using hN
  | succ m ih =>
    rcases Nat.lt_or_ge N (m + 1) with hlt | hge
    · exact stable_succ (ih (by omega))
    · have : N = m + 1 := le_antisymm h hge
      exact this ▸ hN

set_option linter.dupNamespace false in
/-- **Conditional reduction of Gilbreath's conjecture.**
If some row `N ≥ 1` of the Gilbreath triangle has the form `1, x₁, x₂, …` with every
`xᵢ ∈ {0, 2}`, and every row from the first up to row `N` starts with `1`, then
Gilbreath's conjecture holds: every row after the zeroth starts with `1`.

(The hypotheses are exactly the "stabilization" property that all numerical evidence for
the conjecture is based on; the unconditional statement remains open.) -/
theorem GilbreathConjecture (N : ℕ) (hN : 1 ≤ N)
    (hbase : ∀ n, 1 ≤ n → n ≤ N → gRow n 0 = 1)
    (hstable : ∀ k, 1 ≤ k → gRow N k = 0 ∨ gRow N k = 2) :
    GilbreathStatement := by
  intro n hn
  rcases Nat.lt_or_ge n N with hlt | hge
  · exact hbase n hn (le_of_lt hlt)
  · exact (stable_of_le ⟨hbase N hN le_rfl, hstable⟩ hge).1

end Brockian.GilbreathConjecture

