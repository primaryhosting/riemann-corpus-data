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

set_option grind.warning false
set_option linter.dupNamespace false

/-!
# Gilbreath's Conjecture — Conditional Reduction

CONDITIONAL: Gilbreath's conjecture assuming the Odlyzko "clean window" hypothesis (that for
every `N ≥ 1` some row of index `k ≤ N` begins with `1` followed by `N` entries all equal to
`0` or `2`).

This module packages the AXLE-verified reduction theorem
`Brockian.GilbreathConjectureReduction.GilbreathConjecture`, a genuine proven implication
`OdlyzkoHypothesis → GilbreathStatement`. `OdlyzkoHypothesis` is a separate, open hypothesis;
the conclusion is not proved unconditionally.
-/

namespace Brockian.GilbreathConjectureReduction

/-- The rows of Gilbreath's triangle: `gRow 0` enumerates the primes and
`gRow (k+1) n = |gRow k (n+1) - gRow k n|`. -/
noncomputable def gRow : ℕ → ℕ → ℕ
  | 0, n => Nat.nth Nat.Prime n
  | k + 1, n => Nat.dist (gRow k (n + 1)) (gRow k n)

/-- **Gilbreath's conjecture**: every row of index `k ≥ 1` of Gilbreath's triangle starts with `1`. -/
def GilbreathStatement : Prop := ∀ k, 1 ≤ k → gRow k 0 = 1

/-- Row `k` begins with `1` and its next `N` entries all lie in `{0, 2}`. -/
def CleanWindow (k N : ℕ) : Prop :=
  gRow k 0 = 1 ∧ ∀ i, 1 ≤ i → i ≤ N → gRow k i = 0 ∨ gRow k i = 2

/-- The hypothesis used by Odlyzko's verification method: for every `N ≥ 1` there is a row of
index `k` with `1 ≤ k ≤ N` which begins with `1` and whose next `N` entries are all `0` or `2`. -/
def OdlyzkoHypothesis : Prop := ∀ N, 1 ≤ N → ∃ k, 1 ≤ k ∧ k ≤ N ∧ CleanWindow k N

/-- A clean window propagates to the next row, with the window shortened by one. -/
lemma cleanWindow_succ {k N : ℕ} (h : CleanWindow k (N + 1)) : CleanWindow (k + 1) N := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, ?_⟩
  · have h2 := h1 1 le_rfl (by omega)
    show Nat.dist (gRow k 1) (gRow k 0) = 1
    rcases h2 with h | h <;> rw [h, h0] <;> decide
  · intro i hi hiN
    show Nat.dist (gRow k (i + 1)) (gRow k i) = 0 ∨ Nat.dist (gRow k (i + 1)) (gRow k i) = 2
    rcases h1 (i + 1) (by omega) (by omega) with h | h <;>
      rcases h1 i hi (by omega) with h' | h' <;> rw [h, h'] <;> decide

/-- A clean window of width `N` at row `k` forces the next `N` rows to begin with `1`. -/
lemma head_of_cleanWindow {k N : ℕ} (h : CleanWindow k N) : ∀ j, j ≤ N → gRow (k + j) 0 = 1 := by
  induction N generalizing k with
  | zero => intro j hj; interval_cases j; exact h.1
  | succ N ih =>
      intro j hj
      match j with
      | 0 => exact h.1
      | (j + 1) =>
        have e : k + (j + 1) = (k + 1) + j := by omega
        rw [e]
        exact ih (cleanWindow_succ h) j (by omega)

/-- **Conditional Gilbreath conjecture.** Under `OdlyzkoHypothesis` — for every `N ≥ 1` some row
of index `k ≤ N` begins with `1` followed by `N` entries all equal to `0` or `2` — every row of
Gilbreath's triangle of index `k ≥ 1` begins with `1`. -/
theorem GilbreathConjecture (H : OdlyzkoHypothesis) : GilbreathStatement := by
  intro m hm
  obtain ⟨k, hk1, hkm, hw⟩ := H m hm
  have h := head_of_cleanWindow hw (m - k) (by omega)
  rwa [show k + (m - k) = m from by omega] at h

end Brockian.GilbreathConjectureReduction
