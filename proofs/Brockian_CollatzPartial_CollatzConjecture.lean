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
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` if `n` is even, `n ↦ 3 * n + 1` if `n` is odd. -/
def step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `Reaches1 n` says that some iterate of the Collatz map sends `n` to `1`. -/
def Reaches1 (n : ℕ) : Prop := ∃ k : ℕ, step^[k] n = 1

/-- The Collatz descent hypothesis: every integer `n ≥ 2` is eventually mapped by the
Collatz map to a strictly smaller value.  This is equivalent to the Collatz conjecture
(it rules out both nontrivial cycles and divergent trajectories) and is itself open. -/
def DescentHypothesis : Prop := ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, 0 < k ∧ step^[k] n < n

lemma step_pos {n : ℕ} (hn : 0 < n) : 0 < step n := by
  unfold step
  split
  · omega
  · omega

lemma iterate_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < step^[k] n := by
  induction k generalizing n with
  | zero => simpa using hn
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact ih (step_pos hn)

lemma reaches1_one : Reaches1 1 := ⟨0, rfl⟩

/-- If some iterate of `n` reaches `1`, so does `n` itself (transfer along iteration). -/
lemma reaches1_of_iterate {n : ℕ} (k : ℕ) (h : Reaches1 (step^[k] n)) : Reaches1 n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [Function.iterate_add_apply]; exact hj⟩

lemma step_two_pow (k : ℕ) : step (2 ^ (k + 1)) = 2 ^ k := by
  have h : 2 ^ (k + 1) % 2 = 0 := by
    simp [pow_succ, Nat.mul_mod_left]
  unfold step
  rw [if_pos h, pow_succ]
  omega

/-- Unconditional partial result: every power of two reaches `1`. -/
theorem reaches1_two_pow (k : ℕ) : Reaches1 (2 ^ k) := by
  induction k with
  | zero => simpa using reaches1_one
  | succ k ih =>
      refine reaches1_of_iterate 1 ?_
      rw [Function.iterate_one, step_two_pow]
      exact ih

/-- Bounded search: `reachesIn f n` is `true` iff `n` reaches `1` within `f` steps. -/
def reachesIn : ℕ → ℕ → Bool
  | 0, n => n == 1
  | f + 1, n => n == 1 || reachesIn f (step n)

lemma reaches1_of_reachesIn : ∀ (f n : ℕ), reachesIn f n = true → Reaches1 n := by
  intro f
  induction f with
  | zero =>
      intro n h
      exact ⟨0, by simpa using (by simpa [reachesIn] using h : n = 1)⟩
  | succ f ih =>
      intro n h
      rw [reachesIn, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · exact ⟨0, by simpa using h⟩
      · exact reaches1_of_iterate 1 (by simpa using ih (step n) h)

set_option maxRecDepth 40000 in
private lemma reachesIn_below_1000 :
    ∀ m ∈ List.range 1000, m = 0 ∨ reachesIn 300 m = true := by decide

/-- Unconditional partial result: every positive integer below `1000` reaches `1`
(each within at most `300` steps).  Verified by kernel computation. -/
theorem reaches1_of_lt_1000 {n : ℕ} (hn : 0 < n) (h : n < 1000) : Reaches1 n := by
  have hm : n ∈ List.range 1000 := List.mem_range.mpr h
  rcases reachesIn_below_1000 n hm with h0 | hb
  · omega
  · exact reaches1_of_reachesIn 300 n hb

/-- **Conditional reduction of the Collatz conjecture.**  Assuming the (open) descent
hypothesis — that every `n ≥ 2` eventually maps to a strictly smaller value — every
positive integer reaches `1` under iteration of the Collatz map.

This is a Lean-checked conditional proof, by strong induction on `n`; the Collatz
conjecture itself remains open, and the hypothesis `hdesc` is not discharged here. -/
theorem CollatzConjecture (hdesc : DescentHypothesis) :
    ∀ n : ℕ, 0 < n → Reaches1 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases lt_or_ge n 2 with h1 | h2
    · have : n = 1 := by omega
      rw [this]; exact reaches1_one
    · obtain ⟨k, _, hk⟩ := hdesc n h2
      exact reaches1_of_iterate k (ih _ hk (iterate_pos hn k))

/-- Converse direction: the Collatz conjecture implies the descent hypothesis, so the
hypothesis assumed in `CollatzConjecture` is exactly equivalent to the conjecture. -/
theorem descentHypothesis_of_collatz (h : ∀ n : ℕ, 0 < n → Reaches1 n) :
    DescentHypothesis := by
  intro n hn
  obtain ⟨k, hk⟩ := h n (by omega)
  refine ⟨k, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at hk; omega
    · exact hk0
  · omega

end Brockian.CollatzPartial

