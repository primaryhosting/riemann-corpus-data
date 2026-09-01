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
# Bonferroni / truncated inclusion-exclusion

The combinatorial heart of Brun's pure sieve: truncating the alternating sum over subsets
at an even level gives an upper bound for the indicator of the empty set.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/
lemma alt_choose_partial (r : ℕ) : ∀ k : ℕ,
    ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ((r + 1).choose j) = (-1) ^ k * (r.choose k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ r k]
    push_cast
    ring

lemma alt_choose_zero (k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (((0:ℕ)).choose j) = 1 := by
  have : ∀ j ∈ range (k + 1), (-1 : ℝ) ^ j * (((0:ℕ)).choose j) = if j = 0 then 1 else 0 := by
    intro j _
    rcases Nat.eq_zero_or_pos j with h | h
    · simp [h]
    · rw [Nat.choose_eq_zero_of_lt h]
      simp [Nat.ne_of_gt h]
  rw [Finset.sum_congr rfl this]
  simp

lemma alt_choose_nonneg (r k : ℕ) (hk : Even k) :
    (0 : ℝ) ≤ ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (r.choose j) := by
  cases r with
  | zero => rw [alt_choose_zero]; norm_num
  | succ r =>
    rw [alt_choose_partial r k, hk.neg_one_pow]
    positivity

lemma sum_powerset_card_le {α : Type*} [DecidableEq α] (S : Finset α) (k : ℕ) :
    ∑ T ∈ S.powerset with #T ≤ k, (-1 : ℝ) ^ (#T)
      = ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ((#S).choose j) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun T => #T) (t := range (k + 1))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hset : {T ∈ ({T ∈ S.powerset | #T ≤ k}) | #T = j} = S.powersetCard j := by
      ext T
      simp only [mem_filter, mem_powerset, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_⟩, h2⟩
        have : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
        omega
    rw [hset, Finset.sum_congr rfl (fun T hT => by
        rw [(Finset.mem_powersetCard.mp hT).2]), Finset.sum_const,
      Finset.card_powersetCard]
    simp [mul_comm]
  · intro T hT
    simp only [mem_filter, mem_powerset] at hT
    simp only [Finset.mem_range]
    omega

/-- **Bonferroni inequality**: for even `k`, the truncated alternating sum over subsets of `S`
of size at most `k` is at least the indicator that `S` is empty. -/
lemma bonferroni {α : Type*} [DecidableEq α] (S : Finset α) (k : ℕ) (hk : Even k) :
    (if S = ∅ then (1 : ℝ) else 0) ≤ ∑ T ∈ S.powerset with #T ≤ k, (-1 : ℝ) ^ (#T) := by
  rw [sum_powerset_card_le]
  by_cases h : S = ∅
  · subst h
    simp only [Finset.card_empty]
    rw [alt_choose_zero]
    norm_num
  · rw [if_neg h]
    exact alt_choose_nonneg _ k hk

end Brun

