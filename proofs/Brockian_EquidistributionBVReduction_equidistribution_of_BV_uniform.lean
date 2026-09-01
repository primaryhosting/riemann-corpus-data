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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Set MeasureTheory Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The monotone step function `t ↦ 𝟙[c ≤ t]`, a function of bounded variation which is used as
a test function to extract equidistribution from convergence of averages along BV functions. -/
noncomputable def stepGe (c : ℝ) : ℝ → ℝ := fun t => if c ≤ t then 1 else 0

lemma monotoneOn_stepGe (c : ℝ) (s : Set ℝ) : MonotoneOn (stepGe c) s := by
  intro p _ q _ hpq
  simp only [stepGe]
  split <;> split <;> simp_all; linarith

/-- The step function `stepGe c` has bounded variation on `[0, 1]`. -/
lemma boundedVariationOn_stepGe (c : ℝ) : BoundedVariationOn (stepGe c) (Icc 0 1) := by
  have h := (monotoneOn_stepGe c (Icc (0:ℝ) 1)).eVariationOn_le (a := 0) (b := 1)
    (by norm_num) (by norm_num)
  rw [Set.inter_self] at h
  exact ne_top_of_le_ne_top (by simp) h

lemma intervalIntegrable_stepGe (c a b : ℝ) :
    IntervalIntegrable (stepGe c) volume a b :=
  (monotoneOn_stepGe c (uIcc a b)).intervalIntegrable

/-- The integral of the step function over `[0, 1]` is `1 - c`, for `c ∈ [0, 1]`. -/
lemma integral_stepGe {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) :
    (∫ t in (0:ℝ)..1, stepGe c t) = 1 - c := by
  obtain ⟨h0, h1⟩ := hc
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := c)
    (intervalIntegrable_stepGe c 0 c) (intervalIntegrable_stepGe c c 1)]
  have e1 : (∫ t in (0:ℝ)..c, stepGe c t) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ)) ?_]
    · simp
    · have hne : ∀ᵐ x : ℝ, x ≠ c := by simp [ae_iff]
      filter_upwards [hne] with y hy hymem
      rcases le_or_gt c y with h | h
      · rw [Set.uIoc_of_le h0] at hymem
        exact absurd (le_antisymm hymem.2 h) hy
      · simp [stepGe, not_le.mpr h]
  have e2 : (∫ t in c..(1:ℝ), stepGe c t) = 1 - c := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) ?_]
    · simp
    · intro y hy
      rw [Set.uIcc_of_le h1] at hy
      simp [stepGe, hy.1]
  rw [e1, e2, zero_add]

/-- Counting the points of a sequence lying in `[c, 1]` as a sum of step-function values. -/
lemma sum_stepGe_eq_card (x : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, stepGe c (x n))
      = (({n ∈ Finset.range N | c ≤ x n}).card : ℝ) := by
  simp [stepGe]

lemma card_lt_add_card_le (x : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    ({n ∈ Finset.range N | x n < c}).card + ({n ∈ Finset.range N | c ≤ x n}).card = N := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.range N) (p := fun n => x n < c)
  simp only [not_lt, Finset.card_range] at h
  exact h

/-- **Equidistribution from convergence of averages along functions of bounded variation.**

If, for every real-valued function `f` of bounded variation on `[0, 1]`, the Cesàro averages
`(1/N) ∑_{n < N} f (x n)` converge to `∫₀¹ f`, then the sequence `x` is equidistributed:
for every `c ∈ [0, 1]` the proportion of indices `n < N` with `x n < c` converges to `c`.

This is the reduction step of the classical BV (Koksma) criterion for uniform distribution;
the hypothesis is applied to the bounded-variation test functions `t ↦ 𝟙[c ≤ t]`. -/
theorem equidistribution_of_BV_uniform (x : ℕ → ℝ)
    (hBV : ∀ f : ℝ → ℝ, BoundedVariationOn f (Icc 0 1) →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / (N : ℝ)) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f t)))
    {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) :
    Tendsto (fun N : ℕ => ((({n ∈ Finset.range N | x n < c}).card : ℝ)) / (N : ℝ)) atTop (𝓝 c) := by
  have hstep := hBV (stepGe c) (boundedVariationOn_stepGe c)
  rw [integral_stepGe hc] at hstep
  simp only [sum_stepGe_eq_card x c] at hstep
  have hmain : Tendsto
      (fun N : ℕ => 1 - ((({n ∈ Finset.range N | c ≤ x n}).card : ℝ)) / (N : ℝ)) atTop
      (𝓝 (1 - (1 - c))) := (tendsto_const_nhds (x := (1:ℝ))).sub hstep
  rw [sub_sub_cancel] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcard : ((({n ∈ Finset.range N | x n < c}).card : ℝ))
      + ((({n ∈ Finset.range N | c ≤ x n}).card : ℝ)) = (N : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (card_lt_add_card_le x c N)
  field_simp
  linarith

end Brockian.EquidistributionBVReduction

