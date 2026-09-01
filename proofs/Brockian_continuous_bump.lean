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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian
namespace Equidistribution

/-- A continuous trapezoidal "bump": it is `0` outside `[c, d]`, `1` on `[c + ε, d - ε]`, and
takes values in `[0,1]` everywhere. -/
noncomputable def bump (c d ε t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t - c) / ε) ((d - t) / ε)))

lemma continuous_bump (c d ε : ℝ) : Continuous (bump c d ε) := by
  unfold bump
  fun_prop

lemma bump_nonneg (c d ε t : ℝ) : 0 ≤ bump c d ε t := le_max_left _ _

lemma bump_le_one {c d ε : ℝ} (t : ℝ) : bump c d ε t ≤ 1 := by
  unfold bump
  apply max_le (by norm_num)
  exact min_le_left _ _

lemma bump_eq_zero_of_le {c d ε t : ℝ} (hε : 0 < ε) (ht : t ≤ c) : bump c d ε t = 0 := by
  unfold bump
  have h1 : (t - c) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  have h2 : min 1 (min ((t - c) / ε) ((d - t) / ε)) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h1)
  exact max_eq_left h2

lemma bump_eq_zero_of_ge {c d ε t : ℝ} (hε : 0 < ε) (ht : d ≤ t) : bump c d ε t = 0 := by
  unfold bump
  have h1 : (d - t) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  have h2 : min 1 (min ((t - c) / ε) ((d - t) / ε)) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h1)
  exact max_eq_left h2

lemma bump_eq_one {c d ε t : ℝ} (hε : 0 < ε) (h1 : c + ε ≤ t) (h2 : t ≤ d - ε) :
    bump c d ε t = 1 := by
  unfold bump
  have hA : (1:ℝ) ≤ (t - c) / ε := by
    rw [le_div_iff₀ hε]; linarith
  have hB : (1:ℝ) ≤ (d - t) / ε := by
    rw [le_div_iff₀ hε]; linarith
  have : min 1 (min ((t - c) / ε) ((d - t) / ε)) = 1 :=
    min_eq_left (le_min hA hB)
  rw [this]
  exact max_eq_right (by norm_num)

/-- The lower bump is below the indicator of `[a, b)`. -/
lemma bump_le_indicator {a b ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    bump a b ε t ≤ (if t ∈ Set.Ico a b then (1:ℝ) else 0) := by
  by_cases ht : t ∈ Set.Ico a b
  · simp only [ht, if_true]
    exact bump_le_one t
  · simp only [ht, if_false]
    rcases lt_or_ge t a with h | h
    · exact le_of_eq (bump_eq_zero_of_le hε h.le)
    · have hb : b ≤ t := by
        by_contra hcon
        exact ht ⟨h, lt_of_not_ge hcon⟩
      exact le_of_eq (bump_eq_zero_of_ge hε hb)

/-- The indicator of `[a, b)` is below the widened bump. -/
lemma indicator_le_bump {a b ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (if t ∈ Set.Ico a b then (1:ℝ) else 0) ≤ bump (a - ε) (b + ε) ε t := by
  by_cases ht : t ∈ Set.Ico a b
  · simp only [ht, if_true]
    rw [bump_eq_one hε (by simp; linarith [ht.1]) (by simp; linarith [ht.2.le])]
  · simp only [ht, if_false]
    exact bump_nonneg _ _ _ _

lemma integral_bump_le {c d ε : ℝ} (hε : 0 < ε) (hcd : c ≤ d) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) :
    (∫ t in (0:ℝ)..1, bump c d ε t) ≤ d - c := by
  set g : ℝ → ℝ := bump c d ε with hg
  have hcont : Continuous g := continuous_bump c d ε
  set c' : ℝ := max 0 c with hc'
  set d' : ℝ := min 1 d with hd'
  have h0c' : (0:ℝ) ≤ c' := le_max_left _ _
  have hc'1 : c' ≤ 1 := max_le (by norm_num) hc1
  have hd'1 : d' ≤ 1 := min_le_left _ _
  have h0d' : (0:ℝ) ≤ d' := le_min (by norm_num) hd0
  have hc'd' : c' ≤ d' := by
    apply max_le
    · exact h0d'
    · exact le_min hc1 hcd
  have hsplit1 : (∫ t in (0:ℝ)..c', g t) + (∫ t in c'..1, g t) = ∫ t in (0:ℝ)..1, g t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hsplit2 : (∫ t in c'..d', g t) + (∫ t in d'..(1:ℝ), g t) = ∫ t in c'..1, g t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hfirst : (∫ t in (0:ℝ)..c', g t) = 0 := by
    rcases le_or_gt c 0 with h | h
    · have : c' = 0 := by simp [hc', max_eq_left h]
      rw [this]
      simp
    · have hc'c : c' = c := max_eq_right h.le
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le h0c'] at ht
        exact bump_eq_zero_of_le hε (by rw [← hc'c]; exact ht.2)
  have hlast : (∫ t in d'..(1:ℝ), g t) = 0 := by
    rcases le_or_gt 1 d with h | h
    · have : d' = 1 := by simp [hd', min_eq_left h]
      rw [this]
      simp
    · have hd'd : d' = d := min_eq_right h.le
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le hd'1] at ht
        exact bump_eq_zero_of_ge hε (by rw [← hd'd]; exact ht.1)
  have hmid : (∫ t in c'..d', g t) ≤ d' - c' := by
    have : (∫ t in c'..d', g t) ≤ ∫ _t in c'..d', (1:ℝ) := by
      apply intervalIntegral.integral_mono_on hc'd' (hcont.intervalIntegrable _ _)
        (intervalIntegrable_const)
      intro t _
      exact bump_le_one t
    simpa using this
  have hdc : d' - c' ≤ d - c := by
    have h1 : c ≤ c' := le_max_right _ _
    have h2 : d' ≤ d := min_le_right _ _
    linarith
  linarith [hsplit1, hsplit2, hfirst, hlast, hmid, hdc]

lemma le_integral_bump {c d ε : ℝ} (hε : 0 < ε) (h0c : 0 ≤ c) (hd1 : d ≤ 1) :
    (d - ε) - (c + ε) ≤ ∫ t in (0:ℝ)..1, bump c d ε t := by
  set g : ℝ → ℝ := bump c d ε with hg
  have hcont : Continuous g := continuous_bump c d ε
  rcases le_or_gt (d - ε) (c + ε) with h | h
  · have : (0:ℝ) ≤ ∫ t in (0:ℝ)..1, g t := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t _
      exact bump_nonneg _ _ _ _
    linarith
  · have h1 : (0:ℝ) ≤ c + ε := by linarith
    have h2 : d - ε ≤ 1 := by linarith
    have h3 : c + ε ≤ d - ε := h.le
    have hsplit1 : (∫ t in (0:ℝ)..(c + ε), g t) + (∫ t in (c + ε)..1, g t)
        = ∫ t in (0:ℝ)..1, g t :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    have hsplit2 : (∫ t in (c + ε)..(d - ε), g t) + (∫ t in (d - ε)..(1:ℝ), g t)
        = ∫ t in (c + ε)..1, g t :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    have hA : (0:ℝ) ≤ ∫ t in (0:ℝ)..(c + ε), g t := by
      apply intervalIntegral.integral_nonneg h1
      intro t _
      exact bump_nonneg _ _ _ _
    have hB : (0:ℝ) ≤ ∫ t in (d - ε)..(1:ℝ), g t := by
      apply intervalIntegral.integral_nonneg h2
      intro t _
      exact bump_nonneg _ _ _ _
    have hmid : (∫ t in (c + ε)..(d - ε), g t) = (d - ε) - (c + ε) := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) ?_]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le h3] at ht
        exact bump_eq_one hε ht.1 ht.2
    linarith [hsplit1, hsplit2, hA, hB, hmid]

/-- The counting function equals the sum of the indicator. -/
lemma card_filter_eq_sum (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    ((((Finset.range N).filter (fun n => x n ∈ Set.Ico a b)).card : ℝ))
      = ∑ n ∈ Finset.range N, (if x n ∈ Set.Ico a b then (1:ℝ) else 0) := by
  rw [Finset.sum_boole]

/-- **Equidistribution from an asymptotic (Weyl-type) hypothesis.**

If the Cesàro averages of `f (x n)` converge to `∫₀¹ f` for every continuous `f : ℝ → ℝ`,
then the proportion of indices `n < N` with `x n ∈ [a, b)` converges to `b - a`, for every
subinterval `[a, b) ⊆ [0, 1]`. -/
theorem equidistribution_of_asymptotic (x : ℕ → ℝ)
    (h : ∀ f : ℝ → ℝ, Continuous f →
      Filter.Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / (N : ℝ)) Filter.atTop
        (nhds (∫ t in (0:ℝ)..1, f t)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ => ((((Finset.range N).filter (fun n => x n ∈ Set.Ico a b)).card : ℝ)) / (N : ℝ))
      Filter.atTop (nhds (b - a)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set e : ℝ := δ / 8 with he
  have hepos : 0 < e := by positivity
  -- lower and upper test functions
  set fl : ℝ → ℝ := bump a b e with hfl
  set fu : ℝ → ℝ := bump (a - e) (b + e) e with hfu
  have hIl : b - a - 2 * e ≤ ∫ t in (0:ℝ)..1, fl t := by
    have := le_integral_bump (c := a) (d := b) hepos ha hb
    linarith
  have hIu : (∫ t in (0:ℝ)..1, fu t) ≤ b - a + 2 * e := by
    have := integral_bump_le (c := a - e) (d := b + e) hepos (by linarith) (by linarith)
      (by linarith)
    linarith
  have hl := h fl (continuous_bump _ _ _)
  have hu := h fu (continuous_bump _ _ _)
  rw [Metric.tendsto_atTop] at hl hu
  obtain ⟨N1, hN1⟩ := hl e hepos
  obtain ⟨N2, hN2⟩ := hu e hepos
  refine ⟨max (max N1 N2) 1, fun N hN => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNpos : 0 < (N : ℝ) := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  -- pointwise sandwich of the sums
  have hsuml : (∑ n ∈ Finset.range N, fl (x n))
      ≤ (((Finset.range N).filter (fun n => x n ∈ Set.Ico a b)).card : ℝ) := by
    rw [card_filter_eq_sum]
    exact Finset.sum_le_sum fun n _ => bump_le_indicator hepos (x n)
  have hsumu : (((Finset.range N).filter (fun n => x n ∈ Set.Ico a b)).card : ℝ)
      ≤ ∑ n ∈ Finset.range N, fu (x n) := by
    rw [card_filter_eq_sum]
    exact Finset.sum_le_sum fun n _ => indicator_le_bump hepos (x n)
  set C : ℝ := (((Finset.range N).filter (fun n => x n ∈ Set.Ico a b)).card : ℝ) / (N : ℝ) with hC
  have hCl : (∑ n ∈ Finset.range N, fl (x n)) / (N : ℝ) ≤ C := by
    rw [hC]; gcongr
  have hCu : C ≤ (∑ n ∈ Finset.range N, fu (x n)) / (N : ℝ) := by
    rw [hC]; gcongr
  have h1 := hN1 N hN1'
  have h2 := hN2 N hN2'
  rw [Real.dist_eq, abs_lt] at h1 h2
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [h1.1, hCl, hIl]
  · linarith [h2.2, hCu, hIu]

end Equidistribution
end Brockian

