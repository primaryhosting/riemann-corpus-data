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
# Weyl's equidistribution criterion, via reduction of BV (indicator) test functions

This file proves the classical **Weyl criterion** (sufficiency direction):
if all nontrivial exponential sums along a real sequence `x : ℕ → ℝ` have vanishing
Cesàro averages, then `x` is equidistributed modulo one in the counting sense.

The proof proceeds by the *BV reduction*: the characteristic function of an interval
(a function of bounded variation) is squeezed between continuous trapezoidal functions
on the circle, and continuous functions on the circle are approximated uniformly by
trigonometric polynomials.

As an application, the sequence `n ↦ n * α` is equidistributed mod one for irrational `α`.
-/

open Filter Topology MeasureTheory Finset

namespace Brockian
namespace EquidistributionBVReduction

noncomputable section

open scoped Classical

instance factOnePos : Fact ((0:ℝ) < 1) := ⟨one_pos⟩

/-- The circle `ℝ / ℤ`. -/
abbrev Circ := AddCircle (1:ℝ)

/-- `x : ℕ → ℝ` is equidistributed modulo one: for every subinterval `[a, b) ⊆ [0,1]`,
the proportion of the first `N` terms whose fractional part lies in `[a, b)` tends to
`b - a`. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / (N : ℝ))
      atTop (𝓝 (b - a))

/-- Weyl's exponential sum condition: for every nonzero integer frequency `k`, the Cesàro
averages of `exp (2 π i k xₙ)` tend to `0`. -/
def WeylCondition (x : ℕ → ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 →
    Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * x n)) / (N : ℂ))
      atTop (𝓝 0)

/-- Averages of `f` along the sequence `x` (viewed on the circle) tend to the integral of
`f` over the circle. -/
def AvgTendsto (x : ℕ → ℝ) (f : Circ → ℂ) : Prop :=
  Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f ((x n : ℝ) : Circ)) / (N : ℂ))
    atTop (𝓝 (∫ t, f t))

/-! ### Basic facts about the circle -/

lemma volume_circ_univ : (volume (Set.univ : Set Circ)) = 1 := by
  rw [AddCircle.measure_univ]; norm_num

instance : IsProbabilityMeasure (volume : Measure Circ) := ⟨volume_circ_univ⟩

lemma integrable_of_continuous {f : Circ → ℂ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma integrable_of_continuous_real {f : Circ → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-! ### Step 1: the Weyl condition gives the result for characters -/

lemma integral_fourier_eq_zero {k : ℤ} (hk : k ≠ 0) : (∫ t : Circ, fourier k t) = 0 := by
  rw [← AddCircle.intervalIntegral_preimage (1:ℝ) 0 (fun z : Circ => fourier k z)]
  have hc : (2 * (Real.pi:ℂ) * Complex.I * k) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero, hk]
  have hf : ∀ t : ℝ,
      (fourier k (t : Circ)) = Complex.exp ((2 * (Real.pi:ℂ) * Complex.I * k) * t) := by
    intro t; rw [fourier_coe_apply]; norm_num
  simp only [hf]
  rw [integral_exp_mul_complex hc]
  have h1 : (2 * (Real.pi:ℂ) * Complex.I * k * (((0:ℝ) + 1 : ℝ) : ℂ))
      = (k : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [h1, Complex.exp_int_mul_two_pi_mul_I]
  norm_num

lemma integral_fourier_zero : (∫ t : Circ, fourier (0 : ℤ) t) = 1 := by
  simp

lemma avgTendsto_fourier {x : ℕ → ℝ} (hW : WeylCondition x) (k : ℤ) :
    AvgTendsto x (fourier k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · unfold AvgTendsto
    rw [integral_fourier_zero]
    apply Tendsto.congr' _ (tendsto_const_nhds (x := (1:ℂ)))
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [fourier_zero]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      div_self (by exact_mod_cast hN.ne' : (N:ℂ) ≠ 0)]
  · unfold AvgTendsto
    rw [integral_fourier_eq_zero hk]
    refine (hW k hk).congr (fun N => ?_)
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [fourier_coe_apply]
    norm_num

/-! ### Step 2: linearity and closedness, hence all continuous test functions -/

/-- The set of continuous test functions for which the averages converge, as a submodule. -/
def avgSubmodule (x : ℕ → ℝ) : Submodule ℂ C(Circ, ℂ) where
  carrier := {f | AvgTendsto x f}
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, AvgTendsto, ContinuousMap.coe_add, Pi.add_apply] at *
    rw [integral_add (integrable_of_continuous f.continuous)
      (integrable_of_continuous g.continuous)]
    refine (hf.add hg).congr (fun N => ?_)
    rw [Finset.sum_add_distrib, add_div]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, AvgTendsto, ContinuousMap.coe_zero]
    simp
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq, AvgTendsto, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul] at *
    rw [integral_const_mul]
    refine (hf.const_mul c).congr (fun N => ?_)
    rw [← mul_div_assoc, Finset.mul_sum]

lemma mem_avgSubmodule (x : ℕ → ℝ) (f : C(Circ, ℂ)) : f ∈ avgSubmodule x ↔ AvgTendsto x f :=
  Iff.rfl

lemma dist_avg_le (x : ℕ → ℝ) (f g : C(Circ, ℂ)) (N : ℕ) (hN : 0 < N) :
    ‖(∑ n ∈ range N, f ((x n : ℝ) : Circ)) / (N:ℂ)
      - (∑ n ∈ range N, g ((x n : ℝ) : Circ)) / (N:ℂ)‖ ≤ ‖f - g‖ := by
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, norm_div]
  have h1 : ‖∑ n ∈ range N, (f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ))‖ ≤ N * ‖f - g‖ := by
    calc ‖∑ n ∈ range N, (f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ))‖
        ≤ ∑ n ∈ range N, ‖f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range N, ‖f - g‖ := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          simpa using ContinuousMap.norm_coe_le_norm (f - g) ((x n : ℝ) : Circ)
      _ = N * ‖f - g‖ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Complex.norm_natCast, div_le_iff₀ (by positivity)]
  linarith

lemma norm_integral_sub_le (f g : C(Circ, ℂ)) :
    ‖(∫ t : Circ, f t) - ∫ t : Circ, g t‖ ≤ ‖f - g‖ := by
  rw [← integral_sub (integrable_of_continuous f.continuous)
    (integrable_of_continuous g.continuous)]
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure Circ))
    (C := ‖f - g‖) (f := fun t => f t - g t) ?_
  · simpa [volume_circ_univ] using this
  · filter_upwards with t
    simpa using ContinuousMap.norm_coe_le_norm (f - g) t

lemma isClosed_avgSubmodule (x : ℕ → ℝ) :
    IsClosed ((avgSubmodule x : Submodule ℂ C(Circ, ℂ)) : Set C(Circ, ℂ)) := by
  apply isClosed_of_closure_subset
  intro f hf
  rw [SetLike.mem_coe, mem_avgSubmodule, AvgTendsto, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgS, hgd⟩ := Metric.mem_closure_iff.1 hf (ε/3) (by linarith)
  have hg : AvgTendsto x g := (mem_avgSubmodule x g).1 hgS
  rw [AvgTendsto, Metric.tendsto_atTop] at hg
  obtain ⟨N₀, hN₀⟩ := hg (ε/3) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N₀ 1) hN)
  have hfg : ‖f - g‖ < ε/3 := by rw [← dist_eq_norm]; exact hgd
  have h1 : dist ((∑ n ∈ range N, f ((x n:ℝ) : Circ)) / (N:ℂ))
      ((∑ n ∈ range N, g ((x n:ℝ) : Circ)) / (N:ℂ)) < ε/3 := by
    rw [dist_eq_norm]; exact lt_of_le_of_lt (dist_avg_le x f g N hN1) hfg
  have h3 := hN₀ N (le_trans (le_max_left N₀ 1) hN)
  have h2 : dist (∫ t : Circ, g t) (∫ t : Circ, f t) < ε/3 := by
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt (norm_integral_sub_le f g) hfg
  calc dist ((∑ n ∈ range N, f ((x n:ℝ) : Circ)) / (N:ℂ)) (∫ t : Circ, f t)
      ≤ dist ((∑ n ∈ range N, f ((x n:ℝ) : Circ)) / (N:ℂ))
            ((∑ n ∈ range N, g ((x n:ℝ) : Circ)) / (N:ℂ))
        + dist ((∑ n ∈ range N, g ((x n:ℝ) : Circ)) / (N:ℂ)) (∫ t : Circ, g t)
        + dist (∫ t : Circ, g t) (∫ t : Circ, f t) := dist_triangle4 _ _ _ _
    _ < ε/3 + ε/3 + ε/3 := by linarith
    _ = ε := by ring

lemma avgTendsto_continuous {x : ℕ → ℝ} (hW : WeylCondition x) (f : C(Circ, ℂ)) :
    AvgTendsto x f := by
  have hspan : Submodule.span ℂ (Set.range (fourier (T := (1:ℝ)))) ≤ avgSubmodule x := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact (mem_avgSubmodule x _).2 (avgTendsto_fourier hW k)
  have h := Submodule.topologicalClosure_minimal _ hspan (isClosed_avgSubmodule x)
  rw [span_fourier_closure_eq_top] at h
  exact (mem_avgSubmodule x f).1 (h Submodule.mem_top)

lemma avgTendsto_real {x : ℕ → ℝ} (hW : WeylCondition x) {f : Circ → ℝ} (hf : Continuous f) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f ((x n : ℝ) : Circ)) / (N : ℝ))
      atTop (𝓝 (∫ t, f t)) := by
  have hc : AvgTendsto x (fun t => ((f t : ℝ) : ℂ)) :=
    avgTendsto_continuous hW ⟨fun t => ((f t : ℝ) : ℂ), by fun_prop⟩
  rw [AvgTendsto, integral_complex_ofReal] at hc
  refine tendsto_ofReal_iff.mp (hc.congr (fun N => ?_))
  push_cast
  ring

/-! ### Step 3: trapezoidal approximations of indicators -/

/-- A trapezoid supported in `[u, v]`, equal to `1` on `[u + ε, v - ε]`. -/
def trap (u v ε : ℝ) (t : ℝ) : ℝ := max 0 (min 1 (min ((t - u)/ε) ((v - t)/ε)))

lemma trap_nonneg (u v ε t : ℝ) : 0 ≤ trap u v ε t := le_max_left _ _

lemma trap_le_one (u v ε t : ℝ) : trap u v ε t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma continuous_trap (u v ε : ℝ) : Continuous (trap u v ε) := by
  unfold trap; fun_prop

lemma trap_eq_one {u v ε t : ℝ} (hε : 0 < ε) (h1 : u + ε ≤ t) (h2 : t ≤ v - ε) :
    trap u v ε t = 1 := by
  unfold trap
  have e1 : (1:ℝ) ≤ (t - u)/ε := by rw [le_div_iff₀ hε]; linarith
  have e2 : (1:ℝ) ≤ (v - t)/ε := by rw [le_div_iff₀ hε]; linarith
  rw [min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

lemma trap_eq_zero_of_le {u v ε t : ℝ} (hε : 0 < ε) (h : t ≤ u) : trap u v ε t = 0 := by
  unfold trap
  have h1 : (t - u)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h1))

lemma trap_eq_zero_of_ge {u v ε t : ℝ} (hε : 0 < ε) (h : v ≤ t) : trap u v ε t = 0 := by
  unfold trap
  have h1 : (v - t)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h1))

/-- The trapezoid transplanted to the circle, using the fundamental domain `[p, p+1)`. -/
def circTrap (p u v ε : ℝ) : Circ → ℝ := AddCircle.liftIco 1 p (trap u v ε)

lemma circTrap_coe {p u v ε : ℝ} {t : ℝ} (ht : t ∈ Set.Ico p (p + 1)) :
    circTrap p u v ε (t : Circ) = trap u v ε t :=
  AddCircle.liftIco_coe_apply (by simpa using ht)

lemma circTrap_nonneg (p u v ε : ℝ) (z : Circ) : 0 ≤ circTrap p u v ε z := by
  unfold circTrap AddCircle.liftIco
  simp only [Function.comp_apply, Set.restrict_apply]
  exact trap_nonneg _ _ _ _

lemma circTrap_le_one (p u v ε : ℝ) (z : Circ) : circTrap p u v ε z ≤ 1 := by
  unfold circTrap AddCircle.liftIco
  simp only [Function.comp_apply, Set.restrict_apply]
  exact trap_le_one _ _ _ _

lemma continuous_circTrap {p u v ε : ℝ} (h1 : trap u v ε p = 0)
    (h2 : trap u v ε (p + 1) = 0) : Continuous (circTrap p u v ε) :=
  AddCircle.liftIco_continuous (by rw [h1, h2]) (continuous_trap u v ε).continuousOn

lemma integral_circTrap (p u v ε : ℝ) :
    (∫ z : Circ, circTrap p u v ε z) = ∫ t in p..(p+1), trap u v ε t := by
  rw [← AddCircle.intervalIntegral_preimage 1 p (circTrap p u v ε)]
  apply intervalIntegral.integral_congr_ae
  have h0 : ∀ᵐ (t:ℝ), t ∉ ({p+1} : Set ℝ) := by rw [ae_iff]; simp
  filter_upwards [h0] with t ht hmem
  rw [Set.uIoc_of_le (by linarith)] at hmem
  exact circTrap_coe ⟨hmem.1.le, lt_of_le_of_ne hmem.2 (by simpa using ht)⟩

lemma coe_fract (y : ℝ) : ((Int.fract y : ℝ) : Circ) = (y : Circ) := by
  rw [Int.fract]; simp

lemma circTrap_coe_rep (p u v ε y : ℝ) :
    ∃ m : ℤ, (y + m) ∈ Set.Ico p (p+1) ∧ circTrap p u v ε (y : Circ) = trap u v ε (y + m) := by
  have h1 : p ≤ y + (⌈p - y⌉ : ℤ) := by have := Int.le_ceil (p - y); linarith
  have h2 : y + (⌈p - y⌉ : ℤ) < p + 1 := by have := Int.ceil_lt_add_one (p - y); linarith
  refine ⟨⌈p - y⌉, ⟨h1, h2⟩, ?_⟩
  rw [show ((y:ℝ) : Circ) = (((y + (⌈p-y⌉:ℤ) : ℝ)) : Circ) by simp]
  exact circTrap_coe ⟨h1, h2⟩

lemma integral_trap_le {u v ε p : ℝ} (hε : 0 < ε) (hpu : p ≤ u) (huv : u ≤ v) (hv : v ≤ p + 1) :
    (∫ t in p..(p+1), trap u v ε t) ≤ v - u := by
  have hint : ∀ c d : ℝ, IntervalIntegrable (trap u v ε) volume c d :=
    fun c d => (continuous_trap u v ε).intervalIntegrable c d
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint p u) (hint u (p+1)),
    ← intervalIntegral.integral_add_adjacent_intervals (hint u v) (hint v (p+1))]
  have h1 : (∫ t in p..u, trap u v ε t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hpu] at ht
      exact trap_eq_zero_of_le hε ht.2
  have h3 : (∫ t in v..(p+1), trap u v ε t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hv] at ht
      exact trap_eq_zero_of_ge hε ht.1
  have h2 : (∫ t in u..v, trap u v ε t) ≤ v - u := by
    calc (∫ t in u..v, trap u v ε t) ≤ ∫ _t in u..v, (1:ℝ) :=
          intervalIntegral.integral_mono_on huv (hint u v) intervalIntegrable_const
            (fun t _ => trap_le_one _ _ _ _)
      _ = v - u := by simp
  rw [h1, h3]
  linarith

lemma le_integral_trap {u v ε p : ℝ} (hε : 0 < ε) (hpu : p ≤ u) (huv : u + ε ≤ v - ε)
    (hv : v ≤ p + 1) : v - u - 2*ε ≤ ∫ t in p..(p+1), trap u v ε t := by
  have hint : ∀ c d : ℝ, IntervalIntegrable (trap u v ε) volume c d :=
    fun c d => (continuous_trap u v ε).intervalIntegrable c d
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint p (u+ε)) (hint (u+ε) (p+1)),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (u+ε) (v-ε)) (hint (v-ε) (p+1))]
  have h1 : 0 ≤ (∫ t in p..(u+ε), trap u v ε t) :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => trap_nonneg _ _ _ _)
  have h3 : 0 ≤ (∫ t in (v-ε)..(p+1), trap u v ε t) :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => trap_nonneg _ _ _ _)
  have h2 : (∫ t in (u+ε)..(v-ε), trap u v ε t) = (v - ε) - (u + ε) := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le huv] at ht
      exact trap_eq_one hε ht.1 ht.2
  rw [h2]
  linarith

/-- Counting is bounded above by the average of the outer trapezoid. -/
lemma count_le_sum_circTrap {x : ℕ → ℝ} {a b ε p : ℝ} (hε : 0 < ε) (hpa : p ≤ a - ε)
    (hpb : b + ε ≤ p + 1) (N : ℕ) :
    (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ)
      ≤ ∑ n ∈ Finset.range N, circTrap p (a - ε) (b + ε) ε ((x n : ℝ) : Circ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases h : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos h, ← coe_fract (x n),
      circTrap_coe (u := a - ε) (v := b + ε) ⟨by have := h.1; linarith, by have := h.2; linarith⟩,
      trap_eq_one hε (by have := h.1; linarith) (by have := h.2; linarith)]
  · rw [if_neg h]
    exact circTrap_nonneg _ _ _ _ _

/-- Counting is bounded below by the average of the inner trapezoid. -/
lemma sum_circTrap_le_count {x : ℕ → ℝ} {a b ε p : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hb : b ≤ 1)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, circTrap p a b ε ((x n : ℝ) : Circ))
      ≤ (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases h : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos h]
    exact circTrap_le_one _ _ _ _ _
  · rw [if_neg h]
    have hfr0 : 0 ≤ Int.fract (x n) := Int.fract_nonneg _
    have hfr1 : Int.fract (x n) < 1 := Int.fract_lt_one _
    rw [← coe_fract (x n)]
    obtain ⟨m, _, heq⟩ := circTrap_coe_rep p a b ε (Int.fract (x n))
    rw [heq]
    refine le_of_eq ?_
    by_contra hne
    have h1 : ¬ (Int.fract (x n) + m ≤ a) := fun hle => hne (trap_eq_zero_of_le hε hle)
    have h2 : ¬ (b ≤ Int.fract (x n) + m) := fun hge => hne (trap_eq_zero_of_ge hε hge)
    push_neg at h1 h2
    have hm0 : m = 0 := by
      have hm1 : (-1 : ℝ) < (m : ℝ) := by linarith
      have hm2 : (m : ℝ) < 1 := by linarith
      have hm1' : (-1 : ℤ) < m := by exact_mod_cast hm1
      have hm2' : m < (1 : ℤ) := by exact_mod_cast hm2
      omega
    subst hm0
    simp only [Int.cast_zero, add_zero] at h1 h2
    exact h ⟨h1.le, h2⟩

/-! ### Step 4: the main theorem -/

/-- Key sandwich estimate for a nondegenerate proper subinterval. -/
lemma tendsto_count_of_weyl {x : ℕ → ℝ} (hW : WeylCondition x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hlt : b - a < 1) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / (N : ℝ))
      atTop (𝓝 (b - a)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set p : ℝ := (a + b - 1)/2 with hpdef
  obtain ⟨ε, hε, hε1, hε2, hε3⟩ :
      ∃ ε : ℝ, 0 < ε ∧ 4*ε ≤ 1 - (b - a) ∧ 2*ε ≤ b - a ∧ 4*ε < δ := by
    refine ⟨min ((1 - (b-a))/4) (min ((b-a)/2) (δ/5)), ?_, ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
    · have := min_le_left ((1 - (b-a))/4) (min ((b-a)/2) (δ/5)); linarith
    · have := le_trans (min_le_right ((1 - (b-a))/4) (min ((b-a)/2) (δ/5))) (min_le_left _ _)
      linarith
    · have := le_trans (min_le_right ((1 - (b-a))/4) (min ((b-a)/2) (δ/5))) (min_le_right _ _)
      linarith
  have hpa : p ≤ a - ε := by rw [hpdef]; linarith
  have hpb : b + ε ≤ p + 1 := by rw [hpdef]; linarith
  have hcont_hi : Continuous (circTrap p (a - ε) (b + ε) ε) :=
    continuous_circTrap (trap_eq_zero_of_le hε (by linarith))
      (trap_eq_zero_of_ge hε (by linarith))
  have hcont_lo : Continuous (circTrap p a b ε) :=
    continuous_circTrap (trap_eq_zero_of_le hε (by linarith))
      (trap_eq_zero_of_ge hε (by linarith))
  have hIhi : (∫ z : Circ, circTrap p (a - ε) (b + ε) ε z) ≤ (b - a) + 2*ε := by
    rw [integral_circTrap]
    have := integral_trap_le (u := a - ε) (v := b + ε) (p := p) hε (by linarith) (by linarith)
      (by linarith)
    linarith
  have hIlo : (b - a) - 2*ε ≤ ∫ z : Circ, circTrap p a b ε z := by
    rw [integral_circTrap]
    have := le_integral_trap (u := a) (v := b) (p := p) hε (by linarith) (by linarith)
      (by linarith)
    linarith
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (avgTendsto_real hW hcont_hi) ε hε
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (avgTendsto_real hW hcont_lo) ε hε
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ 1) hN)
  have hNR : (0:ℝ) < N := by exact_mod_cast hN1
  have h1 := hN₁ N (le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 1)) hN)
  have h2 := hN₂ N (le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 1)) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  have hcu : (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / (N:ℝ)
      ≤ (∑ n ∈ Finset.range N, circTrap p (a - ε) (b + ε) ε ((x n : ℝ) : Circ)) / (N:ℝ) := by
    gcongr
    exact count_le_sum_circTrap hε hpa hpb N
  have hcl : (∑ n ∈ Finset.range N, circTrap p a b ε ((x n : ℝ) : Circ)) / (N:ℝ)
      ≤ (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / (N:ℝ) := by
    gcongr
    exact sum_circTrap_le_count hε ha hb N
  constructor
  · linarith [h2.1, hIlo, hcl]
  · linarith [h1.2, hIhi, hcu]

/-- **Weyl's equidistribution criterion.** If all nontrivial exponential sums along `x` have
vanishing Cesàro averages, then `x` is equidistributed modulo one.  The BV (indicator) test
functions are reduced to continuous ones by a trapezoidal sandwich, and continuous test
functions are handled by Fourier approximation. -/
theorem equidistribution_of_BV_uniform {x : ℕ → ℝ} (hW : WeylCondition x) :
    EquidistributedMod1 x := by
  intro a b ha hab hb
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp only [Set.Ico_self, Set.mem_empty_iff_false, Finset.filter_false, Finset.card_empty,
      Nat.cast_zero, zero_div, sub_self]
    exact tendsto_const_nhds
  · rcases lt_or_eq_of_le (show b - a ≤ 1 by linarith) with hltb | heq
    · exact tendsto_count_of_weyl hW ha hlt hb hltb
    · have ha0 : a = 0 := by linarith
      have hb1 : b = 1 := by linarith
      subst ha0; subst hb1
      rw [show (1:ℝ) - 0 = 1 by ring]
      apply Tendsto.congr' _ (tendsto_const_nhds (x := (1:ℝ)))
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [Finset.filter_true_of_mem (fun n _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩),
        Finset.card_range, div_self (by exact_mod_cast hN.ne' : (N:ℝ) ≠ 0)]

/-- For irrational `α` the sequence `n ↦ n α` satisfies Weyl's exponential-sum condition:
the sums are geometric series with ratio `≠ 1`, hence bounded. -/
theorem weylCondition_nat_mul_irrational {α : ℝ} (hα : Irrational α) :
    WeylCondition (fun n : ℕ => n * α) := by
  intro k hk
  set z : ℂ := Complex.exp (2 * (Real.pi:ℂ) * Complex.I * k * α) with hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have h2 : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
      simp [Complex.ext_iff, Real.pi_ne_zero]
    field_simp at hm
    have hreal : (k:ℝ) * α = (m:ℝ) := by exact_mod_cast hm
    exact (Irrational.intCast_mul hα hk).ne_int m hreal
  have hnorm : ‖z‖ = 1 := by
    rw [hz, show 2 * (Real.pi:ℂ) * Complex.I * k * α
        = ((2 * Real.pi * k * α : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hsum : ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        Complex.exp (2 * (Real.pi:ℂ) * Complex.I * k * ((((n:ℝ) * α : ℝ)) : ℂ)))
        = (z ^ N - 1) / (z - 1) := by
    intro N
    rw [← geom_sum_eq hz1 N]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hd : 0 < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
  apply squeeze_zero_norm' (a := fun N : ℕ => (2 / ‖z - 1‖) / N)
  · filter_upwards with N
    rw [norm_div, hsum N, norm_div, Complex.norm_natCast]
    have hzn : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hnorm]; norm_num
    gcongr
  · exact tendsto_const_div_atTop_nhds_zero_nat _

/-- **Weyl's theorem**: for irrational `α`, the sequence `n ↦ n α` is equidistributed mod one. -/
theorem equidistributedMod1_nat_mul_irrational {α : ℝ} (hα : Irrational α) :
    EquidistributedMod1 (fun n : ℕ => n * α) :=
  equidistribution_of_BV_uniform (weylCondition_nat_mul_irrational hα)

end

end EquidistributionBVReduction
end Brockian

