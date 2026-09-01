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
# Equidistribution of irrational rotations and the bounded-variation reduction

This file develops, from scratch, Weyl's equidistribution theorem for the sequence
`n ↦ n • α mod 1` (`α` irrational) and reduces averages of functions of bounded variation
to their integral.

The final result `total_over_main_tendsto` states that, for a function `f` of bounded
variation on `[0,1]` with nonzero integral, the *total*
`∑_{n < N} f (fract (n α))` divided by the *main term* `N * ∫₀¹ f` tends to `1`.
-/

open Filter Finset Set MeasureTheory Metric
open scoped Topology

namespace Brockian.EquidistributionBVReduction

noncomputable section

/-- A sequence of reals is equidistributed mod one when, for every subinterval `[a,b) ⊆ [0,1]`,
the proportion of the first `N` fractional parts lying in `[a, b)` tends to `b - a`. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ =>
        (((range N).filter fun n => Int.fract (x n) ∈ Ico a b).card : ℝ) / (N : ℝ))
      atTop (𝓝 (b - a))

/-! ### Step 1: averages of Fourier characters -/

/-- Averages of geometric sums with unimodular ratio `z ≠ 1` tend to `0`. -/
theorem geom_avg_tendsto (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, z ^ n) / (N : ℂ)) atTop (𝓝 0) := by
  have hzn : (0:ℝ) < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
  have hS : ∀ N : ℕ, ‖∑ n ∈ range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
    intro N
    rw [geom_sum_eq hz1, norm_div]
    gcongr
    calc ‖z ^ N - 1‖ ≤ ‖(z:ℂ) ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow, hz]; norm_num
  refine squeeze_zero_norm (fun N => ?_) (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖z - 1‖))
  rw [norm_div, Complex.norm_natCast]
  gcongr
  exact hS N

/-- The Fourier character evaluated along the orbit is a geometric sequence. -/
theorem fourier_orbit (α : ℝ) (k : ℤ) (n : ℕ) :
    fourier k (((n * α : ℝ)) : AddCircle (1:ℝ))
      = (fourier k ((α : ℝ) : AddCircle (1:ℝ))) ^ n := by
  rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- For irrational `α` and `k ≠ 0`, the value `fourier k α` is not `1`. -/
theorem fourier_ne_one {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    (fourier k ((α : ℝ) : AddCircle (1:ℝ))) ≠ 1 := by
  rw [fourier_coe_apply]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2:ℂ) * (Real.pi:ℂ) * Complex.I ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have key : (k : ℂ) * (α : ℂ) = (m : ℂ) := by
    have : (2 * (Real.pi:ℂ) * Complex.I) * ((k:ℂ) * α)
        = (2 * (Real.pi:ℂ) * Complex.I) * m := by
      push_cast at hm ⊢
      linear_combination hm
    exact mul_left_cancel₀ h2 this
  have hreal : (k : ℝ) * α = (m : ℝ) := by exact_mod_cast key
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  refine hα ⟨(m : ℚ) / (k : ℚ), ?_⟩
  push_cast
  field_simp
  linear_combination -hreal

/-- `‖fourier k x‖ = 1`. -/
theorem norm_fourier_coe (k : ℤ) (x : ℝ) :
    ‖fourier k ((x : ℝ) : AddCircle (1:ℝ))‖ = 1 := by
  rw [fourier_coe_apply, Complex.norm_exp]
  norm_num

/-- Every continuous function on the circle is integrable. -/
theorem integrable_of_continuousMap (F : C(AddCircle (1:ℝ), ℂ)) :
    Integrable (fun t => F t) (volume : Measure (AddCircle (1:ℝ))) :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integral of a Fourier character over the circle. -/
theorem integral_fourier (k : ℤ) :
    ∫ t : AddCircle (1:ℝ), fourier k t = if k = 0 then 1 else 0 := by
  have h0 := congrFun (fourierCoeff_fourier (T := (1:ℝ)) k) 0
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul] at h0
  have hh : ∫ t : AddCircle (1:ℝ), fourier k t ∂AddCircle.haarAddCircle
      = ∫ t : AddCircle (1:ℝ), fourier k t := by
    rw [AddCircle.integral_haarAddCircle]; simp
  rw [← hh, h0]
  by_cases hk : k = 0 <;> simp [hk, Pi.single_apply, eq_comm]

/-- The Cesàro average of a Fourier character along the orbit converges to its integral. -/
theorem avg_fourier_tendsto {α : ℝ} (hα : Irrational α) (k : ℤ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, fourier k ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ))
      atTop (𝓝 (∫ t : AddCircle (1:ℝ), fourier k t)) := by
  rw [integral_fourier]
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    have : ∀ N : ℕ, N ≠ 0 →
        (∑ n ∈ range N, fourier (0:ℤ) ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ) = 1 := by
      intro N hN
      simp only [fourier_zero, sum_const, card_range, nsmul_eq_mul, mul_one]
      exact div_self (Nat.cast_ne_zero.mpr hN)
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ne_atTop 0] with N hN using (this N hN).symm
  · simp only [if_neg hk]
    have hz : ‖fourier k ((α : ℝ) : AddCircle (1:ℝ))‖ = 1 := norm_fourier_coe k α
    have := geom_avg_tendsto _ hz (fourier_ne_one hα hk)
    refine this.congr (fun N => ?_)
    congr 1
    exact (sum_congr rfl fun n _ => (fourier_orbit α k n)).symm

/-! ### Step 2: from characters to all continuous functions -/

/-- The averaging result for trigonometric polynomials. -/
theorem avg_tendsto_of_mem_span {α : ℝ} (hα : Irrational α) (F : C(AddCircle (1:ℝ), ℂ))
    (hF : F ∈ Submodule.span ℂ (Set.range (fourier (T := (1:ℝ))))) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)) atTop
      (𝓝 (∫ t : AddCircle (1:ℝ), F t)) := by
  induction hF using Submodule.span_induction with
  | mem F hF => obtain ⟨k, rfl⟩ := hF; exact avg_fourier_tendsto hα k
  | zero => simp
  | add F G _ _ ihF ihG =>
      have hint : ∫ t : AddCircle (1:ℝ), (F + G) t
          = (∫ t : AddCircle (1:ℝ), F t) + ∫ t : AddCircle (1:ℝ), G t := by
        simp only [ContinuousMap.add_apply]
        exact integral_add (integrable_of_continuousMap F) (integrable_of_continuousMap G)
      rw [hint]
      refine (ihF.add ihG).congr (fun N => ?_)
      simp only [ContinuousMap.add_apply, sum_add_distrib]
      ring
  | smul c F _ ih =>
      have hint : ∫ t : AddCircle (1:ℝ), (c • F) t = c * ∫ t : AddCircle (1:ℝ), F t := by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact integral_const_mul c _
      rw [hint]
      refine (ih.const_mul c).congr (fun N => ?_)
      simp only [ContinuousMap.smul_apply, smul_eq_mul, ← mul_sum]
      ring

/-- The integral of a continuous function on the unit circle is bounded by its sup-norm. -/
theorem norm_integral_le_norm (H : C(AddCircle (1:ℝ), ℂ)) :
    ‖∫ t : AddCircle (1:ℝ), H t‖ ≤ ‖H‖ := by
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (AddCircle (1:ℝ)))) (C := ‖H‖)
    (f := fun t => H t) (Filter.Eventually.of_forall fun t => H.norm_coe_le_norm t)
  simpa [measureReal_def] using this

/-- **Weyl's theorem, continuous form.** For irrational `α`, the Cesàro averages of a continuous
function on the circle along the orbit of the rotation by `α` converge to its integral. -/
theorem avg_tendsto_continuous {α : ℝ} (hα : Irrational α) (F : C(AddCircle (1:ℝ), ℂ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)) atTop
      (𝓝 (∫ t : AddCircle (1:ℝ), F t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmem : F ∈ closure
      ((Submodule.span ℂ (Set.range (fourier (T := (1:ℝ))))) : Set C(AddCircle (1:ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]; trivial
  obtain ⟨G, hGmem, hFG⟩ := Metric.mem_closure_iff.1 hmem (ε/4) (by positivity)
  rw [dist_eq_norm] at hFG
  obtain ⟨N₁, hN₁⟩ :=
    Metric.tendsto_atTop.1 (avg_tendsto_of_mem_span hα G hGmem) (ε/4) (by positivity)
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have hdiff : ‖(∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)
      - (∑ n ∈ range N, G ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)‖ ≤ ‖F - G‖ := by
    rw [div_sub_div_same, ← sum_sub_distrib, norm_div, Complex.norm_natCast, div_le_iff₀ hNpos]
    calc ‖∑ n ∈ range N, (F ((n * α : ℝ) : AddCircle (1:ℝ)) - G ((n * α : ℝ) : AddCircle (1:ℝ)))‖
        ≤ ∑ n ∈ range N,
            ‖F ((n * α : ℝ) : AddCircle (1:ℝ)) - G ((n * α : ℝ) : AddCircle (1:ℝ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ range N, ‖F - G‖ := by
          refine sum_le_sum fun n _ => ?_
          simpa using (F - G).norm_coe_le_norm ((n * α : ℝ) : AddCircle (1:ℝ))
      _ = ‖F - G‖ * N := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hint : ‖(∫ t : AddCircle (1:ℝ), G t) - ∫ t : AddCircle (1:ℝ), F t‖ ≤ ‖F - G‖ := by
    have hsub : (∫ t : AddCircle (1:ℝ), G t) - ∫ t : AddCircle (1:ℝ), F t
        = ∫ t : AddCircle (1:ℝ), (G - F) t := by
      simp only [ContinuousMap.sub_apply]
      rw [integral_sub (integrable_of_continuousMap G) (integrable_of_continuousMap F)]
    rw [hsub]
    calc ‖∫ t : AddCircle (1:ℝ), (G - F) t‖ ≤ ‖G - F‖ := norm_integral_le_norm _
      _ = ‖F - G‖ := norm_sub_rev _ _
  have h3 := hN₁ N (le_trans (le_max_left _ _) hN)
  rw [dist_eq_norm] at h3 ⊢
  calc ‖(∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ) - ∫ t : AddCircle (1:ℝ), F t‖
      ≤ ‖(∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)
          - (∑ n ∈ range N, G ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)‖
        + ‖(∑ n ∈ range N, G ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)
            - ∫ t : AddCircle (1:ℝ), G t‖
        + ‖(∫ t : AddCircle (1:ℝ), G t) - ∫ t : AddCircle (1:ℝ), F t‖ := by
        have := norm_add₃_le (a := (∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)
          - (∑ n ∈ range N, G ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ))
          (b := (∑ n ∈ range N, G ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)
            - ∫ t : AddCircle (1:ℝ), G t)
          (c := (∫ t : AddCircle (1:ℝ), G t) - ∫ t : AddCircle (1:ℝ), F t)
        simpa using this
    _ < ε := by linarith [hdiff, hint, h3]

/-- **Weyl's theorem, real continuous form.** -/
theorem avg_tendsto_continuous_real {α : ℝ} (hα : Irrational α) (F : AddCircle (1:ℝ) → ℝ)
    (hF : Continuous F) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℝ)) atTop
      (𝓝 (∫ t : AddCircle (1:ℝ), F t)) := by
  set G : C(AddCircle (1:ℝ), ℂ) := ⟨fun t => (F t : ℂ), Complex.continuous_ofReal.comp hF⟩ with hG
  have h := avg_tendsto_continuous hα G
  have hint : (∫ t : AddCircle (1:ℝ), G t) = ((∫ t : AddCircle (1:ℝ), F t : ℝ) : ℂ) := by
    simp [hG, integral_complex_ofReal]
  rw [hint] at h
  have h2 : Tendsto
      (fun N : ℕ => (((∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℝ) : ℝ) : ℂ))
      atTop (𝓝 (((∫ t : AddCircle (1:ℝ), F t : ℝ) : ℂ))) := by
    refine h.congr (fun N => ?_)
    push_cast [hG]
    rfl
  exact tendsto_ofReal_iff.mp h2

/-! ### Step 3: from continuous functions to intervals -/

/-- A trapezoidal bump: it equals `1` on the closed ball of radius `s` around `c`,
vanishes outside the ball of radius `s + δ`, and takes values in `[0,1]`. -/
def bump (c : AddCircle (1:ℝ)) (s δ : ℝ) : AddCircle (1:ℝ) → ℝ :=
  fun x => max 0 (min 1 ((s + δ - dist x c)/δ))

theorem continuous_bump (c : AddCircle (1:ℝ)) (s δ : ℝ) : Continuous (bump c s δ) := by
  unfold bump; fun_prop

theorem bump_nonneg (c : AddCircle (1:ℝ)) (s δ : ℝ) (x) : 0 ≤ bump c s δ x := le_max_left _ _

theorem bump_le_one (c : AddCircle (1:ℝ)) (s δ : ℝ) (x) : bump c s δ x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem bump_eq_one {c : AddCircle (1:ℝ)} {s δ : ℝ} (hδ : 0 < δ) {x} (hx : dist x c ≤ s) :
    bump c s δ x = 1 := by
  unfold bump
  have h1 : (1:ℝ) ≤ (s + δ - dist x c)/δ := by rw [le_div_iff₀ hδ]; linarith
  rw [min_eq_left h1]
  simp

theorem dist_lt_of_bump_pos {c : AddCircle (1:ℝ)} {s δ : ℝ} (hδ : 0 < δ) {x}
    (hx : 0 < bump c s δ x) : dist x c < s + δ := by
  unfold bump at hx
  by_contra h
  push_neg at h
  have h1 : (s + δ - dist x c)/δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  have h2 : min 1 ((s + δ - dist x c)/δ) ≤ 0 := le_trans (min_le_right _ _) h1
  simp [max_eq_left h2] at hx

theorem integrable_bump (c : AddCircle (1:ℝ)) (s δ : ℝ) :
    Integrable (bump c s δ) (volume : Measure (AddCircle (1:ℝ))) :=
  (continuous_bump c s δ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_indicator_closedBall (c : AddCircle (1:ℝ)) (r : ℝ) :
    Integrable ((closedBall c r).indicator (1 : AddCircle (1:ℝ) → ℝ)) volume := by
  refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
  exact integrableOn_const (measure_lt_top _ _).ne

theorem measureReal_closedBall (c : AddCircle (1:ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (AddCircle (1:ℝ))).real (closedBall c r) = min 1 (2*r) := by
  rw [measureReal_def, AddCircle.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]

/-- Upper bound for the integral of a bump function. -/
theorem integral_bump_le {c : AddCircle (1:ℝ)} {s δ : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s + δ) :
    ∫ t : AddCircle (1:ℝ), bump c s δ t ≤ min 1 (2*(s+δ)) := by
  have hle : ∀ x, bump c s δ x ≤ (closedBall c (s+δ)).indicator (1 : AddCircle (1:ℝ) → ℝ) x := by
    intro x
    by_cases hx : x ∈ closedBall c (s + δ)
    · rw [indicator_of_mem hx]; exact bump_le_one _ _ _ _
    · rw [indicator_of_notMem hx]
      by_contra h
      push_neg at h
      exact hx (by simpa [Metric.mem_closedBall] using (dist_lt_of_bump_pos hδ h).le)
  calc ∫ t : AddCircle (1:ℝ), bump c s δ t
      ≤ ∫ t : AddCircle (1:ℝ), (closedBall c (s+δ)).indicator (1 : AddCircle (1:ℝ) → ℝ) t :=
        integral_mono (integrable_bump c s δ) (integrable_indicator_closedBall c (s+δ)) hle
    _ = (volume : Measure (AddCircle (1:ℝ))).real (closedBall c (s+δ)) :=
        integral_indicator_one measurableSet_closedBall
    _ = min 1 (2*(s+δ)) := measureReal_closedBall c hs

/-- Lower bound for the integral of a bump function. -/
theorem le_integral_bump {c : AddCircle (1:ℝ)} {s δ : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) :
    min 1 (2*s) ≤ ∫ t : AddCircle (1:ℝ), bump c s δ t := by
  have hle : ∀ x, (closedBall c s).indicator (1 : AddCircle (1:ℝ) → ℝ) x ≤ bump c s δ x := by
    intro x
    by_cases hx : x ∈ closedBall c s
    · rw [indicator_of_mem hx, bump_eq_one hδ (Metric.mem_closedBall.1 hx)]
      exact le_rfl
    · rw [indicator_of_notMem hx]; exact bump_nonneg _ _ _ _
  calc min 1 (2*s) = (volume : Measure (AddCircle (1:ℝ))).real (closedBall c s) :=
        (measureReal_closedBall c hs).symm
    _ = ∫ t : AddCircle (1:ℝ), (closedBall c s).indicator (1 : AddCircle (1:ℝ) → ℝ) t :=
        (integral_indicator_one measurableSet_closedBall).symm
    _ ≤ ∫ t : AddCircle (1:ℝ), bump c s δ t :=
        integral_mono (integrable_indicator_closedBall c s) (integrable_bump c s δ) hle

theorem norm_coe_le_abs (x : ℝ) : ‖(x : AddCircle (1:ℝ))‖ ≤ |x| := by
  rw [AddCircle.norm_eq]
  simpa using round_le x 0

theorem dist_coe_le (x y : ℝ) :
    dist ((x : ℝ) : AddCircle (1:ℝ)) ((y : ℝ) : AddCircle (1:ℝ)) ≤ |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact norm_coe_le_abs _

/-- If a point of `[0,1)` is within circle-distance `(b-a)/2` of the midpoint of `[a,b]`,
then it lies in `[a, b)`. -/
theorem mem_Ico_of_dist_lt {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t < 1)
    (h : dist ((t : ℝ) : AddCircle (1:ℝ)) (((a+b)/2 : ℝ) : AddCircle (1:ℝ)) < (b-a)/2) :
    t ∈ Ico a b := by
  set u : ℝ := t - (a+b)/2 with hu
  have hdist : dist ((t : ℝ) : AddCircle (1:ℝ)) (((a+b)/2 : ℝ) : AddCircle (1:ℝ))
      = |u - (round u : ℝ)| := by
    rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
    simp [hu]
  rw [hdist] at h
  have habs : a < b := by
    rcases lt_or_eq_of_le hab with h1 | h1
    · exact h1
    · exact absurd h (by rw [← h1]; simp)
  have hr : (b-a)/2 ≤ 1/2 := by linarith
  have hu1 : -1 < u ∧ u < 1 := by constructor <;> simp only [hu] <;> linarith
  have habs' : |u - (round u : ℝ)| < 1/2 := lt_of_lt_of_le h hr
  rw [abs_lt] at habs'
  have hm2 : round u < 2 := by
    exact_mod_cast (show ((round u : ℤ):ℝ) < 2 by linarith [hu1.1, hu1.2])
  have hm2' : -2 < round u := by
    exact_mod_cast (show (-2:ℝ) < ((round u : ℤ):ℝ) by linarith [hu1.1, hu1.2])
  have hmem : round u = -1 ∨ round u = 0 ∨ round u = 1 := by omega
  rcases hmem with h1 | h1 | h1 <;> rw [h1] at h <;> push_cast at h <;> rw [abs_lt] at h <;>
    simp only [hu] at h <;> exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩

/-- A convenient criterion for convergence of a real sequence. -/
theorem tendsto_of_eventually_abs_sub_le {u : ℕ → ℝ} {L : ℝ}
    (h : ∀ ε > 0, ∀ᶠ N in atTop, |u N - L| ≤ ε) : Tendsto u atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (h (ε/2) (by positivity))
  refine ⟨N₀, fun N hN => ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hN₀ N hN) (by linarith)

/-- **Weyl's equidistribution theorem.** For irrational `α`, the sequence `n ↦ nα`
is equidistributed modulo one. -/
theorem equidistributed_irrational {α : ℝ} (hα : Irrational α) :
    EquidistributedMod1 (fun n : ℕ => n * α) := by
  intro a b ha hab hb
  refine tendsto_of_eventually_abs_sub_le (fun ε hε => ?_)
  set δ : ℝ := ε/4 with hδdef
  have hδ : 0 < δ := by positivity
  set c : AddCircle (1:ℝ) := (((a+b)/2 : ℝ) : AddCircle (1:ℝ)) with hc
  set r : ℝ := (b-a)/2 with hr
  have hr0 : 0 ≤ r := by linarith [hr]
  have hr1 : 2 * r ≤ 1 := by linarith [hr]
  have hcoe : ∀ n : ℕ, (((n:ℝ) * α : ℝ) : AddCircle (1:ℝ))
      = ((Int.fract ((n:ℝ)*α) : ℝ) : AddCircle (1:ℝ)) := fun n => (AddCircle.coe_fract _).symm
  have hterm_up : ∀ n : ℕ, (if Int.fract ((n:ℝ)*α) ∈ Ico a b then (1:ℝ) else 0)
      ≤ bump c r δ ((((n:ℝ) * α : ℝ)) : AddCircle (1:ℝ)) := by
    intro n
    by_cases hmem : Int.fract ((n:ℝ)*α) ∈ Ico a b
    · rw [if_pos hmem]
      refine le_of_eq (bump_eq_one hδ ?_).symm
      rw [hcoe n, hc]
      refine le_trans (dist_coe_le _ _) ?_
      rw [abs_le]
      obtain ⟨h1, h2⟩ := hmem
      constructor <;> linarith [hr]
    · rw [if_neg hmem]; exact bump_nonneg _ _ _ _
  have hterm_lo : ∀ n : ℕ, bump c (r-δ) δ ((((n:ℝ) * α : ℝ)) : AddCircle (1:ℝ))
      ≤ (if Int.fract ((n:ℝ)*α) ∈ Ico a b then (1:ℝ) else 0) := by
    intro n
    by_cases hmem : Int.fract ((n:ℝ)*α) ∈ Ico a b
    · rw [if_pos hmem]; exact bump_le_one _ _ _ _
    · rw [if_neg hmem]
      by_contra hcon
      push_neg at hcon
      have hd := dist_lt_of_bump_pos hδ hcon
      rw [hcoe n, hc] at hd
      have hd' : dist ((Int.fract ((n:ℝ)*α) : ℝ) : AddCircle (1:ℝ))
          (((a+b)/2 : ℝ) : AddCircle (1:ℝ)) < (b-a)/2 := by simpa [hr] using hd
      exact hmem (mem_Ico_of_dist_lt ha hab hb (Int.fract_nonneg _) (Int.fract_lt_one _) hd')
  have hcard : ∀ N : ℕ,
      (((range N).filter fun n : ℕ => Int.fract ((n:ℝ)*α) ∈ Ico a b).card : ℝ)
        = ∑ n ∈ range N, (if Int.fract ((n:ℝ)*α) ∈ Ico a b then (1:ℝ) else 0) := by
    intro N
    rw [card_filter]
    push_cast
    rfl
  -- the two comparison sequences
  set U : ℕ → ℝ :=
    fun N => (∑ n ∈ range N, bump c r δ ((((n:ℝ) * α : ℝ)) : AddCircle (1:ℝ)))/(N:ℝ) with hU
  set L : ℕ → ℝ :=
    fun N => (∑ n ∈ range N, bump c (r-δ) δ ((((n:ℝ) * α : ℝ)) : AddCircle (1:ℝ)))/(N:ℝ) with hL
  have hUlim : Tendsto U atTop (𝓝 (∫ t : AddCircle (1:ℝ), bump c r δ t)) :=
    avg_tendsto_continuous_real hα _ (continuous_bump c r δ)
  have hLlim : Tendsto L atTop (𝓝 (∫ t : AddCircle (1:ℝ), bump c (r-δ) δ t)) :=
    avg_tendsto_continuous_real hα _ (continuous_bump c (r-δ) δ)
  have hUint : (∫ t : AddCircle (1:ℝ), bump c r δ t) ≤ (b - a) + 2*δ := by
    refine le_trans (integral_bump_le hδ (by linarith)) ?_
    refine le_trans (min_le_right _ _) ?_
    linarith [hr]
  have hLint : (b - a) - 2*δ ≤ ∫ t : AddCircle (1:ℝ), bump c (r-δ) δ t := by
    rcases le_or_gt δ r with hcase | hcase
    · refine le_trans ?_ (le_integral_bump hδ (by linarith))
      rw [le_min_iff]
      constructor
      · linarith [hr]
      · linarith [hr]
    · have hnonneg : 0 ≤ ∫ t : AddCircle (1:ℝ), bump c (r-δ) δ t :=
        integral_nonneg (fun t => bump_nonneg _ _ _ _)
      refine le_trans ?_ hnonneg
      linarith [hr]
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hUlim δ hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hLlim δ hδ
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with N hN
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) hN
  have hUN := hN₁ N hN1
  have hLN := hN₂ N hN2
  rw [Real.dist_eq, abs_lt] at hUN hLN
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hup : (((range N).filter fun n : ℕ => Int.fract ((n:ℝ)*α) ∈ Ico a b).card : ℝ)/(N:ℝ)
      ≤ U N := by
    rw [hcard N, hU]
    exact div_le_div_of_nonneg_right (sum_le_sum fun n _ => hterm_up n) hNnn
  have hlo : L N ≤ (((range N).filter fun n : ℕ => Int.fract ((n:ℝ)*α) ∈ Ico a b).card : ℝ)/(N:ℝ) := by
    rw [hcard N, hL]
    exact div_le_div_of_nonneg_right (sum_le_sum fun n _ => hterm_lo n) hNnn
  rw [abs_le]
  constructor
  · have : (b - a) - 3*δ ≤ L N := by linarith [hLN.1, hLint]
    have hδε : 3*δ ≤ ε := by rw [hδdef]; linarith
    linarith
  · have : U N ≤ (b - a) + 3*δ := by linarith [hUN.2, hUint]
    have hδε : 3*δ ≤ ε := by rw [hδdef]; linarith
    linarith

/-! ### Step 4: from intervals to monotone functions -/

/-- Membership in a grid interval is detected by the floor function. -/
theorem grid_floor_iff {m : ℕ} (hm : 0 < m) {t : ℝ} (ht0 : 0 ≤ t) (j : ℕ) :
    t ∈ Ico ((j:ℝ)/m) (((j:ℝ)+1)/m) ↔ ⌊(m:ℝ)*t⌋₊ = j := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rintro ⟨h1, h2⟩
    rw [div_le_iff₀ hmpos] at h1
    rw [lt_div_iff₀ hmpos] at h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    constructor
    · rw [div_le_iff₀ hmpos]; linarith
    · rw [lt_div_iff₀ hmpos]; linarith

/-- A step function built on the uniform grid takes the value indexed by the floor. -/
theorem sum_grid_indicator {m : ℕ} (hm : 0 < m) (cf : ℕ → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∑ i ∈ range m, cf i * (if t ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0)
      = cf ⌊(m:ℝ)*t⌋₊ := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hlt : ⌊(m:ℝ)*t⌋₊ < m := by
    refine (Nat.floor_lt' (by omega)).2 ?_
    calc (m:ℝ)*t < m*1 := by exact mul_lt_mul_of_pos_left ht1 hmpos
      _ = m := by ring
  rw [Finset.sum_eq_single ⌊(m:ℝ)*t⌋₊]
  · rw [if_pos ((grid_floor_iff hm ht0 _).2 rfl), mul_one]
  · intro j _ hj
    rw [if_neg (fun hmem => hj ((grid_floor_iff hm ht0 j).1 hmem).symm), mul_zero]
  · intro h
    exact absurd (mem_range.2 hlt) h

/-- Averages of grid step functions along an equidistributed sequence. -/
theorem avg_step_tendsto {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {m : ℕ} (hm : 0 < m)
    (cf : ℕ → ℝ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, ∑ i ∈ range m,
        cf i * (if Int.fract (x n) ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0)) / (N:ℝ))
      atTop (𝓝 (∑ i ∈ range m, cf i / m)) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have key : ∀ N : ℕ, (∑ n ∈ range N, ∑ i ∈ range m,
      cf i * (if Int.fract (x n) ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0)) / (N:ℝ)
      = ∑ i ∈ range m, cf i *
        ((((range N).filter fun n =>
            Int.fract (x n) ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m)).card : ℝ)/(N:ℝ)) := by
    intro N
    rw [Finset.sum_comm, Finset.sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, card_filter]
    push_cast
    rw [mul_div_assoc]
  simp only [key]
  have heq : ∑ i ∈ range m, cf i / m = ∑ i ∈ range m, cf i * (((i:ℝ)+1)/m - (i:ℝ)/m) := by
    refine sum_congr rfl fun i _ => ?_
    rw [show ((i:ℝ)+1)/m - (i:ℝ)/m = 1/m by ring, mul_one_div]
  rw [heq]
  refine tendsto_finset_sum _ fun i hi => ?_
  refine Tendsto.const_mul _ ?_
  refine hx ((i:ℝ)/m) (((i:ℝ)+1)/m) (by positivity) (by gcongr; linarith) ?_
  rw [div_le_one hmpos]
  have h1 : i < m := mem_range.1 hi
  have : (i:ℝ) + 1 ≤ m := by exact_mod_cast h1
  linarith

/-- The upper grid step function dominates a monotone function. -/
theorem le_step_upper {f : ℝ → ℝ} (hf : MonotoneOn f (Icc 0 1)) {m : ℕ} (hm : 0 < m) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    f t ≤ ∑ i ∈ range m, f (((i:ℝ)+1)/m) * (if t ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  rw [sum_grid_indicator hm (fun i => f (((i:ℝ)+1)/m)) ht0 ht1]
  have hlt : ⌊(m:ℝ)*t⌋₊ < m := by
    refine (Nat.floor_lt' (by omega)).2 ?_
    calc (m:ℝ)*t < m*1 := by exact mul_lt_mul_of_pos_left ht1 hmpos
      _ = m := by ring
  have hle1 : ((⌊(m:ℝ)*t⌋₊ : ℝ) + 1)/m ≤ 1 := by
    rw [div_le_one hmpos]
    have : (⌊(m:ℝ)*t⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hlt
    linarith
  have hmem : ((⌊(m:ℝ)*t⌋₊ : ℝ) + 1)/m ∈ Icc (0:ℝ) 1 := ⟨by positivity, hle1⟩
  refine hf ⟨ht0, ht1.le⟩ hmem ?_
  rw [le_div_iff₀ hmpos]
  have := Nat.lt_floor_add_one ((m:ℝ)*t)
  linarith [this]

/-- The lower grid step function is dominated by a monotone function. -/
theorem step_lower_le {f : ℝ → ℝ} (hf : MonotoneOn f (Icc 0 1)) {m : ℕ} (hm : 0 < m) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∑ i ∈ range m, f ((i:ℝ)/m) * (if t ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0) ≤ f t := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  rw [sum_grid_indicator hm (fun i => f ((i:ℝ)/m)) ht0 ht1]
  have hfl : ((⌊(m:ℝ)*t⌋₊ : ℝ))/m ≤ t := by
    rw [div_le_iff₀ hmpos]
    have := Nat.floor_le (a := (m:ℝ)*t) (by positivity)
    linarith [this]
  refine hf ⟨by positivity, le_trans hfl ht1.le⟩ ⟨ht0, ht1.le⟩ hfl

/-- Lower Riemann sums of a monotone function underestimate its integral. -/
theorem riemann_lower {f : ℝ → ℝ} (hf : MonotoneOn f (Icc 0 1)) {m : ℕ} (hm : 0 < m) :
    ∑ i ∈ range m, f ((i:ℝ)/m) / m ≤ ∫ t in (0:ℝ)..1, f t := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  set a : ℕ → ℝ := fun i => (i:ℝ)/m with ha
  have hsub : ∀ i ≤ m, a i ∈ Icc (0:ℝ) 1 := by
    intro i hi
    refine ⟨by positivity, ?_⟩
    rw [ha]; simp only; rw [div_le_one hmpos]; exact_mod_cast hi
  have hmono : ∀ i < m, MonotoneOn f (uIcc (a i) (a (i+1))) := by
    intro i hi
    refine hf.mono ?_
    rw [Set.uIcc_of_le (by rw [ha]; simp only; gcongr; simp)]
    intro y hy
    exact ⟨le_trans (hsub i (le_of_lt hi)).1 hy.1, le_trans hy.2 (hsub (i+1) hi).2⟩
  have hint : ∀ i < m, IntervalIntegrable f volume (a i) (a (i+1)) :=
    fun i hi => (hmono i hi).intervalIntegrable
  have hsplit : ∑ i ∈ range m, ∫ t in (a i)..(a (i+1)), f t = ∫ t in (a 0)..(a m), f t :=
    intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [ha]
  have ham : a m = 1 := by rw [ha]; field_simp
  rw [ha0, ham] at hsplit
  rw [← hsplit]
  refine sum_le_sum fun i hi => ?_
  have hi' : i < m := mem_range.1 hi
  have hle : a i ≤ a (i+1) := by rw [ha]; simp only; gcongr; simp
  have hcomp : ∫ _t in (a i)..(a (i+1)), f (a i) ≤ ∫ t in (a i)..(a (i+1)), f t := by
    refine intervalIntegral.integral_mono_on hle (_root_.intervalIntegrable_const) (hint i hi') ?_
    intro y hy
    exact hf (hsub i hi'.le) ⟨le_trans (hsub i hi'.le).1 hy.1, le_trans hy.2 (hsub (i+1) hi').2⟩ hy.1
  rw [intervalIntegral.integral_const, smul_eq_mul] at hcomp
  have hlen : a (i+1) - a i = 1/m := by rw [ha]; push_cast; field_simp; ring
  rw [hlen] at hcomp
  calc f ((i:ℝ)/m)/m = 1/m * f (a i) := by rw [ha]; ring
    _ ≤ _ := hcomp

/-- Upper Riemann sums of a monotone function overestimate its integral. -/
theorem riemann_upper {f : ℝ → ℝ} (hf : MonotoneOn f (Icc 0 1)) {m : ℕ} (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, f t) ≤ ∑ i ∈ range m, f (((i:ℝ)+1)/m) / m := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  set a : ℕ → ℝ := fun i => (i:ℝ)/m with ha
  have hsub : ∀ i ≤ m, a i ∈ Icc (0:ℝ) 1 := by
    intro i hi
    refine ⟨by positivity, ?_⟩
    rw [ha]; simp only; rw [div_le_one hmpos]; exact_mod_cast hi
  have hmono : ∀ i < m, MonotoneOn f (uIcc (a i) (a (i+1))) := by
    intro i hi
    refine hf.mono ?_
    rw [Set.uIcc_of_le (by rw [ha]; simp only; gcongr; simp)]
    intro y hy
    exact ⟨le_trans (hsub i (le_of_lt hi)).1 hy.1, le_trans hy.2 (hsub (i+1) hi).2⟩
  have hint : ∀ i < m, IntervalIntegrable f volume (a i) (a (i+1)) :=
    fun i hi => (hmono i hi).intervalIntegrable
  have hsplit : ∑ i ∈ range m, ∫ t in (a i)..(a (i+1)), f t = ∫ t in (a 0)..(a m), f t :=
    intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [ha]
  have ham : a m = 1 := by rw [ha]; field_simp
  rw [ha0, ham] at hsplit
  rw [← hsplit]
  refine sum_le_sum fun i hi => ?_
  have hi' : i < m := mem_range.1 hi
  have hle : a i ≤ a (i+1) := by rw [ha]; simp only; gcongr; simp
  have hcomp : ∫ t in (a i)..(a (i+1)), f t ≤ ∫ _t in (a i)..(a (i+1)), f (a (i+1)) := by
    refine intervalIntegral.integral_mono_on hle (hint i hi') (_root_.intervalIntegrable_const) ?_
    intro y hy
    exact hf ⟨le_trans (hsub i hi'.le).1 hy.1, le_trans hy.2 (hsub (i+1) hi').2⟩
      (hsub (i+1) hi') hy.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hcomp
  have hlen : a (i+1) - a i = 1/m := by rw [ha]; push_cast; field_simp; ring
  rw [hlen] at hcomp
  calc ∫ t in (a i)..(a (i+1)), f t ≤  1/m * f (a (i+1)) := hcomp
    _ = f (((i:ℝ)+1)/m)/m := by rw [ha]; push_cast; ring

/-- The difference between the upper and the lower Riemann sums is `(f 1 - f 0)/m`. -/
theorem riemann_diff (f : ℝ → ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ i ∈ range m, f (((i:ℝ)+1)/m) / m) - (∑ i ∈ range m, f ((i:ℝ)/m) / m)
      = (f 1 - f 0)/m := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  rw [← Finset.sum_sub_distrib]
  have : ∀ i ∈ range m, f (((i:ℝ)+1)/m) / m - f ((i:ℝ)/m) / m
      = (fun j : ℕ => f ((j:ℝ)/m)/m) (i+1) - (fun j : ℕ => f ((j:ℝ)/m)/m) i := by
    intro i _
    dsimp only
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun j : ℕ => f ((j:ℝ)/m)/m)]
  rw [Nat.cast_zero, zero_div]
  have h1 : (m:ℝ)/m = 1 := by field_simp
  rw [h1]
  ring

/-- **Equidistribution reduction for monotone functions.** If `x` is equidistributed mod one and
`f` is monotone on `[0,1]`, then the Cesàro averages of `f` along the fractional parts of `x`
converge to `∫₀¹ f`. -/
theorem monotoneOn_avg_tendsto {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {f : ℝ → ℝ}
    (hf : MonotoneOn f (Icc 0 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f (Int.fract (x n))) / (N:ℝ)) atTop
      (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  refine tendsto_of_eventually_abs_sub_le (fun ε hε => ?_)
  set I : ℝ := ∫ t in (0:ℝ)..1, f t with hI
  set V : ℝ := f 1 - f 0 with hV
  have hV0 : 0 ≤ V := sub_nonneg.2 (hf ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one)
  obtain ⟨m, hmgt⟩ := exists_nat_gt (4*(V+1)/ε)
  have hpos' : 0 < 4*(V+1)/ε := by positivity
  have hmpos : (0:ℝ) < m := lt_trans hpos' hmgt
  have hmpos0 : 0 < m := by exact_mod_cast hmpos
  have hVm : V/m ≤ ε/4 := by
    rw [div_le_div_iff₀ hmpos (by norm_num)]
    rw [div_lt_iff₀ hε] at hmgt
    nlinarith
  set SU : ℝ := ∑ i ∈ range m, f (((i:ℝ)+1)/m) / m with hSU
  set SL : ℝ := ∑ i ∈ range m, f ((i:ℝ)/m) / m with hSL
  have hdiff : SU - SL = V/m := riemann_diff f hmpos0
  have hSLI : SL ≤ I := riemann_lower hf hmpos0
  have hISU : I ≤ SU := riemann_upper hf hmpos0
  set Uf : ℕ → ℝ := fun N => (∑ n ∈ range N, ∑ i ∈ range m,
      f (((i:ℝ)+1)/m) * (if Int.fract (x n) ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0))/(N:ℝ)
    with hUf
  set Lf : ℕ → ℝ := fun N => (∑ n ∈ range N, ∑ i ∈ range m,
      f ((i:ℝ)/m) * (if Int.fract (x n) ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then 1 else 0))/(N:ℝ)
    with hLf
  have hUlim : Tendsto Uf atTop (𝓝 SU) := avg_step_tendsto hx hmpos0 _
  have hLlim : Tendsto Lf atTop (𝓝 SL) := avg_step_tendsto hx hmpos0 _
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hUlim (ε/4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hLlim (ε/4) (by positivity)
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with N hN
  have hUN := hN₁ N (le_trans (le_max_left _ _) hN)
  have hLN := hN₂ N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at hUN hLN
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hup : (∑ n ∈ range N, f (Int.fract (x n))) / (N:ℝ) ≤ Uf N := by
    rw [hUf]
    exact div_le_div_of_nonneg_right
      (sum_le_sum fun n _ =>
        le_step_upper hf hmpos0 (Int.fract_nonneg _) (Int.fract_lt_one _)) hNnn
  have hlo : Lf N ≤ (∑ n ∈ range N, f (Int.fract (x n))) / (N:ℝ) := by
    rw [hLf]
    exact div_le_div_of_nonneg_right
      (sum_le_sum fun n _ =>
        step_lower_le hf hmpos0 (Int.fract_nonneg _) (Int.fract_lt_one _)) hNnn
  rw [abs_le]
  exact ⟨by linarith [hLN.1, hdiff, hSLI, hVm], by linarith [hUN.2, hdiff, hISU, hVm]⟩

/-! ### Step 5: the bounded-variation reduction -/

/-- **Equidistribution reduction for functions of bounded variation.** -/
theorem boundedVariationOn_avg_tendsto {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Icc 0 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f (Int.fract (x n))) / (N:ℝ)) atTop
      (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hpi : IntervalIntegrable p volume 0 1 := by
    refine MonotoneOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le zero_le_one]
  have hqi : IntervalIntegrable q volume 0 1 := by
    refine MonotoneOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le zero_le_one]
  have hInt : (∫ t in (0:ℝ)..1, f t) = (∫ t in (0:ℝ)..1, p t) - ∫ t in (0:ℝ)..1, q t := by
    rw [← intervalIntegral.integral_sub hpi hqi]
    congr 1
  rw [hInt]
  refine ((monotoneOn_avg_tendsto hx hp).sub (monotoneOn_avg_tendsto hx hq)).congr (fun N => ?_)
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun n _ => by simp [hpq]

/-- **Main theorem.** For an irrational `α` and a function `f` of bounded variation on `[0,1]`
with nonzero integral, the total sum `∑_{n < N} f (fract (nα))` divided by the main term
`N · ∫₀¹ f` tends to `1`. -/
theorem total_over_main_tendsto {α : ℝ} (hα : Irrational α) {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Icc 0 1)) (hI : (∫ t in (0:ℝ)..1, f t) ≠ 0) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f (Int.fract (n * α)))
        / ((N:ℝ) * ∫ t in (0:ℝ)..1, f t)) atTop (𝓝 1) := by
  have h := boundedVariationOn_avg_tendsto (equidistributed_irrational hα) hf
  have h2 := h.div_const (∫ t in (0:ℝ)..1, f t)
  rw [div_self hI] at h2
  exact h2.congr (fun N => by rw [div_div])

/-- The same conclusion for a monotone `f`, which is a special case of a function of
bounded variation. -/
theorem total_over_main_tendsto_of_monotoneOn {α : ℝ} (hα : Irrational α) {f : ℝ → ℝ}
    (hf : MonotoneOn f (Icc 0 1)) (hI : (∫ t in (0:ℝ)..1, f t) ≠ 0) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f (Int.fract (n * α)))
        / ((N:ℝ) * ∫ t in (0:ℝ)..1, f t)) atTop (𝓝 1) := by
  have h := monotoneOn_avg_tendsto (equidistributed_irrational hα) hf
  have h2 := h.div_const (∫ t in (0:ℝ)..1, f t)
  rw [div_self hI] at h2
  exact h2.congr (fun N => by rw [div_div])

/-- A concrete instance: the fractional parts of `nα` have average `1/2`. -/
theorem total_over_main_tendsto_fract {α : ℝ} (hα : Irrational α) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, Int.fract ((n:ℝ) * α)) / ((N:ℝ) * (1/2)))
      atTop (𝓝 1) := by
  have hint : (∫ t in (0:ℝ)..1, t) = 1/2 := by simp [integral_id]
  have h := total_over_main_tendsto_of_monotoneOn hα (f := fun t : ℝ => t)
    (fun a _ b _ hab => hab) (by rw [hint]; norm_num)
  rwa [hint] at h

end

end Brockian.EquidistributionBVReduction

