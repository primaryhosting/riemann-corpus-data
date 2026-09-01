import Brockian.Equidistribution

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
# Weyl equidistribution

This file develops, from scratch, Weyl's criterion for equidistribution modulo one and applies
it to the sequence `n ↦ n * α` for irrational `α`.

The main statement is `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`, which
is *conditional* on the asymptotic vanishing of the Weyl exponential sums, and its unconditional
consequence `Brockian.Equidistribution.equidistributedMod1_natMul_irrational`.
-/

namespace Brockian.Equidistribution

open MeasureTheory Filter Finset Complex Topology Metric

open scoped Real

noncomputable section

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/
def countIn (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card

/-- A sequence of reals is equidistributed modulo one when, for every subinterval `[a, b)` of
`[0, 1]`, the proportion of the first `N` terms whose fractional part lies in `[a, b)` tends to
the length `b - a` of the interval. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (countIn x a b N : ℝ) / N) atTop (𝓝 (b - a))

/-- The average of a complex valued function on the circle along the first `N` terms of the
sequence `x`. -/
def cavg (x : ℕ → ℝ) (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (x n)

/-- The average of a real valued function on the circle along the first `N` terms of the
sequence `x`. -/
def ravg (x : ℕ → ℝ) (f : AddCircle (1 : ℝ) → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (x n)

/-- Weyl's hypothesis: all nontrivial exponential sums of the sequence have vanishing averages. -/
def WeylCondition (x : ℕ → ℝ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → Tendsto (cavg x (fourier h)) atTop (𝓝 0)

instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨UnitAddCircle.measure_univ⟩

/-! ### Basic facts about averages and integrals on the circle -/

theorem integrable_of_continuousMap (f : C(AddCircle (1 : ℝ), ℂ)) :
    Integrable (fun z => f z) volume :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem integrable_of_continuousMap_real (f : C(AddCircle (1 : ℝ), ℝ)) :
    Integrable (fun z => f z) volume :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem norm_integral_le_norm (f : C(AddCircle (1 : ℝ), ℂ)) : ‖∫ z, f z‖ ≤ ‖f‖ := by
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (AddCircle (1 : ℝ))))
    (C := ‖f‖) (f := fun z => f z) (.of_forall fun z => f.norm_coe_le_norm z)
  simpa using this

theorem norm_cavg_le (x : ℕ → ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    ‖cavg x f N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cavg, norm_nonneg]
  · rw [cavg, norm_mul, norm_inv]
    have h1 : ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ N * ‖f‖ :=
      calc ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ ∑ n ∈ Finset.range N, ‖f (x n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := Finset.sum_le_sum fun n _ => f.norm_coe_le_norm _
        _ = N * ‖f‖ := by simp
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Complex.norm_natCast, inv_mul_le_iff₀ hNpos]
    exact h1

theorem cavg_sub (x : ℕ → ℝ) (f g : AddCircle (1 : ℝ) → ℂ) (N : ℕ) :
    cavg x (f - g) N = cavg x f N - cavg x g N := by
  simp [cavg, Finset.sum_sub_distrib, mul_sub]

/-! ### Weyl's criterion, step 1: characters -/

theorem integral_fourier_eq_zero {h : ℤ} (hh : h ≠ 0) :
    (∫ z : AddCircle (1 : ℝ), fourier h z) = 0 := by
  rw [← AddCircle.intervalIntegral_preimage 1 0]
  simp only [fourier_coe_apply]
  rw [intervalIntegral.integral_congr (g := fun x : ℝ => Complex.exp (2 * π * I * h * x))
    (fun x _ => by push_cast; ring_nf)]
  rw [integral_exp_mul_complex (by simp [Real.pi_ne_zero, hh, Complex.ext_iff])]
  norm_num
  left
  rw [sub_eq_zero, Complex.exp_eq_one_iff]
  exact ⟨h, by ring⟩

theorem cavg_tendsto_of_mem_span (x : ℕ → ℝ) (hx : WeylCondition x)
    {f : C(AddCircle (1 : ℝ), ℂ)} (hf : f ∈ Submodule.span ℂ (Set.range (@fourier 1))) :
    Tendsto (cavg x f) atTop (𝓝 (∫ z, f z)) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨h, rfl⟩ := hg
      rcases eq_or_ne h 0 with rfl | hh
      · have hint : (∫ z : AddCircle (1 : ℝ), (fourier (0 : ℤ)) z) = 1 := by simp
        rw [hint]
        refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)))
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        simp [cavg, inv_mul_cancel₀ hN0]
      · rw [integral_fourier_eq_zero hh]
        exact hx h hh
  | zero =>
      refine Tendsto.congr (f₁ := fun _ => (0 : ℂ)) (fun N => by simp [cavg]) ?_
      simp only [ContinuousMap.zero_apply, integral_zero]
      exact tendsto_const_nhds
  | add g1 g2 _ _ ih1 ih2 =>
      refine Tendsto.congr (f₁ := fun N => cavg x g1 N + cavg x g2 N)
        (fun N => by simp [cavg, Finset.sum_add_distrib, mul_add]) ?_
      simp only [ContinuousMap.add_apply]
      rw [integral_add (integrable_of_continuousMap g1) (integrable_of_continuousMap g2)]
      exact ih1.add ih2
  | smul c g _ ih =>
      refine Tendsto.congr (f₁ := fun N => c * cavg x g N)
        (fun N => by simp [cavg, Finset.mul_sum, mul_left_comm]) ?_
      simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      exact ih.const_mul c

/-! ### Weyl's criterion, step 2: all continuous functions -/

theorem cavg_tendsto_integral (x : ℕ → ℝ) (hx : WeylCondition x) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (cavg x f) atTop (𝓝 (∫ z, f z)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hdense : f ∈
      closure ((Submodule.span ℂ (Set.range (@fourier 1))) : Set C(AddCircle (1 : ℝ), ℂ)) := by
    have : f ∈ (Submodule.span ℂ (Set.range (@fourier 1))).topologicalClosure := by
      rw [span_fourier_closure_eq_top]; trivial
    exact this
  obtain ⟨p, hp_mem, hp⟩ := Metric.mem_closure_iff.1 hdense (δ / 4) (by linarith)
  have hnorm : ‖f - p‖ < δ / 4 := by rwa [dist_eq_norm] at hp
  have h1 := cavg_tendsto_of_mem_span x hx hp_mem
  rw [Metric.tendsto_atTop] at h1
  obtain ⟨M, hM⟩ := h1 (δ / 4) (by linarith)
  refine ⟨M, fun N hN => ?_⟩
  have e1 : dist (cavg x f N) (cavg x p N) ≤ δ / 4 := by
    rw [dist_eq_norm]
    have := norm_cavg_le x (f - p) N
    rw [show ⇑(f - p) = (⇑f - ⇑p) from rfl, cavg_sub] at this
    linarith
  have e2 : dist (∫ z, p z) (∫ z, f z) ≤ δ / 4 := by
    rw [dist_eq_norm, norm_sub_rev]
    have := norm_integral_le_norm (f - p)
    rw [show (∫ z, (f - p) z) = (∫ z, f z) - ∫ z, p z from by
      simp only [ContinuousMap.sub_apply]
      exact integral_sub (integrable_of_continuousMap f) (integrable_of_continuousMap p)] at this
    linarith
  have e3 : dist (cavg x p N) (∫ z, p z) < δ / 4 := hM N hN
  calc dist (cavg x f N) (∫ z, f z)
      ≤ dist (cavg x f N) (cavg x p N) + dist (cavg x p N) (∫ z, p z)
        + dist (∫ z, p z) (∫ z, f z) := dist_triangle4 _ _ _ _
    _ < δ := by linarith

theorem ravg_tendsto_integral (x : ℕ → ℝ) (hx : WeylCondition x) (f : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (ravg x f) atTop (𝓝 (∫ z, f z)) := by
  set F : C(AddCircle (1 : ℝ), ℂ) := ⟨fun z => (f z : ℂ), by fun_prop⟩ with hF
  have hc := cavg_tendsto_integral x hx F
  have hint : (∫ z, F z) = ((∫ z, f z : ℝ) : ℂ) := by
    simp only [hF, ContinuousMap.coe_mk]
    exact integral_ofReal
  have hcavg : ∀ N, cavg x F N = ((ravg x f N : ℝ) : ℂ) := by
    intro N
    simp [cavg, ravg, hF]
  rw [hint] at hc
  exact Filter.tendsto_ofReal_iff.mp (hc.congr hcavg)

/-! ### Weyl's criterion, step 3: from continuous functions to intervals -/

/-- A continuous trapezoidal bump on the circle: it equals `1` on the closed arc of radius
`s - ep` around `c`, and vanishes outside the open arc of radius `s`. -/
def bump (c s ep : ℝ) : C(AddCircle (1 : ℝ), ℝ) :=
  ⟨fun z => min 1 (max 0 ((s - ‖z - (c : AddCircle (1 : ℝ))‖) / ep)), by fun_prop⟩

theorem bump_nonneg (c s ep : ℝ) (z : AddCircle (1 : ℝ)) : 0 ≤ bump c s ep z :=
  le_min zero_le_one (le_max_left _ _)

theorem bump_le_one (c s ep : ℝ) (z : AddCircle (1 : ℝ)) : bump c s ep z ≤ 1 :=
  min_le_left _ _

theorem bump_eq_one (c s ep : ℝ) (hep : 0 < ep) {z : AddCircle (1 : ℝ)}
    (hz : ‖z - (c : AddCircle (1 : ℝ))‖ ≤ s - ep) : bump c s ep z = 1 := by
  have h1 : 1 ≤ (s - ‖z - (c : AddCircle (1 : ℝ))‖) / ep := by
    rw [le_div_iff₀ hep]; linarith
  simp only [bump, ContinuousMap.coe_mk]
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ (s - ‖z - (c : AddCircle (1 : ℝ))‖) / ep),
    min_eq_left h1]

theorem bump_eq_zero (c s ep : ℝ) (hep : 0 < ep) {z : AddCircle (1 : ℝ)}
    (hz : s ≤ ‖z - (c : AddCircle (1 : ℝ))‖) : bump c s ep z = 0 := by
  have h1 : (s - ‖z - (c : AddCircle (1 : ℝ))‖) / ep ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hep.le
  simp only [bump, ContinuousMap.coe_mk]
  rw [max_eq_left h1, min_eq_right zero_le_one]

/-- The integral of `bump c s ep` over the circle, computed as an integral over the interval
of length one centred at `c`. -/
theorem integral_bump_eq (c s ep : ℝ) :
    (∫ z, bump c s ep z) = ∫ t in (c - 1 / 2)..(c + 1 / 2), min 1 (max 0 ((s - |t - c|) / ep)) := by
  rw [← AddCircle.intervalIntegral_preimage 1 (c - 1 / 2), show c - 1 / 2 + 1 = c + 1 / 2 by ring]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (by linarith)] at ht
  obtain ⟨h1, h2⟩ := ht
  have habs : |t - c| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one, abs_le]; constructor <;> linarith
  simp only [bump, ContinuousMap.coe_mk]
  rw [← QuotientAddGroup.mk_sub, (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).2 habs]

theorem integral_bump_le (c s ep : ℝ) (hep : 0 < ep) (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) :
    (∫ z, bump c s ep z) ≤ 2 * s := by
  rw [integral_bump_eq]
  set ψ : ℝ → ℝ := fun t => min 1 (max 0 ((s - |t - c|) / ep)) with hψ
  have hcont : Continuous ψ := by fun_prop
  have hii : ∀ u v : ℝ, IntervalIntegrable ψ volume u v := fun u v => hcont.intervalIntegrable u v
  have hzero : ∀ t : ℝ, s ≤ |t - c| → ψ t = 0 := by
    intro t ht
    have : (s - |t - c|) / ep ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hep.le
    simp [hψ, max_eq_left this]
  have h1 : (∫ t in (c - 1 / 2)..(c - s), ψ t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact hzero t (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2])
  have h3 : (∫ t in (c + s)..(c + 1 / 2), ψ t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact hzero t (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.1])
  have h2 : (∫ t in (c - s)..(c + s), ψ t) ≤ 2 * s := by
    have := intervalIntegral.integral_mono_on (f := ψ) (g := fun _ => (1 : ℝ)) (a := c - s)
      (b := c + s) (by linarith) (hii _ _) (by simp [intervalIntegrable_const])
      (fun t _ => min_le_left _ _)
    simpa [mul_comm] using this.trans_eq (by simp; ring)
  have hsplit : (∫ t in (c - 1 / 2)..(c - s), ψ t) + (∫ t in (c - s)..(c + s), ψ t)
      + (∫ t in (c + s)..(c + 1 / 2), ψ t) = ∫ t in (c - 1 / 2)..(c + 1 / 2), ψ t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
  rw [← hsplit, h1, h3]
  linarith

theorem le_integral_bump (c s ep : ℝ) (hep : 0 < ep) (hs' : s ≤ 1 / 2) :
    2 * (s - ep) ≤ ∫ z, bump c s ep z := by
  rw [integral_bump_eq]
  set ψ : ℝ → ℝ := fun t => min 1 (max 0 ((s - |t - c|) / ep)) with hψ
  have hcont : Continuous ψ := by fun_prop
  have hii : ∀ u v : ℝ, IntervalIntegrable ψ volume u v := fun u v => hcont.intervalIntegrable u v
  have hnonneg : ∀ t, 0 ≤ ψ t := fun t => le_min zero_le_one (le_max_left _ _)
  rcases lt_or_ge (s - ep) 0 with hneg | hpos
  · have : (0 : ℝ) ≤ ∫ t in (c - 1 / 2)..(c + 1 / 2), ψ t :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => hnonneg t
    linarith
  · set u := s - ep with hu
    have hu2 : u ≤ 1 / 2 := by linarith
    have hone : ∀ t : ℝ, |t - c| ≤ u → ψ t = 1 := by
      intro t ht
      have h1 : 1 ≤ (s - |t - c|) / ep := by rw [le_div_iff₀ hep]; linarith
      simp [hψ, max_eq_right (by linarith : (0 : ℝ) ≤ (s - |t - c|) / ep), min_eq_left h1]
    have h2 : (∫ t in (c - u)..(c + u), ψ t) = 2 * u := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
      · simp; ring
      · intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact hone t (by rw [abs_le]; constructor <;> [linarith [ht.1]; linarith [ht.2]])
    have h1 : (0 : ℝ) ≤ ∫ t in (c - 1 / 2)..(c - u), ψ t :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => hnonneg t
    have h3 : (0 : ℝ) ≤ ∫ t in (c + u)..(c + 1 / 2), ψ t :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => hnonneg t
    have hsplit : (∫ t in (c - 1 / 2)..(c - u), ψ t) + (∫ t in (c - u)..(c + u), ψ t)
        + (∫ t in (c + u)..(c + 1 / 2), ψ t) = ∫ t in (c - 1 / 2)..(c + 1 / 2), ψ t := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
        intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
    rw [← hsplit, h2]
    linarith

/-! ### From membership of arcs to fractional parts -/

theorem norm_le_of_fract_mem {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hy : Int.fract y ∈ Set.Ico a b) :
    ‖((y : AddCircle (1 : ℝ)) - (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)))‖ ≤ (b - a) / 2 := by
  obtain ⟨hy1, hy2⟩ := hy
  have hfr : ((Int.fract y : ℝ) : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) := by
    rw [Int.fract]; simp
  rw [← hfr, ← QuotientAddGroup.mk_sub]
  have habs : |Int.fract y - (a + b) / 2| ≤ (b - a) / 2 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |Int.fract y - (a + b) / 2| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one]
    linarith [Int.fract_nonneg y, Int.fract_lt_one y]
  rw [(AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).2 h2]
  exact habs

theorem fract_mem_of_norm_lt {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hy : ‖((y : AddCircle (1 : ℝ)) - (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)))‖ < (b - a) / 2) :
    Int.fract y ∈ Set.Ico a b := by
  rw [← QuotientAddGroup.mk_sub, AddCircle.norm_eq] at hy
  set k : ℤ := round ((1 : ℝ)⁻¹ * (y - (a + b) / 2)) with hk
  have hlt : |y - (a + b) / 2 - k| < (b - a) / 2 := by
    have h : y - (a + b) / 2 - (k : ℝ) * 1 = y - (a + b) / 2 - k := by ring
    rwa [h] at hy
  rw [abs_lt] at hlt
  have h1 : a < y - k := by linarith [hlt.1]
  have h2 : y - k < b := by linarith [hlt.2]
  have hfr : Int.fract y = y - k := by
    rw [← Int.fract_sub_intCast y k, Int.fract_eq_self]
    constructor <;> linarith
  rw [hfr]
  exact ⟨h1.le, h2⟩

/-! ### Weyl's criterion -/

theorem countIn_eq_sum (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : (countIn x a b N : ℝ)
    = ∑ n ∈ Finset.range N, (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0) := by
  rw [countIn, Finset.card_filter]
  push_cast
  rfl

theorem ravg_bump_le_count (x : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (ep : ℝ)
    (hep : 0 < ep) (N : ℕ) :
    ravg x (bump ((a + b) / 2) ((b - a) / 2) ep) N ≤ (countIn x a b N : ℝ) / N := by
  have hdiv : (countIn x a b N : ℝ) / N
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0) := by
    rw [countIn_eq_sum, div_eq_inv_mul]
  rw [hdiv, ravg]
  have hNn : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) hNn
  by_cases hmem : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos hmem]
    exact bump_le_one _ _ _ _
  · rw [if_neg hmem]
    have hge : ((b - a) / 2)
        ≤ ‖((x n : AddCircle (1 : ℝ)) - (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)))‖ := by
      by_contra hcon
      exact hmem (fract_mem_of_norm_lt ha hb (not_le.mp hcon))
    rw [bump_eq_zero _ _ _ hep hge]

theorem count_le_ravg_bump (x : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (ep : ℝ)
    (hep : 0 < ep) (N : ℕ) :
    (countIn x a b N : ℝ) / N ≤ ravg x (bump ((a + b) / 2) ((b - a) / 2 + ep) ep) N := by
  have hdiv : (countIn x a b N : ℝ) / N
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0) := by
    rw [countIn_eq_sum, div_eq_inv_mul]
  rw [hdiv, ravg]
  have hNn : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) hNn
  by_cases hmem : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos hmem, bump_eq_one _ _ _ hep (by simpa using norm_le_of_fract_mem ha hb hmem)]
  · rw [if_neg hmem]
    exact bump_nonneg _ _ _ _

/-- **Weyl's criterion.** A sequence whose nontrivial exponential sums have vanishing averages is
equidistributed modulo one. -/
theorem equidistributedMod1_of_weylCondition (x : ℕ → ℝ) (hx : WeylCondition x) :
    EquidistributedMod1 x := by
  intro a b ha hab hb
  rcases eq_or_lt_of_le (show b - a ≤ 1 by linarith) with hfull | hlt
  · have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    subst ha0; subst hb1
    rw [show (1 : ℝ) - 0 = 1 by norm_num]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hcnt : countIn x 0 1 N = N := by
      rw [countIn, Finset.filter_true_of_mem, Finset.card_range]
      intro n _
      exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    rw [hcnt, div_self (by positivity)]
  · rw [Metric.tendsto_atTop]
    intro δ hδ
    set r := (b - a) / 2 with hr
    set c := (a + b) / 2 with hc
    have hr0 : 0 ≤ r := by rw [hr]; linarith
    have hrhalf : r < 1 / 2 := by rw [hr]; linarith
    set ep := min (δ / 8) ((1 / 2 - r) / 2) with hep_def
    have hep : 0 < ep := lt_min (by linarith) (by linarith)
    have hep1 : ep ≤ δ / 8 := min_le_left _ _
    have hep2 : r + ep ≤ 1 / 2 := by
      have := min_le_right (δ / 8) ((1 / 2 - r) / 2)
      rw [← hep_def] at this
      linarith
    have hlow := ravg_tendsto_integral x hx (bump c r ep)
    have hup := ravg_tendsto_integral x hx (bump c (r + ep) ep)
    have hI1 : 2 * (r - ep) ≤ ∫ z, bump c r ep z := le_integral_bump c r ep hep (by linarith)
    have hI2 : (∫ z, bump c (r + ep) ep z) ≤ 2 * (r + ep) :=
      integral_bump_le c (r + ep) ep hep (by linarith) hep2
    rw [Metric.tendsto_atTop] at hlow hup
    obtain ⟨M1, hM1⟩ := hlow (δ / 4) (by linarith)
    obtain ⟨M2, hM2⟩ := hup (δ / 4) (by linarith)
    refine ⟨max M1 M2, fun N hN => ?_⟩
    have e1 := hM1 N (le_trans (le_max_left _ _) hN)
    have e2 := hM2 N (le_trans (le_max_right _ _) hN)
    rw [Real.dist_eq, abs_lt] at e1 e2 ⊢
    have s1 := ravg_bump_le_count x a b ha hb ep hep N
    have s2 := count_le_ravg_bump x a b ha hb ep hep N
    rw [← hc, ← hr] at s1 s2
    exact ⟨by linarith [e1.1, s1], by linarith [e2.2, s2]⟩

/-! ### The exponential sums for `n * α` -/

theorem weyl_sum_tendsto_zero {α : ℝ} (hα : Irrational α) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * (n * α))) atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * π * Complex.I * h * α) with hz
  have hz1 : z ≠ 1 := by
    rw [hz, Ne, Complex.exp_eq_one_iff]
    rintro ⟨n, hn⟩
    have hpi : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.ext_iff]
    have h2 : ((h : ℂ) * α) * (2 * (π : ℂ) * Complex.I) = (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
      rw [← hn]; ring
    have h3 : ((h : ℂ) * α) = (n : ℂ) := mul_right_cancel₀ hpi h2
    have h4 : ((h : ℝ) * α) = (n : ℝ) := by exact_mod_cast h3
    have hh' : ((h : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hh
    exact hα.ne_rational n h (by field_simp at h4 ⊢; linarith [h4])
  have hznorm : ‖z‖ = 1 := by
    rw [hz, Complex.norm_exp]
    norm_num
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * (n * α)) = (z ^ N - 1) / (z - 1) := by
    intro N
    rw [← geom_sum_eq hz1]
    exact Finset.sum_congr rfl fun n _ => by rw [hz, ← Complex.exp_nat_mul]; ring_nf
  have hzsub : (0 : ℝ) < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
  refine squeeze_zero_norm (a := fun N : ℕ => (2 / ‖z - 1‖) / N) (fun N => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [hsum N, norm_mul, norm_div, norm_inv, Complex.norm_natCast]
  have h5 : ‖z ^ N - 1‖ ≤ 2 :=
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hznorm]; norm_num
  calc (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖) ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := by gcongr
    _ = (2 / ‖z - 1‖) / N := by ring

/-! ### Main results -/

/-- **Weyl's equidistribution theorem, conditional form.** If the Weyl exponential sums of the
sequence `n ↦ n * α` have vanishing averages, then the sequence is equidistributed modulo one. -/
theorem equidistribution_of_asymptotic_exists {α : ℝ}
    (h_asymptotic : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * π * Complex.I * h * (n * α))) atTop (𝓝 0)) :
    EquidistributedMod1 (fun n : ℕ => n * α) := by
  refine equidistributedMod1_of_weylCondition _ fun h hh => ?_
  refine Tendsto.congr (fun N => ?_) (h_asymptotic h hh)
  simp only [cavg, fourier_coe_apply]
  push_cast
  simp

/-- **Weyl's equidistribution theorem.** For irrational `α` the sequence `n ↦ n * α` is
equidistributed modulo one. -/
theorem equidistributedMod1_natMul_irrational {α : ℝ} (hα : Irrational α) :
    EquidistributedMod1 (fun n : ℕ => n * α) :=
  equidistribution_of_asymptotic_exists (fun h hh => weyl_sum_tendsto_zero hα h hh)

end

end Brockian.Equidistribution

