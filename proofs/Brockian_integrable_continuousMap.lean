import Brockian.EquidistributionBVReduction

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
# Equidistribution of `n • α` and the reduction of configuration counts to the main term

For an irrational `α`, the configuration count

`configCount α a b N = #{ n < N : Int.fract (n * α) ∈ [a, b) }`

is asymptotic to its main term `mainTerm a b N = (b - a) * N`.

The analytic input (Weyl equidistribution of the sequence `n • α` on the circle `ℝ / ℤ`)
is proved here from scratch, so the final statement
`configCount_over_main_tendsto` is unconditional.

The proof proceeds by:
* computing the Birkhoff averages of the Fourier monomials `fourier k` along the orbit
  (geometric sums, `avg_fourier_tendsto`);
* extending to all continuous functions by Stone--Weierstrass (`avg_continuous_tendsto`);
* sandwiching the indicator of an arc between continuous piecewise-linear functions
  (a bounded-variation reduction) to obtain the counting asymptotics.
-/

open Filter MeasureTheory Set Topology Complex
open scoped BigOperators

set_option autoImplicit false

namespace Brockian

namespace EquidistributionBVReduction

noncomputable section

local instance isProbabilityMeasure_volume_unitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The point `n * α` of the circle `ℝ / ℤ`. -/
def orbit (alpha : ℝ) (n : ℕ) : UnitAddCircle := (((n : ℝ) * alpha : ℝ) : UnitAddCircle)

/-- The Birkhoff (Cesàro) average of `f` over the first `N` points of the orbit of `α`. -/
def avg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (alpha : ℝ) (f : UnitAddCircle → E) (N : ℕ) : E :=
  (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, f (orbit alpha n)

/-- The number of `n < N` whose fractional part `Int.fract (n * α)` lies in `[a, b)`. -/
def configCount (alpha a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * alpha) ∈ Ico a b).card

/-- The expected main term for `configCount`. -/
def mainTerm (a b : ℝ) (N : ℕ) : ℝ := (b - a) * N

/-! ### Integrability and basic estimates -/

theorem integrable_continuousMap (f : C(UnitAddCircle, ℂ)) : Integrable (fun x => f x) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem avg_sub_le (alpha : ℝ) (f g : C(UnitAddCircle, ℂ)) (N : ℕ) :
    ‖avg alpha f N - avg alpha g N‖ ≤ ‖f - g‖ := by
  have hsum : ‖∑ n ∈ Finset.range N, (f (orbit alpha n) - g (orbit alpha n))‖ ≤ N * ‖f - g‖ := by
    calc ‖∑ n ∈ Finset.range N, (f (orbit alpha n) - g (orbit alpha n))‖
        ≤ ∑ n ∈ Finset.range N, ‖f (orbit alpha n) - g (orbit alpha n)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ := by
          refine Finset.sum_le_sum fun n _ => ?_
          simpa using (f - g).norm_coe_le_norm (orbit alpha n)
      _ = N * ‖f - g‖ := by simp
  have hrw : avg alpha f N - avg alpha g N
      = (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, (f (orbit alpha n) - g (orbit alpha n)) := by
    simp [avg, Finset.sum_sub_distrib, smul_sub]
  rw [hrw, norm_smul, norm_inv, Real.norm_natCast]
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · rw [inv_mul_le_iff₀ (by exact_mod_cast h)]
    exact hsum

theorem integral_sub_le (f g : C(UnitAddCircle, ℂ)) :
    ‖(∫ x : UnitAddCircle, f x) - ∫ x : UnitAddCircle, g x‖ ≤ ‖f - g‖ := by
  rw [← integral_sub (integrable_continuousMap f) (integrable_continuousMap g)]
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure UnitAddCircle))
    (f := fun x => f x - g x) (C := ‖f - g‖) ?_
  · simpa using h
  · filter_upwards with x
    simpa using (f - g).norm_coe_le_norm x

/-! ### Fourier monomials -/

/-- The integral of a Fourier monomial over the circle. -/
theorem integral_fourier_eq (k : ℤ) :
    (∫ x : UnitAddCircle, fourier (T := 1) k x) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp
  rw [← UnitAddCircle.intervalIntegral_preimage 0 (fun x => fourier (T := 1) k x)]
  have h : ∀ x : ℝ, (fourier (T := 1) k (x : UnitAddCircle))
      = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * k) * x) := by
    intro x
    rw [fourier_coe_apply]
    push_cast
    ring_nf
  simp only [h]
  have hc : (2 * (Real.pi : ℂ) * Complex.I * k) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero, hk]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * k * ((0 + 1 : ℝ) : ℂ)) = 1 := by
    push_cast
    rw [show (2 * (Real.pi : ℂ) * Complex.I * k * (0 + 1)) = (k : ℂ) * (2 * Real.pi * Complex.I) by
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [h1]
  simp

/-- Weyl's exponential-sum estimate: for `k ≠ 0` the Birkhoff averages of `fourier k` along
the orbit of an irrational rotation tend to `0`. -/
theorem avg_fourier_tendsto_zero {alpha : ℝ} (halpha : Irrational alpha) {k : ℤ} (hk : k ≠ 0) :
    Tendsto (avg alpha (fourier (T := 1) k)) atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * k * alpha) with hz
  have hpow : ∀ n : ℕ, fourier (T := 1) k (orbit alpha n) = z ^ n := by
    intro n
    rw [orbit, fourier_coe_apply, hz, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    have h4 : ((k : ℂ) * alpha) * (2 * Real.pi * Complex.I)
        = (m : ℂ) * (2 * Real.pi * Complex.I) := by rw [← hm]; ring
    have h3 : (k : ℂ) * alpha = m := mul_right_cancel₀ h2 h4
    have hkey : (k : ℝ) * alpha = m := by exact_mod_cast h3
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have halp : alpha = (m : ℝ) / (k : ℝ) := by field_simp; linarith [hkey]
    exact halpha ⟨(m : ℚ) / (k : ℚ), by push_cast [halp]; ring⟩
  have hznorm : ‖z‖ = 1 := by rw [hz, Complex.norm_exp]; norm_num
  have hnorm : ∀ N : ℕ, ‖avg alpha (fourier (T := 1) k) N‖ ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
    intro N
    rw [avg, norm_smul, norm_inv, Real.norm_natCast]
    have hsum : ‖∑ n ∈ Finset.range N, fourier (T := 1) k (orbit alpha n)‖ ≤ 2 / ‖z - 1‖ := by
      simp only [hpow]
      rw [geom_sum_eq hz1, norm_div]
      gcongr
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by simp [norm_pow, hznorm]; norm_num
    have hpos : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hsum hpos
  refine squeeze_zero_norm hnorm ?_
  have h0 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using h0.mul_const (2 / ‖z - 1‖)

/-- The Birkhoff averages of a Fourier monomial along the orbit of an irrational rotation
converge to the integral of the monomial. -/
theorem avg_fourier_tendsto {alpha : ℝ} (halpha : Irrational alpha) (k : ℤ) :
    Tendsto (avg alpha (fourier (T := 1) k)) atTop
      (𝓝 (∫ x : UnitAddCircle, fourier (T := 1) k x)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [integral_fourier_eq, if_pos rfl]
    have hev : ∀ N : ℕ, N ≠ 0 → avg alpha (fourier (T := 1) 0) N = 1 := by
      intro N hN
      have hN' : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      simp only [avg, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [Complex.real_smul]
      push_cast
      field_simp
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact (hev N hN).symm
  · rw [integral_fourier_eq, if_neg hk]
    exact avg_fourier_tendsto_zero halpha hk

/-! ### From monomials to all continuous functions -/

theorem avg_span_tendsto {alpha : ℝ} (halpha : Irrational alpha) {g : C(UnitAddCircle, ℂ)}
    (hg : g ∈ Submodule.span ℂ (Set.range (fourier (T := 1)))) :
    Tendsto (avg alpha g) atTop (𝓝 (∫ x : UnitAddCircle, g x)) := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact avg_fourier_tendsto halpha k
  | zero =>
      have h1 : (avg alpha ((0 : C(UnitAddCircle, ℂ)) : UnitAddCircle → ℂ)) = fun _ => 0 := by
        funext N; simp [avg]
      rw [h1]
      simp
  | add x y hx hy ihx ihy =>
      have hint : (∫ t : UnitAddCircle, (x + y) t) = (∫ t, x t) + ∫ t, y t := by
        simp only [ContinuousMap.add_apply]
        exact integral_add (integrable_continuousMap x) (integrable_continuousMap y)
      rw [hint]
      have h2 : (avg alpha ((x + y : C(UnitAddCircle, ℂ)) : UnitAddCircle → ℂ))
          = fun N => avg alpha x N + avg alpha y N := by
        funext N
        simp [avg, ContinuousMap.add_apply, Finset.sum_add_distrib, smul_add]
      rw [h2]
      exact ihx.add ihy
  | smul c x hx ihx =>
      have hint : (∫ t : UnitAddCircle, (c • x) t) = c • ∫ t, x t := by
        simp only [ContinuousMap.smul_apply]
        exact integral_smul c _
      rw [hint]
      have h3 : (avg alpha ((c • x : C(UnitAddCircle, ℂ)) : UnitAddCircle → ℂ))
          = fun N => c • avg alpha x N := by
        funext N
        simp [avg, ContinuousMap.smul_apply, Finset.mul_sum]
        ring_nf
      rw [h3]
      exact ihx.const_smul c

/-- Stone--Weierstrass: trigonometric polynomials are uniformly dense. -/
theorem exists_trig_poly_approx (f : C(UnitAddCircle, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ Submodule.span ℂ (Set.range (fourier (T := 1))), ‖f - g‖ < ε := by
  have hmem : f ∈ (Submodule.span ℂ (Set.range (fourier (T := 1)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  have hmem' : f ∈ closure
      ((Submodule.span ℂ (Set.range (fourier (T := 1)))) : Set C(UnitAddCircle, ℂ)) := hmem
  rw [Metric.mem_closure_iff] at hmem'
  obtain ⟨g, hg, hdist⟩ := hmem' ε hε
  exact ⟨g, hg, by rwa [← dist_eq_norm]⟩

/-- Birkhoff averages converge to the integral for every continuous complex-valued function. -/
theorem avg_continuous_tendsto {alpha : ℝ} (halpha : Irrational alpha) (f : C(UnitAddCircle, ℂ)) :
    Tendsto (avg alpha f) atTop (𝓝 (∫ x : UnitAddCircle, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := exists_trig_poly_approx f (ε := ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp (avg_span_tendsto halpha hg)) (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : dist (avg alpha f N) (avg alpha g N) < ε / 3 := by
    rw [dist_eq_norm]; exact lt_of_le_of_lt (avg_sub_le alpha f g N) hfg
  have h2 : dist (avg alpha (g : UnitAddCircle → ℂ) N) (∫ x : UnitAddCircle, g x) < ε / 3 :=
    hN₀ N hN
  have h3 : dist (∫ x : UnitAddCircle, g x) (∫ x : UnitAddCircle, f x) < ε / 3 := by
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (integral_sub_le g f) ?_
    rwa [← norm_neg, neg_sub]
  calc dist (avg alpha f N) (∫ x : UnitAddCircle, f x)
      ≤ dist (avg alpha f N) (avg alpha g N)
        + dist (avg alpha (g : UnitAddCircle → ℂ) N) (∫ x : UnitAddCircle, g x)
        + dist (∫ x : UnitAddCircle, g x) (∫ x : UnitAddCircle, f x) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

/-- Real-valued version of `avg_continuous_tendsto`. -/
theorem avg_continuous_tendsto_real {alpha : ℝ} (halpha : Irrational alpha)
    (f : C(UnitAddCircle, ℝ)) :
    Tendsto (avg alpha f) atTop (𝓝 (∫ x : UnitAddCircle, f x)) := by
  set F : C(UnitAddCircle, ℂ) := ⟨fun x => ((f x : ℝ) : ℂ), by fun_prop⟩ with hF
  have hint : (∫ x : UnitAddCircle, F x) = ((∫ x : UnitAddCircle, f x : ℝ) : ℂ) := by
    simp only [hF, ContinuousMap.coe_mk]
    exact integral_complex_ofReal
  have havg : avg alpha (F : UnitAddCircle → ℂ) = fun N => ((avg alpha f N : ℝ) : ℂ) := by
    funext N
    simp [avg, hF, Complex.ofReal_sum, Complex.real_smul]
  have h := avg_continuous_tendsto halpha F
  rw [hint, havg] at h
  have h2 := (Complex.continuous_re.tendsto _).comp h
  simpa [Function.comp] using h2

/-! ### Continuous sandwich functions for the indicator of an arc -/

/-- A trapezoidal function which equals `1` on `[a, b]` and vanishes outside `[a - eps, b + eps]`. -/
def trapUpper (a b eps x : ℝ) : ℝ :=
  max 0 (min 1 (min ((x - (a - eps)) / eps) ((b + eps - x) / eps)))

/-- A trapezoidal function which equals `1` on `[a + eps, b - eps]` and vanishes outside `(a, b)`. -/
def trapLower (a b eps x : ℝ) : ℝ :=
  max 0 (min 1 (min ((x - a) / eps) ((b - x) / eps)))

lemma trapUpper_cont (a b eps : ℝ) : Continuous (trapUpper a b eps) := by
  unfold trapUpper; fun_prop

lemma trapLower_cont (a b eps : ℝ) : Continuous (trapLower a b eps) := by
  unfold trapLower; fun_prop

lemma trapUpper_nonneg (a b eps x : ℝ) : 0 ≤ trapUpper a b eps x := le_max_left _ _

lemma trapLower_nonneg (a b eps x : ℝ) : 0 ≤ trapLower a b eps x := le_max_left _ _

lemma trapUpper_le_one (a b eps x : ℝ) : trapUpper a b eps x ≤ 1 :=
  max_le zero_le_one (le_trans (min_le_left _ _) le_rfl)

lemma trapLower_le_one (a b eps x : ℝ) : trapLower a b eps x ≤ 1 :=
  max_le zero_le_one (le_trans (min_le_left _ _) le_rfl)

lemma trapUpper_eq_one {a b eps x : ℝ} (heps : 0 < eps) (h1 : a ≤ x) (h2 : x ≤ b) :
    trapUpper a b eps x = 1 := by
  unfold trapUpper
  have e1 : 1 ≤ (x - (a - eps)) / eps := by rw [le_div_iff₀ heps]; linarith
  have e2 : 1 ≤ (b + eps - x) / eps := by rw [le_div_iff₀ heps]; linarith
  rw [min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

lemma trapUpper_eq_zero_left {a b eps x : ℝ} (heps : 0 < eps) (h : x ≤ a - eps) :
    trapUpper a b eps x = 0 := by
  unfold trapUpper
  have e1 : (x - (a - eps)) / eps ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) heps.le
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) e1))

lemma trapUpper_eq_zero_right {a b eps x : ℝ} (heps : 0 < eps) (h : b + eps ≤ x) :
    trapUpper a b eps x = 0 := by
  unfold trapUpper
  have e1 : (b + eps - x) / eps ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) heps.le
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) e1))

lemma trapLower_eq_one {a b eps x : ℝ} (heps : 0 < eps) (h1 : a + eps ≤ x) (h2 : x ≤ b - eps) :
    trapLower a b eps x = 1 := by
  unfold trapLower
  have e1 : 1 ≤ (x - a) / eps := by rw [le_div_iff₀ heps]; linarith
  have e2 : 1 ≤ (b - x) / eps := by rw [le_div_iff₀ heps]; linarith
  rw [min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

lemma trapLower_eq_zero {a b eps x : ℝ} (heps : 0 < eps) (h : x ≤ a ∨ b ≤ x) :
    trapLower a b eps x = 0 := by
  unfold trapLower
  rcases h with h | h
  · have e1 : (x - a) / eps ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) heps.le
    exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) e1))
  · have e1 : (b - x) / eps ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) heps.le
    exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) e1))

/-! ### Lifting periodic functions to the circle -/

lemma coe_rep (c x : ℝ) : ((Int.fract (x - c) + c : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  have h : Int.fract (x - c) + c = x - ((⌊x - c⌋ : ℤ) : ℝ) := by rw [Int.fract]; ring
  rw [h]; simp

lemma rep_mem (c x : ℝ) : Int.fract (x - c) + c ∈ Ico c (c + 1) :=
  ⟨by have := Int.fract_nonneg (x - c); linarith,
    by have := Int.fract_lt_one (x - c); linarith⟩

lemma fract_rep (c x : ℝ) : Int.fract (Int.fract (x - c) + c) = Int.fract x := by
  have h : Int.fract (x - c) + c = x - ((⌊x - c⌋ : ℤ) : ℝ) := by rw [Int.fract]; ring
  rw [h]; exact Int.fract_sub_intCast x _

lemma liftIco_coe (c : ℝ) (F : ℝ → ℝ) (x : ℝ) :
    AddCircle.liftIco 1 c F (x : UnitAddCircle) = F (Int.fract (x - c) + c) := by
  rw [← coe_rep c x]
  exact AddCircle.liftIco_coe_apply (by simpa using rep_mem c x)

lemma integral_liftIco (c : ℝ) (F : ℝ → ℝ) (hend : F c = F (c + 1)) :
    (∫ x : UnitAddCircle, AddCircle.liftIco 1 c F x) = ∫ t in c..(c + 1), F t := by
  rw [← UnitAddCircle.intervalIntegral_preimage c (AddCircle.liftIco 1 c F)]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  rw [uIcc_of_le (by linarith)] at ht
  simp only
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [h, liftIco_coe, show Int.fract ((c + 1) - c) + c = c by norm_num, hend]
  · rw [AddCircle.liftIco_coe_apply (show t ∈ Ico c (c + 1) from ⟨ht.1, h⟩)]

lemma integral_le_of_support (F : ℝ → ℝ) (hF : Continuous F) (c p q : ℝ) (hcp : c ≤ p)
    (hpq : p ≤ q) (hqc : q ≤ c + 1) (hz1 : ∀ x ∈ Icc c p, F x = 0)
    (hz2 : ∀ x ∈ Icc q (c + 1), F x = 0) (hle : ∀ x, F x ≤ 1) :
    (∫ t in c..(c + 1), F t) ≤ q - p := by
  have hi : ∀ u v : ℝ, IntervalIntegrable F volume u v := fun u v => hF.intervalIntegrable u v
  have hsplit : (∫ t in c..(c + 1), F t)
      = (∫ t in c..p, F t) + (∫ t in p..q, F t) + (∫ t in q..(c + 1), F t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi c p) (hi p q),
      intervalIntegral.integral_add_adjacent_intervals (hi c q) (hi q (c + 1))]
  have h1 : (∫ t in c..p, F t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro x hx; rw [uIcc_of_le hcp] at hx; exact hz1 x hx
  have h3 : (∫ t in q..(c + 1), F t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro x hx; rw [uIcc_of_le hqc] at hx; exact hz2 x hx
  have h2 : (∫ t in p..q, F t) ≤ q - p := by
    have h := intervalIntegral.integral_mono_on (f := F) (g := fun _ => (1 : ℝ)) hpq (hi p q)
      intervalIntegrable_const (fun x _ => hle x)
    simpa using h
  rw [hsplit, h1, h3]
  simpa using h2

lemma le_integral_of_ge_one (F : ℝ → ℝ) (hF : Continuous F) (c p q : ℝ) (hcp : c ≤ p)
    (hpq : p ≤ q) (hqc : q ≤ c + 1) (hnn : ∀ x, 0 ≤ F x) (hone : ∀ x ∈ Icc p q, 1 ≤ F x) :
    q - p ≤ ∫ t in c..(c + 1), F t := by
  have hi : ∀ u v : ℝ, IntervalIntegrable F volume u v := fun u v => hF.intervalIntegrable u v
  have hsplit : (∫ t in c..(c + 1), F t)
      = (∫ t in c..p, F t) + (∫ t in p..q, F t) + (∫ t in q..(c + 1), F t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi c p) (hi p q),
      intervalIntegral.integral_add_adjacent_intervals (hi c q) (hi q (c + 1))]
  have h1 : (0 : ℝ) ≤ ∫ t in c..p, F t := intervalIntegral.integral_nonneg hcp fun x _ => hnn x
  have h3 : (0 : ℝ) ≤ ∫ t in q..(c + 1), F t :=
    intervalIntegral.integral_nonneg hqc fun x _ => hnn x
  have h2 : q - p ≤ ∫ t in p..q, F t := by
    have h := intervalIntegral.integral_mono_on (f := fun _ => (1 : ℝ)) (g := F) hpq
      intervalIntegrable_const (hi p q) fun x hx => hone x hx
    simpa using h
  rw [hsplit]; linarith

/-- A continuous function on the circle dominating the indicator of the arc `[a, b)`,
with integral at most `(b - a) + 2 * eps`. -/
lemma exists_upper_sandwich {a b eps : ℝ} (hab : a ≤ b) (heps : 0 < eps)
    (hsmall : b - a + 3 * eps ≤ 1) :
    ∃ h : C(UnitAddCircle, ℝ),
      (∀ x : ℝ, (if Int.fract x ∈ Ico a b then (1 : ℝ) else 0) ≤ h (x : UnitAddCircle)) ∧
      (∫ x : UnitAddCircle, h x) ≤ (b - a) + 2 * eps := by
  set c : ℝ := a - 2 * eps with hc
  set F : ℝ → ℝ := trapUpper a b eps with hFdef
  have hend : F c = F (c + 1) := by
    rw [hFdef, trapUpper_eq_zero_left heps (by rw [hc]; linarith),
      trapUpper_eq_zero_right heps (by rw [hc]; linarith)]
  have hcont : Continuous (AddCircle.liftIco 1 c F) :=
    AddCircle.liftIco_continuous (by simpa using hend) ((trapUpper_cont a b eps).continuousOn)
  refine ⟨⟨AddCircle.liftIco 1 c F, hcont⟩, ?_, ?_⟩
  · intro x
    by_cases hx : Int.fract x ∈ Ico a b
    · rw [if_pos hx]
      have hxc : ((x : ℝ) : UnitAddCircle) = ((Int.fract x : ℝ) : UnitAddCircle) := by
        rw [Int.fract]; simp
      have hmem : Int.fract x ∈ Ico c (c + 1) :=
        ⟨by rw [hc]; linarith [hx.1], by rw [hc]; linarith [hx.2]⟩
      show 1 ≤ AddCircle.liftIco 1 c F ((x : ℝ) : UnitAddCircle)
      rw [hxc, AddCircle.liftIco_coe_apply (by simpa using hmem), hFdef,
        trapUpper_eq_one heps hx.1 hx.2.le]
    · rw [if_neg hx]
      show 0 ≤ AddCircle.liftIco 1 c F ((x : ℝ) : UnitAddCircle)
      rw [liftIco_coe]
      exact trapUpper_nonneg _ _ _ _
  · show (∫ x : UnitAddCircle, AddCircle.liftIco 1 c F x) ≤ (b - a) + 2 * eps
    rw [integral_liftIco c F hend]
    have h := integral_le_of_support F (trapUpper_cont a b eps) c (a - eps) (b + eps)
      (by rw [hc]; linarith) (by linarith) (by rw [hc]; linarith)
      (fun x hx => trapUpper_eq_zero_left heps hx.2)
      (fun x hx => trapUpper_eq_zero_right heps hx.1)
      (fun x => trapUpper_le_one _ _ _ _)
    linarith

/-- A continuous function on the circle dominated by the indicator of the arc `[a, b)`,
with integral at least `(b - a) - 2 * eps`. -/
lemma exists_lower_sandwich {a b eps : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (heps : 0 < eps)
    (hgap : a + eps ≤ b - eps) (hsmall : b - a + 2 * eps ≤ 1) :
    ∃ g : C(UnitAddCircle, ℝ),
      (∀ x : ℝ, g (x : UnitAddCircle) ≤ (if Int.fract x ∈ Ico a b then (1 : ℝ) else 0)) ∧
      (b - a) - 2 * eps ≤ ∫ x : UnitAddCircle, g x := by
  set c : ℝ := a - 2 * eps with hc
  set G : ℝ → ℝ := trapLower a b eps with hGdef
  have hend : G c = G (c + 1) := by
    rw [hGdef, trapLower_eq_zero heps (Or.inl (by rw [hc]; linarith)),
      trapLower_eq_zero heps (Or.inr (by rw [hc]; linarith))]
  have hcont : Continuous (AddCircle.liftIco 1 c G) :=
    AddCircle.liftIco_continuous (by simpa using hend) ((trapLower_cont a b eps).continuousOn)
  refine ⟨⟨AddCircle.liftIco 1 c G, hcont⟩, ?_, ?_⟩
  · intro x
    show AddCircle.liftIco 1 c G ((x : ℝ) : UnitAddCircle) ≤ _
    rw [liftIco_coe]
    set r : ℝ := Int.fract (x - c) + c with hr
    by_cases hx : Int.fract x ∈ Ico a b
    · rw [if_pos hx]; exact trapLower_le_one _ _ _ _
    · rw [if_neg hx]
      have hfr : Int.fract r = Int.fract x := fract_rep c x
      have hG0 : G r = 0 := by
        rcases le_or_gt r a with h | h
        · exact trapLower_eq_zero heps (Or.inl h)
        rcases le_or_gt b r with h2 | h2
        · exact trapLower_eq_zero heps (Or.inr h2)
        · exfalso
          have hr0 : 0 ≤ r := le_trans ha h.le
          have hr1 : r < 1 := lt_of_lt_of_le h2 hb
          have hrr : Int.fract r = r := Int.fract_eq_self.mpr ⟨hr0, hr1⟩
          rw [hfr] at hrr
          exact hx (by rw [hrr]; exact ⟨h.le, h2⟩)
      rw [hG0]
  · show (b - a) - 2 * eps ≤ ∫ x : UnitAddCircle, AddCircle.liftIco 1 c G x
    rw [integral_liftIco c G hend]
    have h := le_integral_of_ge_one G (trapLower_cont a b eps) c (a + eps) (b - eps)
      (by rw [hc]; linarith) hgap (by rw [hc]; linarith)
      (fun x => trapLower_nonneg _ _ _ _)
      (fun x hx => le_of_eq (trapLower_eq_one heps hx.1 hx.2).symm)
    linarith

/-- The configuration count written as a sum of indicators. -/
lemma configCount_eq_sum (alpha a b : ℝ) (N : ℕ) :
    (configCount alpha a b N : ℝ)
      = ∑ n ∈ Finset.range N, (if Int.fract ((n : ℝ) * alpha) ∈ Ico a b then (1 : ℝ) else 0) := by
  rw [configCount, Finset.card_filter]
  push_cast
  rfl

/-! ### Counting points in an arc -/

/-- Equidistribution: the proportion of `n < N` with `Int.fract (n * α) ∈ [a, b)`
tends to `b - a`. -/
theorem configCount_div_tendsto {alpha : ℝ} (halpha : Irrational alpha) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount alpha a b N : ℝ) / N) atTop (𝓝 (b - a)) := by
  by_cases hfull : b - a = 1
  · have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    subst ha0
    subst hb1
    have hcount : ∀ N : ℕ, configCount alpha 0 1 N = N := by
      intro N
      rw [configCount, Finset.filter_true_of_mem (fun n _ => ⟨Int.fract_nonneg _,
        Int.fract_lt_one _⟩), Finset.card_range]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ) - 0))
    filter_upwards [eventually_ne_atTop 0] with N hN
    rw [hcount N]
    field_simp
    norm_num
  · have hlt : b - a < 1 := lt_of_le_of_ne (by linarith) hfull
    rw [Metric.tendsto_atTop]
    intro ε hε
    set eps : ℝ := min (ε / 4) (min ((b - a) / 2) ((1 - (b - a)) / 3)) with hepsdef
    have heps : 0 < eps :=
      lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have he1 : eps ≤ ε / 4 := min_le_left _ _
    have he2 : eps ≤ (b - a) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    have he3 : eps ≤ (1 - (b - a)) / 3 := le_trans (min_le_right _ _) (min_le_right _ _)
    obtain ⟨hup, hup_pt, hup_int⟩ := exists_upper_sandwich (a := a) (b := b) hab.le heps
      (by linarith)
    obtain ⟨glo, glo_pt, glo_int⟩ := exists_lower_sandwich (a := a) (b := b) ha hb heps
      (by linarith) (by linarith)
    obtain ⟨N1, hN1⟩ :=
      (Metric.tendsto_atTop.mp (avg_continuous_tendsto_real halpha hup)) eps heps
    obtain ⟨N2, hN2⟩ :=
      (Metric.tendsto_atTop.mp (avg_continuous_tendsto_real halpha glo)) eps heps
    refine ⟨max 1 (max N1 N2), fun N hN => ?_⟩
    have hN0 : 1 ≤ N := le_trans (le_max_left _ _) hN
    have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hN
    have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
    have hle_up : (configCount alpha a b N : ℝ) / N ≤ avg alpha hup N := by
      rw [configCount_eq_sum, avg, smul_eq_mul, div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Finset.sum_le_sum fun n _ => ?_
      exact hup_pt ((n : ℝ) * alpha)
    have hge_lo : avg alpha glo N ≤ (configCount alpha a b N : ℝ) / N := by
      rw [configCount_eq_sum, avg, smul_eq_mul, div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Finset.sum_le_sum fun n _ => ?_
      exact glo_pt ((n : ℝ) * alpha)
    have hu : avg alpha hup N < (∫ x : UnitAddCircle, hup x) + eps := by
      have h := hN1 N hN1'
      rw [Real.dist_eq, abs_lt] at h
      linarith [h.2]
    have hl : (∫ x : UnitAddCircle, glo x) - eps < avg alpha glo N := by
      have h := hN2 N hN2'
      rw [Real.dist_eq, abs_lt] at h
      linarith [h.1]
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

/-- The configuration count is asymptotic to its main term. -/
theorem configCount_over_main_tendsto {alpha : ℝ} (halpha : Irrational alpha) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount alpha a b N : ℝ) / mainTerm a b N) atTop (𝓝 1) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hrw : ∀ N : ℕ, (configCount alpha a b N : ℝ) / mainTerm a b N
      = ((configCount alpha a b N : ℝ) / N) / (b - a) := by
    intro N
    rw [mainTerm, div_div]
    ring_nf
  simp only [hrw]
  have h := (configCount_div_tendsto halpha ha hab hb).div_const (b - a)
  rwa [div_self hba] at h

end

end EquidistributionBVReduction

end Brockian

