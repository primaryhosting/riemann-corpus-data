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

import Brockian.WeylEquidistribution

/-!
# Equidistribution: reduction of a configuration count to its main term

Fix an irrational number `a`, a point `c` on the circle `ℝ/ℤ` and a radius `r` with
`0 < r < 1/2`.  Call `n` *admissible* if the orbit point `n • a` lies within distance `r` of `c`
on `ℝ/ℤ`.  `configCount a c r N` counts the admissible `n < N`, and the expected main term is
`mainTerm r N = 2 * r * N` (the measure of the arc times the number of trials).

The main result `configCount_over_main_tendsto` states that the ratio of the count to the main
term tends to `1`.

The analytic input is Weyl's equidistribution theorem for continuous test functions, proved in
`Brockian.WeylEquidistribution`; the passage from continuous test functions to the (bounded
variation, indeed indicator) test function of an arc is done here by sandwiching the indicator
between two explicit continuous, piecewise-linear functions.
-/

open MeasureTheory Filter Topology Metric
open scoped BigOperators

namespace Brockian
namespace EquidistributionBVReduction

open Brockian.Weyl

noncomputable section

open scoped Classical in
/-- The number of `n < N` for which the orbit point `n • a` lies within distance `r` of `c`
on the circle `ℝ/ℤ`. -/
def configCount (a c r : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => dist (pt a n) ((c : ℝ) : Circ) < r)).card

/-- The expected main term for `configCount a c r N`: the length `2 * r` of the arc times `N`. -/
def mainTerm (r : ℝ) (N : ℕ) : ℝ := 2 * r * N

/-- A continuous upper bound for the indicator of the open arc of radius `r` around `c`:
it equals `1` on that arc and vanishes outside the arc of radius `r + d`. -/
def upperFn (c r d : ℝ) : C(Circ, ℝ) :=
  ⟨fun x => max 0 (min 1 ((r + d - dist x ((c : ℝ) : Circ)) / d)), by fun_prop⟩

/-- A continuous lower bound for the indicator of the open arc of radius `r` around `c`:
it equals `1` on the arc of radius `r - d` and vanishes outside the arc of radius `r`. -/
def lowerFn (c r d : ℝ) : C(Circ, ℝ) :=
  ⟨fun x => max 0 (min 1 ((r - dist x ((c : ℝ) : Circ)) / d)), by fun_prop⟩

lemma upperFn_nonneg (c r d : ℝ) (x : Circ) : 0 ≤ upperFn c r d x := le_max_left _ _

lemma lowerFn_nonneg (c r d : ℝ) (x : Circ) : 0 ≤ lowerFn c r d x := le_max_left _ _

/-- The indicator of the open arc of radius `r` is at most `upperFn`. -/
lemma indicator_le_upperFn (c r d : ℝ) (hd : 0 < d) (x : Circ) :
    (if dist x ((c : ℝ) : Circ) < r then (1 : ℝ) else 0) ≤ upperFn c r d x := by
  by_cases hx : dist x ((c : ℝ) : Circ) < r
  · simp only [hx, if_pos]
    have h1 : (1 : ℝ) ≤ (r + d - dist x ((c : ℝ) : Circ)) / d := by
      rw [le_div_iff₀ hd]; linarith
    simp [upperFn, min_eq_left h1]
  · simp [hx, upperFn_nonneg]

/-- `upperFn` is at most the indicator of the closed arc of radius `r + d`. -/
lemma upperFn_le_indicator (c r d : ℝ) (hd : 0 < d) (x : Circ) :
    upperFn c r d x ≤ (closedBall ((c : ℝ) : Circ) (r + d)).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ closedBall ((c : ℝ) : Circ) (r + d)
  · rw [Set.indicator_of_mem hx]
    simp only [upperFn, ContinuousMap.coe_mk]
    exact max_le zero_le_one (min_le_left _ _)
  · rw [Set.indicator_of_notMem hx]
    simp only [mem_closedBall, not_le] at hx
    have h0 : (r + d - dist x ((c : ℝ) : Circ)) / d ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    simp only [upperFn, ContinuousMap.coe_mk]
    exact max_le le_rfl (le_trans (min_le_right _ _) h0)

/-- The indicator of the closed arc of radius `r - d` is at most `lowerFn`. -/
lemma indicator_le_lowerFn (c r d : ℝ) (hd : 0 < d) (x : Circ) :
    (closedBall ((c : ℝ) : Circ) (r - d)).indicator (fun _ => (1 : ℝ)) x ≤ lowerFn c r d x := by
  by_cases hx : x ∈ closedBall ((c : ℝ) : Circ) (r - d)
  · rw [Set.indicator_of_mem hx]
    simp only [mem_closedBall] at hx
    have h1 : (1 : ℝ) ≤ (r - dist x ((c : ℝ) : Circ)) / d := by
      rw [le_div_iff₀ hd]; linarith
    simp [lowerFn, min_eq_left h1]
  · rw [Set.indicator_of_notMem hx]
    exact lowerFn_nonneg _ _ _ _

/-- `lowerFn` is at most the indicator of the open arc of radius `r`. -/
lemma lowerFn_le_indicator (c r d : ℝ) (hd : 0 < d) (x : Circ) :
    lowerFn c r d x ≤ (if dist x ((c : ℝ) : Circ) < r then (1 : ℝ) else 0) := by
  by_cases hx : dist x ((c : ℝ) : Circ) < r
  · rw [if_pos hx]
    simp only [lowerFn, ContinuousMap.coe_mk]
    exact max_le zero_le_one (min_le_left _ _)
  · rw [if_neg hx]
    push_neg at hx
    have h0 : (r - dist x ((c : ℝ) : Circ)) / d ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    simp only [lowerFn, ContinuousMap.coe_mk]
    exact max_le le_rfl (le_trans (min_le_right _ _) h0)

/-- Upper bound for the volume of a closed arc. -/
lemma volume_closedBall_le (x : Circ) {e : ℝ} (he : 0 ≤ e) :
    (volume (closedBall x e)).toReal ≤ 2 * e := by
  rw [AddCircle.volume_closedBall,
    ENNReal.toReal_ofReal (le_min (by norm_num) (by linarith))]
  exact min_le_right _ _

/-- Lower bound for the volume of a closed arc of length at most the total length. -/
lemma le_volume_closedBall (x : Circ) {e : ℝ} (he : 2 * e ≤ 1) :
    2 * e ≤ (volume (closedBall x e)).toReal := by
  rw [AddCircle.volume_closedBall, min_eq_right he]
  rcases le_or_gt 0 (2 * e) with h | h
  · rw [ENNReal.toReal_ofReal h]
  · exact le_trans h.le ENNReal.toReal_nonneg

/-- Continuous real-valued functions on the circle are integrable. -/
lemma integrable_cont (g : C(Circ, ℝ)) : Integrable (fun x => g x) volume :=
  (map_continuous g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integral_indicator_closedBall (x : Circ) (e : ℝ) :
    ∫ y : Circ, (closedBall x e).indicator (fun _ => (1 : ℝ)) y
      = (volume (closedBall x e)).toReal := by
  rw [integral_indicator_const _ measurableSet_closedBall]
  simp [measureReal_def]

lemma integral_upperFn_le (c r d : ℝ) (hd : 0 < d) (hr : 0 < r) :
    ∫ x : Circ, upperFn c r d x ≤ 2 * (r + d) := by
  have h1 : ∫ x : Circ, upperFn c r d x
      ≤ ∫ x : Circ, (closedBall ((c : ℝ) : Circ) (r + d)).indicator (fun _ => (1 : ℝ)) x :=
    integral_mono (integrable_cont _)
      ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
      (upperFn_le_indicator c r d hd)
  rw [integral_indicator_closedBall] at h1
  exact h1.trans (volume_closedBall_le _ (by linarith))

lemma le_integral_lowerFn (c r d : ℝ) (hd : 0 < d) (hr : r < 1 / 2) :
    2 * (r - d) ≤ ∫ x : Circ, lowerFn c r d x := by
  have h1 : ∫ x : Circ, (closedBall ((c : ℝ) : Circ) (r - d)).indicator (fun _ => (1 : ℝ)) x
      ≤ ∫ x : Circ, lowerFn c r d x :=
    integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
      (integrable_cont _) (indicator_le_lowerFn c r d hd)
  rw [integral_indicator_closedBall] at h1
  exact le_trans (le_volume_closedBall _ (by linarith)) h1

open scoped Classical in
lemma count_eq_sum_indicator (a c r : ℝ) (N : ℕ) :
    (configCount a c r N : ℝ)
      = ∑ n ∈ Finset.range N, (if dist (pt a n) ((c : ℝ) : Circ) < r then (1 : ℝ) else 0) := by
  rw [configCount, Finset.card_filter]
  push_cast
  rfl

lemma count_le_sum_upper (a c r d : ℝ) (hd : 0 < d) (N : ℕ) :
    (configCount a c r N : ℝ) ≤ ∑ n ∈ Finset.range N, upperFn c r d (pt a n) := by
  rw [count_eq_sum_indicator]
  exact Finset.sum_le_sum fun n _ => indicator_le_upperFn c r d hd (pt a n)

lemma sum_lower_le_count (a c r d : ℝ) (hd : 0 < d) (N : ℕ) :
    ∑ n ∈ Finset.range N, lowerFn c r d (pt a n) ≤ (configCount a c r N : ℝ) := by
  rw [count_eq_sum_indicator]
  exact Finset.sum_le_sum fun n _ => lowerFn_le_indicator c r d hd (pt a n)

/-- The equidistribution hypothesis for the orbit `n ↦ n • a` on `ℝ/ℤ`, tested against
continuous functions.  This is the named hypothesis on which the reduction below rests; it is
discharged for every irrational `a` by `equidistributed_of_irrational`. -/
def Equidistributed (a : ℝ) : Prop :=
  ∀ f : C(Circ, ℝ),
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n))
      atTop (𝓝 (∫ x : Circ, f x))

/-- **Discharge of the equidistribution hypothesis**: the orbit of an irrational rotation is
equidistributed on `ℝ/ℤ` (Weyl's theorem, proved in `Brockian.WeylEquidistribution`). -/
theorem equidistributed_of_irrational (a : ℝ) (ha : Irrational a) : Equidistributed a :=
  fun f => tendsto_continuous_real a ha f

/-- The normalised configuration count converges to the length `2 * r` of the arc. -/
theorem configCount_div_tendsto (a c r : ℝ) (ha : Equidistributed a) (hr : 0 < r)
    (hr2 : r < 1 / 2) :
    Tendsto (fun N : ℕ => (configCount a c r N : ℝ) / N) atTop (𝓝 (2 * r)) := by
  rw [Metric.tendsto_atTop]
  intro e he
  set d : ℝ := min (e / 4) (r / 2) with hd_def
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hde : d ≤ e / 4 := min_le_left _ _
  have hdr : d ≤ r / 2 := min_le_right _ _
  have hU := ha (upperFn c r d)
  have hL := ha (lowerFn c r d)
  rw [Metric.tendsto_atTop] at hU hL
  obtain ⟨N₁, hN₁⟩ := hU (e / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hL (e / 4) (by linarith)
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNpos : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hUb : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, upperFn c r d (pt a n)
      < (∫ x : Circ, upperFn c r d x) + e / 4 := by
    have := hN₁ N hN1
    rw [Real.dist_eq, abs_sub_lt_iff] at this
    linarith [this.1]
  have hLb : (∫ x : Circ, lowerFn c r d x) - e / 4
      < (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, lowerFn c r d (pt a n) := by
    have := hN₂ N hN2
    rw [Real.dist_eq, abs_sub_lt_iff] at this
    linarith [this.2]
  have hUi := integral_upperFn_le c r d hd hr
  have hLi := le_integral_lowerFn c r d hd hr2
  have hcu : (N : ℝ)⁻¹ * (configCount a c r N : ℝ)
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, upperFn c r d (pt a n) :=
    mul_le_mul_of_nonneg_left (count_le_sum_upper a c r d hd N) hinv
  have hcl : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, lowerFn c r d (pt a n)
      ≤ (N : ℝ)⁻¹ * (configCount a c r N : ℝ) :=
    mul_le_mul_of_nonneg_left (sum_lower_le_count a c r d hd N) hinv
  rw [Real.dist_eq, abs_sub_lt_iff, div_eq_inv_mul]
  constructor <;> linarith

/-- The reduction of the configuration count to its main term, conditionally on the
equidistribution hypothesis. -/
theorem configCount_over_main_tendsto_of_equidistributed (a c r : ℝ) (ha : Equidistributed a)
    (hr : 0 < r) (hr2 : r < 1 / 2) :
    Tendsto (fun N : ℕ => (configCount a c r N : ℝ) / mainTerm r N) atTop (𝓝 1) := by
  have h := (configCount_div_tendsto a c r ha hr hr2).div_const (2 * r)
  rw [div_self (by positivity)] at h
  refine h.congr (fun N => ?_)
  rw [mainTerm, div_div, mul_comm (N : ℝ) (2 * r)]

/-- **Main theorem.** For an irrational rotation number `a`, the number of `n < N` whose orbit
point `n • a` lies within distance `r` of `c` on `ℝ/ℤ` is asymptotic to its main term
`2 * r * N`.  This is the unconditional form: the equidistribution hypothesis has been
discharged. -/
theorem configCount_over_main_tendsto (a c r : ℝ) (ha : Irrational a) (hr : 0 < r)
    (hr2 : r < 1 / 2) :
    Tendsto (fun N : ℕ => (configCount a c r N : ℝ) / mainTerm r N) atTop (𝓝 1) :=
  configCount_over_main_tendsto_of_equidistributed a c r (equidistributed_of_irrational a ha) hr hr2

end

end EquidistributionBVReduction
end Brockian

import Mathlib

/-!
# Weyl's equidistribution theorem for continuous test functions

For an irrational number `a`, the orbit `n ↦ n • a` on the circle `ℝ/ℤ` is equidistributed:
for every continuous `f : ℝ/ℤ → ℂ` we have

  `(1/N) * ∑_{n < N} f (n • a) → ∫ f`.

The proof is the classical one: the statement holds for the characters `fourier m` by an explicit
geometric-series computation, extends to their linear span by linearity, and then to all
continuous functions by density of the span of characters in the uniform norm
(Stone–Weierstrass, available in Mathlib as `span_fourier_closure_eq_top`).
-/

open MeasureTheory Filter Topology Metric Complex Submodule
open scoped BigOperators Real

namespace Brockian
namespace Weyl

noncomputable section

/-- The circle `ℝ/ℤ`. -/
abbrev Circ := AddCircle (1 : ℝ)

/-- The orbit point `n • a` on the circle `ℝ/ℤ`. -/
def pt (a : ℝ) (n : ℕ) : Circ := (((n : ℝ) * a : ℝ) : Circ)

/-- On `ℝ/ℤ` the Haar probability measure agrees with the volume measure. -/
lemma volume_eq_haar : (volume : Measure Circ) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]; simp

instance : IsProbabilityMeasure (volume : Measure Circ) := by
  rw [volume_eq_haar]; infer_instance

lemma integrable_continuous (g : C(Circ, ℂ)) : Integrable (fun x => g x) volume :=
  (map_continuous g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integral of a character over the circle: `1` for the trivial character, `0` otherwise. -/
lemma integral_fourier (m : ℤ) :
    ∫ x : Circ, fourier m x = if m = 0 then 1 else 0 := by
  have h0 := congrFun (fourierCoeff_fourier (T := (1:ℝ)) m) 0
  simp [fourierCoeff, volume_eq_haar] at h0 ⊢
  rw [h0]
  by_cases hm : m = 0 <;> simp [hm, Pi.single, Function.update, eq_comm]

/-- Weyl sums for a nontrivial character along an irrational rotation tend to `0`. -/
lemma weyl_sum_tendsto (a : ℝ) (ha : Irrational a) {m : ℤ} (hm : m ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier m (pt a n))
      atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * π * I * m * a) with hz
  have hterm : ∀ n : ℕ, fourier m (pt a n) = z ^ n := by
    intro n
    rw [pt, fourier_coe_apply, hz, ← Complex.exp_nat_mul]
    push_cast; ring_nf
  have hzne : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have hne : (2 * (π : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : (2 * (π : ℂ) * I) * ((m : ℂ) * a) = (2 * (π : ℂ) * I) * (k : ℂ) := by
      linear_combination hk
    have h3 : (m : ℝ) * a = (k : ℝ) := by
      have := mul_left_cancel₀ hne h2
      exact_mod_cast this
    exact (ha.intCast_mul hm).ne_int k h3
  have hznorm : ‖z‖ = 1 := by rw [hz, Complex.norm_exp]; simp
  have hzz : (0 : ℝ) < ‖z - 1‖ := by simpa [sub_eq_zero] using hzne
  have hfun : (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier m (pt a n))
      = fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n := by
    funext N; simp_rw [hterm]
  rw [hfun]
  have hbound : ∀ N : ℕ, ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n‖ ≤ (2 / ‖z - 1‖) / N := by
    intro N
    have key : ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
      rw [geom_sum_eq hzne, norm_div]
      gcongr
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm]; norm_num
    calc ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n‖
        = (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, z ^ n‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = (2 / ‖z - 1‖) / N := by ring
  exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- Equidistribution holds for every element of the linear span of the characters. -/
lemma tendsto_of_mem_span (a : ℝ) (ha : Irrational a) (f : C(Circ, ℂ))
    (hf : f ∈ span ℂ (Set.range (fourier : ℤ → C(Circ, ℂ)))) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n))
      atTop (𝓝 (∫ x : Circ, f x)) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rcases eq_or_ne m 0 with rfl | hm
      · rw [integral_fourier 0, if_pos rfl]
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        simp only [fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        field_simp
      · rw [integral_fourier m, if_neg hm]
        exact weyl_sum_tendsto a ha hm
  | zero => simp
  | add x y hx hy ihx ihy =>
      simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]
      rw [integral_add (integrable_continuous x) (integrable_continuous y)]
      exact ihx.add ihy
  | smul c x hx ihx =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [integral_const_mul]
      exact (ihx.const_mul c).congr (fun N => by ring)

/-- **Weyl's equidistribution theorem** for continuous complex-valued test functions. -/
theorem tendsto_continuous (a : ℝ) (ha : Irrational a) (f : C(Circ, ℂ)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n))
      atTop (𝓝 (∫ x : Circ, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ :
      ∃ g ∈ span ℂ (Set.range (fourier : ℤ → C(Circ, ℂ))), ‖f - g‖ < ε / 3 := by
    have h : f ∈ (span ℂ (Set.range (fourier : ℤ → C(Circ, ℂ)))).topologicalClosure := by
      rw [span_fourier_closure_eq_top]; trivial
    have h2 : f ∈ closure ((span ℂ (Set.range (fourier : ℤ → C(Circ, ℂ)))) : Set _) := h
    rw [Metric.mem_closure_iff] at h2
    obtain ⟨g, hg, hd⟩ := h2 (ε / 3) (by linarith)
    exact ⟨g, hg, by rwa [← dist_eq_norm]⟩
  have hgt := tendsto_of_mem_span a ha g hg
  rw [Metric.tendsto_atTop] at hgt
  obtain ⟨N₀, hN₀⟩ := hgt (ε / 3) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsum : ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n)
      - (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (pt a n)‖ ≤ ‖f - g‖ := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    have h1 : ‖∑ n ∈ Finset.range N, (f (pt a n) - g (pt a n))‖ ≤ N * ‖f - g‖ := by
      calc ‖∑ n ∈ Finset.range N, (f (pt a n) - g (pt a n))‖
          ≤ ∑ n ∈ Finset.range N, ‖f (pt a n) - g (pt a n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ := by
            refine Finset.sum_le_sum fun n _ => ?_
            simpa using (f - g).norm_coe_le_norm (pt a n)
        _ = N * ‖f - g‖ := by simp [Finset.sum_const]
    rw [inv_mul_le_iff₀ hN0]
    exact h1
  have hint : ‖(∫ x : Circ, g x) - ∫ x : Circ, f x‖ ≤ ‖f - g‖ := by
    rw [← integral_sub (integrable_continuous g) (integrable_continuous f)]
    have hpt : ∀ x, ‖g x - f x‖ ≤ ‖f - g‖ := by
      intro x
      rw [norm_sub_rev]
      simpa using (f - g).norm_coe_le_norm x
    calc ‖∫ x : Circ, (g x - f x)‖
        ≤ ‖f - g‖ * (volume (Set.univ : Set Circ)).toReal :=
          norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)
      _ = ‖f - g‖ := by simp
  have hmid := hN₀ N hNN
  rw [dist_eq_norm] at hmid ⊢
  calc ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n) - ∫ x : Circ, f x‖
      ≤ ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n)
            - (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (pt a n)‖
        + ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (pt a n) - ∫ x : Circ, g x‖
        + ‖(∫ x : Circ, g x) - ∫ x : Circ, f x‖ := by
        have := norm_add₃_le
          (a := (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n)
                - (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (pt a n))
          (b := (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (pt a n) - ∫ x : Circ, g x)
          (c := (∫ x : Circ, g x) - ∫ x : Circ, f x)
        simpa using this
    _ < ε := by linarith

/-- **Weyl's equidistribution theorem** for continuous real-valued test functions. -/
theorem tendsto_continuous_real (a : ℝ) (ha : Irrational a) (f : C(Circ, ℝ)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n))
      atTop (𝓝 (∫ x : Circ, f x)) := by
  have hF := tendsto_continuous a ha
    (ContinuousMap.mk (fun x => ((f x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp (map_continuous f)))
  simp only [ContinuousMap.coe_mk] at hF
  rw [integral_complex_ofReal] at hF
  rw [← tendsto_ofReal_iff]
  refine hF.congr (fun N => ?_)
  push_cast
  ring

end

end Weyl
end Brockian

