import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The `L^∞`–`W^{1,1}` endpoint estimate in dimension one: for a continuously
differentiable, compactly supported function `f : ℝ → ℝ` one has
`‖f‖_∞ ≤ (1/2) * ‖f'‖_1`. -/
theorem sup_le_half_integral_abs_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (x : ℝ) :
    |f x| ≤ (1 / 2) * ∫ t : ℝ, |deriv f t| := by
  have hgc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hgs : HasCompactSupport (deriv f) := hsupp.deriv
  have hgi : MeasureTheory.Integrable (deriv f) := hgc.integrable_of_hasCompactSupport hgs
  have habs : MeasureTheory.Integrable (fun t : ℝ => |deriv f t|) := hgi.abs
  have hderiv : ∀ y : ℝ, HasDerivAt f (deriv f y) y := fun y =>
    (hf.differentiable (by norm_num) y).hasDerivAt
  obtain ⟨R, hR⟩ := hsupp.isBounded.subset_closedBall (0 : ℝ)
  set a : ℝ := max R |x| + 1 with ha
  have hxa : |x| < a := by
    have : |x| ≤ max R |x| := le_max_right _ _
    linarith
  have hRa : R < a := by
    have : R ≤ max R |x| := le_max_left _ _
    linarith
  have hapos : (0 : ℝ) < a := by linarith [abs_nonneg x]
  have hvan : ∀ y : ℝ, R < |y| → f y = 0 := by
    intro y hy
    have hny : y ∉ tsupport f := by
      intro h
      have := hR h
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith
    exact image_eq_zero_of_notMem_tsupport hny
  have hfa : f a = 0 := by
    apply hvan
    rw [abs_of_pos hapos]
    exact hRa
  have hfna : f (-a) = 0 := by
    apply hvan
    rw [abs_neg, abs_of_pos hapos]
    exact hRa
  have hax : -a ≤ x := by
    have := neg_abs_le x
    linarith
  have hxa' : x ≤ a := le_of_lt (lt_of_le_of_lt (le_abs_self x) hxa)
  have h1 : ∫ y in (-a)..x, deriv f y = f x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hgi.intervalIntegrable), hfna, sub_zero]
  have h2 : ∫ y in x..a, deriv f y = -f x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hgi.intervalIntegrable), hfa, zero_sub]
  have b1 : |f x| ≤ ∫ y in (-a)..x, |deriv f y| := by
    rw [← h1]
    exact intervalIntegral.abs_integral_le_integral_abs hax
  have b2 : |f x| ≤ ∫ y in x..a, |deriv f y| := by
    have h : |∫ y in x..a, deriv f y| ≤ ∫ y in x..a, |deriv f y| :=
      intervalIntegral.abs_integral_le_integral_abs hxa'
    rw [h2, abs_neg] at h
    exact h
  have hsum : (∫ y in (-a)..x, |deriv f y|) + (∫ y in x..a, |deriv f y|)
      = ∫ y in (-a)..a, |deriv f y| :=
    intervalIntegral.integral_add_adjacent_intervals
      (habs.intervalIntegrable) (habs.intervalIntegrable)
  have hle : (∫ y in (-a)..a, |deriv f y|) ≤ ∫ t : ℝ, |deriv f t| := by
    rw [intervalIntegral.integral_of_le (by linarith : (-a : ℝ) ≤ a)]
    exact MeasureTheory.setIntegral_le_integral habs
      (Filter.Eventually.of_forall fun t => abs_nonneg _)
  linarith

/-- Applying the endpoint estimate to `f ^ 2` gives `‖f‖_∞ ^ 2 ≤ ∫ |f| * |f'|`. -/
theorem sq_le_integral_abs_mul_abs_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (x : ℝ) :
    (f x) ^ 2 ≤ ∫ t : ℝ, |f t| * |deriv f t| := by
  have hderiv : ∀ y : ℝ, HasDerivAt f (deriv f y) y := fun y =>
    (hf.differentiable (by norm_num) y).hasDerivAt
  have hg : ContDiff ℝ 1 (fun t : ℝ => f t * f t) := hf.mul hf
  have hgs : HasCompactSupport (fun t : ℝ => f t * f t) := hsupp.mul_right
  have hd : ∀ t : ℝ, deriv (fun y : ℝ => f y * f y) t = 2 * (f t * deriv f t) := by
    intro t
    have h : HasDerivAt (fun y : ℝ => f y * f y) (deriv f t * f t + f t * deriv f t) t :=
      (hderiv t).mul (hderiv t)
    rw [h.deriv]; ring
  have habs : ∀ t : ℝ, |deriv (fun y : ℝ => f y * f y) t| = 2 * (|f t| * |deriv f t|) := by
    intro t
    rw [hd t, abs_mul, abs_mul]
    norm_num
  have key := sup_le_half_integral_abs_deriv hg hgs x
  rw [show |f x * f x| = (f x) ^ 2 by
    rw [abs_of_nonneg (mul_self_nonneg (f x))]; ring] at key
  have hint : (∫ t : ℝ, |deriv (fun y : ℝ => f y * f y) t|)
      = 2 * ∫ t : ℝ, |f t| * |deriv f t| := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall habs)
  rw [hint] at key
  linarith

/-- **Gagliardo–Nirenberg interpolation inequality**, base case in dimension one:
for a continuously differentiable, compactly supported `f : ℝ → ℝ`,
`‖f‖_∞ ^ 2 ≤ ‖f‖_2 * ‖f'‖_2`, i.e. `‖f‖_∞ ≤ ‖f‖_2 ^ (1/2) * ‖f'‖_2 ^ (1/2)`. -/
theorem nirenberg_gagliardo {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (x : ℝ) :
    (f x) ^ 2 ≤ Real.sqrt (∫ t : ℝ, (f t) ^ 2) * Real.sqrt (∫ t : ℝ, (deriv f t) ^ 2) := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hgs : HasCompactSupport (deriv f) := hsupp.deriv
  have hmf : MeasureTheory.MemLp (fun t : ℝ => |f t|) (ENNReal.ofReal 2) :=
    (hfc.abs).memLp_of_hasCompactSupport hsupp.abs
  have hmg : MeasureTheory.MemLp (fun t : ℝ => |deriv f t|) (ENNReal.ofReal 2) :=
    (hgc.abs).memLp_of_hasCompactSupport hgs.abs
  have hconj : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have holder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Filter.Eventually.of_forall fun t : ℝ => abs_nonneg (f t))
    (Filter.Eventually.of_forall fun t : ℝ => abs_nonneg (deriv f t)) hmf hmg
  have e1 : (∫ t : ℝ, |f t| ^ (2 : ℝ)) = ∫ t : ℝ, (f t) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show |f t| ^ (2 : ℝ) = f t ^ 2
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have e2 : (∫ t : ℝ, |deriv f t| ^ (2 : ℝ)) = ∫ t : ℝ, (deriv f t) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show |deriv f t| ^ (2 : ℝ) = deriv f t ^ 2
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [e1, e2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at holder
  exact le_trans (sq_le_integral_abs_mul_abs_deriv hf hsupp x) holder

end Frontier

