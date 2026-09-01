import Mathlib
/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Complex
open scoped FourierTransform

noncomputable section

namespace Zeta23Scaffold

/-- The tent function `t ↦ max (1 - |t|) 0`. -/
def tentR (t : ℝ) : ℝ := max (1 - |t|) 0

/-- The tent function, complex valued. -/
def tent (t : ℝ) : ℂ := (tentR t : ℂ)

lemma continuous_tentR : Continuous tentR := by
  unfold tentR; fun_prop

lemma continuous_tent : Continuous tent :=
  Complex.continuous_ofReal.comp continuous_tentR

lemma tentR_eq_zero {t : ℝ} (h : 1 ≤ |t|) : tentR t = 0 := by
  simp only [tentR, max_eq_right_iff]
  linarith

lemma tentR_of_mem {t : ℝ} (h : |t| ≤ 1) : tentR t = 1 - |t| := by
  simp only [tentR, max_eq_left_iff]
  linarith

lemma hasCompactSupport_tent : HasCompactSupport tent := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  have h1 : 1 ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp [tent, tentR_eq_zero h1]

lemma integrable_tent : Integrable tent :=
  continuous_tent.integrable_of_hasCompactSupport hasCompactSupport_tent

/-- Reduce an integral against the tent function to an interval integral. -/
lemma integral_tent_mul (g : ℝ → ℂ) :
    ∫ v : ℝ, g v * tent v = ∫ v in (-1 : ℝ)..1, g v * ((1 - |v| : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Ioc (-1 : ℝ) 1) (f := fun v => g v * tent v)]
  · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    simp only [Set.mem_Ioc] at hv
    have h1 : |v| ≤ 1 := abs_le.2 ⟨hv.1.le, hv.2⟩
    simp [tent, tentR_of_mem h1]
  · intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have h1 : 1 ≤ |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    simp [tent, tentR_eq_zero h1]

/-- Folding the tent integral onto `[0, 1]`, where the oscillating factor becomes a cosine. -/
lemma tent_fourier_aux (a : ℝ) :
    ∫ v in (-1 : ℝ)..1, Complex.exp ((↑(a * v)) * I) * ((1 - |v| : ℝ) : ℂ)
      = ((2 * ∫ v in (0 : ℝ)..1, (1 - v) * Real.cos (a * v) : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun v => Complex.exp ((↑(a * v)) * I) * ((1 - |v| : ℝ) : ℂ) with hF
  have hcont : Continuous F := by rw [hF]; fun_prop
  have hcont' : Continuous fun v : ℝ => F (-v) := hcont.comp continuous_neg
  have hneg : (∫ x in (-1 : ℝ)..0, F x) = ∫ x in (0 : ℝ)..1, F (-x) := by
    rw [intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (f := F)]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hneg,
    ← intervalIntegral.integral_add (hcont'.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  rw [show ((2 * ∫ v in (0 : ℝ)..1, (1 - v) * Real.cos (a * v) : ℝ) : ℂ)
      = ∫ v in (0 : ℝ)..1, ((2 * ((1 - v) * Real.cos (a * v)) : ℝ) : ℂ) by
    rw [intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
  simp only [hF, abs_of_nonneg hv.1, abs_neg, mul_neg]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

lemma real_tent_cos (a : ℝ) (ha : a ≠ 0) :
    ∫ v in (0 : ℝ)..1, (1 - v) * Real.cos (a * v) = (1 - Real.cos a) / a ^ 2 := by
  have key : ∀ v ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => (1 - t) * Real.sin (a * t) / a - Real.cos (a * t) / a ^ 2)
        ((1 - v) * Real.cos (a * v)) v := by
    intro v _
    have h1 : HasDerivAt (fun t : ℝ => a * t) a v := by
      simpa using (hasDerivAt_id v).const_mul a
    have hs : HasDerivAt (fun t : ℝ => Real.sin (a * t)) (Real.cos (a * v) * a) v :=
      (Real.hasDerivAt_sin (a * v)).comp v h1
    have hc : HasDerivAt (fun t : ℝ => Real.cos (a * t)) (-Real.sin (a * v) * a) v :=
      (Real.hasDerivAt_cos (a * v)).comp v h1
    have hlin : HasDerivAt (fun t : ℝ => 1 - t) (-1) v := by
      simpa using (hasDerivAt_id v).const_sub 1
    have h := ((hlin.mul hs).div_const a).sub (hc.div_const (a ^ 2))
    convert h using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key]
  · simp
    field_simp
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The Fourier transform of the tent function is `sinc (π ξ) ^ 2`. -/
lemma fourier_tent (ξ : ℝ) : 𝓕 tent ξ = ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hrw : ∀ v : ℝ, Complex.exp ((↑(-2 * π * v * ξ)) * I) • tent v
      = Complex.exp ((↑((-2 * π * ξ) * v)) * I) * tent v := by
    intro v
    rw [smul_eq_mul]
    ring_nf
  simp_rw [hrw]
  rw [integral_tent_mul, tent_fourier_aux]
  rw [Complex.ofReal_inj]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp only [Real.sinc_zero, mul_zero, one_pow, zero_mul, Real.cos_zero, mul_one]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    norm_num
  · have ha : (-2 * π * ξ) ≠ 0 := by
      have := Real.pi_ne_zero
      simp only [ne_eq, mul_eq_zero, not_or]
      push_neg
      exact ⟨⟨by norm_num, this⟩, hξ⟩
    rw [real_tent_cos _ ha]
    have hpi : π * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
    rw [Real.sinc_of_ne_zero hpi]
    have hc : Real.cos (-2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
      rw [show (-2 * π * ξ) = -(2 * (π * ξ)) by ring, Real.cos_neg, Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
    rw [hc]
    field_simp
    ring

lemma integrable_sinc_sq : Integrable (fun x : ℝ => Real.sinc x ^ 2) := by
  have hint : Integrable (fun x : ℝ => 2 * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 2
  refine hint.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [show (2 : ℝ) * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) by ring, le_div_iff₀ hpos]
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  · rw [Real.sinc_of_ne_zero hx]
    have h1 : Real.sin x ^ 2 ≤ x ^ 2 := by
      nlinarith [Real.abs_sin_le_abs (x := x), sq_abs x, sq_abs (Real.sin x),
        abs_nonneg (Real.sin x)]
    have h2 : Real.sin x ^ 2 ≤ 1 := by nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hx2]
    nlinarith

lemma integrable_fourier_tent : Integrable (𝓕 tent) := by
  have h : Integrable (fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ)) :=
    Integrable.ofReal (integrable_sinc_sq.comp_mul_left' Real.pi_ne_zero)
  exact h.congr (Filter.Eventually.of_forall fun ξ => (fourier_tent ξ).symm)

lemma integral_sinc_sq_eq_pi : ∫ x : ℝ, Real.sinc x ^ 2 = π := by
  have hinv := continuous_tent.fourierInv_fourier_eq integrable_tent integrable_fourier_tent
  have h0 : 𝓕⁻ (𝓕 tent) 0 = ∫ ξ : ℝ, 𝓕 tent ξ := by
    rw [Real.fourierInv_eq']
    simp
  have h1 : (∫ ξ : ℝ, 𝓕 tent ξ) = 1 := by
    rw [← h0, hinv]
    simp [tent, tentR, abs_zero]
  have h2 : (∫ ξ : ℝ, Real.sinc (π * ξ) ^ 2) = 1 := by
    have : (∫ ξ : ℝ, ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ)) = 1 := by
      rw [← h1]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => (fourier_tent ξ).symm)
    rw [_root_.integral_complex_ofReal] at this
    exact_mod_cast this
  rw [MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => Real.sinc x ^ 2) π] at h2
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ π⁻¹), smul_eq_mul] at h2
  field_simp at h2
  linarith

/-- The normalization integral of the sine kernel: `∫ (sin x / x)^2 dx = π`. -/
theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  rw [← integral_sinc_sq_eq_pi]
  apply integral_congr_ae
  have hae : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hae] with x hx
  rw [Real.sinc_of_ne_zero hx]

end Zeta23Scaffold

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

