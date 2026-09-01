import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped FourierTransform

open MeasureTheory Complex

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-! ## The tent function and its Fourier transform

The proof of `∫ (sin x / x) ^ 2 dx = π` goes through Fourier inversion applied to the
tent (triangle) function `x ↦ max 0 (1 - |x|)`, whose Fourier transform is
`w ↦ (sin (π w) / (π w)) ^ 2`. -/

/-- The triangle (tent) function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function. -/
noncomputable def tri (x : ℝ) : ℂ := ((max 0 (1 - |x|) : ℝ) : ℂ)

lemma continuous_tri : Continuous tri := by
  unfold tri
  fun_prop

lemma tri_zero : tri 0 = 1 := by simp [tri]

lemma tri_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : tri x = 0 := by
  have : (1 : ℝ) - |x| ≤ 0 := by linarith
  simp [tri, max_eq_left this]

lemma hasCompactSupport_tri : HasCompactSupport tri := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  apply tri_eq_zero_of_one_le_abs
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma integrable_tri : Integrable tri :=
  continuous_tri.integrable_of_hasCompactSupport hasCompactSupport_tri

/-- Derivative of `t ↦ exp (z t) * (A + B t)`. -/
lemma hasDerivAt_expmul (z A B : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (z * t) * (A + B * t))
      (Complex.exp (z * x) * ((z * A + B) + z * B * x)) x := by
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => z * (t : ℂ)) (z * 1) x := hx.const_mul z
  have h2 := (h1.cexp).mul ((hx.const_mul B).const_add A)
  convert h2 using 1
  ring

lemma integral_expmul (z A B : ℂ) (a b : ℝ) :
    (∫ x in a..b, Complex.exp (z * x) * ((z * A + B) + z * B * x)) =
      Complex.exp (z * b) * (A + B * b) - Complex.exp (z * a) * (A + B * a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_expmul z A B x)
  apply Continuous.intervalIntegrable
  fun_prop

lemma integral_tri_pieces (z : ℂ) (hz : z ≠ 0) :
    (∫ x in (0:ℝ)..1, Complex.exp (z * x) * (1 - x))
      + (∫ x in (-1:ℝ)..0, Complex.exp (z * x) * (1 + x))
      = (Complex.exp z + Complex.exp (-z) - 2) / z ^ 2 := by
  have h1 := integral_expmul z ((1 + 1 / z) / z) (-1 / z) 0 1
  have h2 := integral_expmul z ((1 - 1 / z) / z) (1 / z) (-1) 0
  have e1 : ∀ x : ℝ, Complex.exp (z * x) * ((z * ((1 + 1 / z) / z) + (-1 / z)) + z * (-1 / z) * x)
      = Complex.exp (z * x) * (1 - x) := by
    intro x; congr 1; field_simp; ring
  have e2 : ∀ x : ℝ, Complex.exp (z * x) * ((z * ((1 - 1 / z) / z) + (1 / z)) + z * (1 / z) * x)
      = Complex.exp (z * x) * (1 + x) := by
    intro x; congr 1; field_simp; ring
  simp_rw [e1] at h1
  simp_rw [e2] at h2
  rw [h1, h2]
  push_cast
  field_simp
  simp only [mul_zero, Complex.exp_zero]
  ring

/-- Splitting `∫ exp (z x) * tri x` into the two linear pieces. -/
lemma integral_exp_mul_tri_split (z : ℂ) :
    (∫ x : ℝ, Complex.exp (z * x) * tri x)
      = (∫ x in (-1:ℝ)..0, Complex.exp (z * x) * (1 + x))
        + (∫ x in (0:ℝ)..1, Complex.exp (z * x) * (1 - x)) := by
  have hcont : Continuous (fun x : ℝ => Complex.exp (z * x) * tri x) :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (z * x)).mul continuous_tri
  have hsupp : ∀ x ∉ Set.Ioc (-1:ℝ) 1, Complex.exp (z * x) * tri x = 0 := by
    intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have h : 1 ≤ |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    rw [tri_eq_zero_of_one_le_abs h, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (b := (0:ℝ)) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hx
    simp only [Set.mem_Icc] at hx
    have h1 : |x| = -x := abs_of_nonpos hx.2
    have h4 : (max 0 (1 - |x|) : ℝ) = 1 + x := by
      rw [h1, max_eq_right (by linarith [hx.1] : (0:ℝ) ≤ 1 - -x)]; ring
    simp only [tri, h4]
    push_cast
    ring
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [Set.mem_Icc] at hx
    have h1 : |x| = x := abs_of_nonneg hx.1
    have h4 : (max 0 (1 - |x|) : ℝ) = 1 - x := by
      rw [h1, max_eq_right (by linarith [hx.2] : (0:ℝ) ≤ 1 - x)]
    simp only [tri, h4]
    push_cast
    ring

lemma integral_exp_mul_tri (z : ℂ) (hz : z ≠ 0) :
    (∫ x : ℝ, Complex.exp (z * x) * tri x) = (Complex.exp z + Complex.exp (-z) - 2) / z ^ 2 := by
  rw [integral_exp_mul_tri_split z, add_comm, integral_tri_pieces z hz]

lemma exp_add_exp_neg (u : ℂ) :
    Complex.exp (u * Complex.I) + Complex.exp (-(u * Complex.I)) = 2 * Complex.cos u := by
  rw [show -(u * Complex.I) = (-u) * Complex.I by ring, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  ring

lemma quotient_eval (w : ℝ) (hw : w ≠ 0) (z : ℂ) (hzdef : z = ((-2 * π * w : ℝ) : ℂ) * Complex.I) :
    (Complex.exp z + Complex.exp (-z) - 2) / z ^ 2
      = (((Real.sin (π * w) / (π * w)) ^ 2 : ℝ) : ℂ) := by
  have hpw : (π * w) ≠ 0 := mul_ne_zero Real.pi_ne_zero hw
  have hz2 : z ^ 2 = ((-(2 * π * w) ^ 2 : ℝ) : ℂ) := by
    rw [hzdef]; push_cast; ring_nf; simp [Complex.I_sq]
  have hexp : Complex.exp z + Complex.exp (-z) = ((2 * Real.cos (2 * π * w) : ℝ) : ℂ) := by
    rw [hzdef]
    push_cast
    rw [show (-2 * (π : ℂ) * (w : ℂ) * Complex.I)
        = ((2 * (π : ℂ) * (w : ℂ)) * Complex.I) * (-1) by ring]
    rw [show (((2 * (π : ℂ) * (w : ℂ)) * Complex.I) * (-1))
        = -((2 * (π : ℂ) * (w : ℂ)) * Complex.I) by ring]
    rw [neg_neg, add_comm]
    exact exp_add_exp_neg _
  rw [hexp, hz2]
  have hcos : 2 * Real.cos (2 * π * w) - 2 = -(4 * Real.sin (π * w) ^ 2) := by
    have h : Real.cos (2 * (π * w)) = 1 - 2 * Real.sin (π * w) ^ 2 := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (π * w)]
    rw [show 2 * π * w = 2 * (π * w) by ring, h]; ring
  rw [show ((2 * Real.cos (2 * π * w) : ℝ) : ℂ) - 2
      = (((2 * Real.cos (2 * π * w) - 2 : ℝ)) : ℂ) by push_cast; ring, hcos,
    ← Complex.ofReal_div]
  congr 1
  field_simp
  ring

/-- The Fourier transform of the tent function is `w ↦ (sin (π w) / (π w)) ^ 2`
(away from `w = 0`). -/
lemma fourier_tri (w : ℝ) (hw : w ≠ 0) :
    𝓕 tri w = (((Real.sin (π * w) / (π * w)) ^ 2 : ℝ) : ℂ) := by
  set z : ℂ := ((-2 * π * w : ℝ) : ℂ) * Complex.I with hzdef
  have hz : z ≠ 0 := by
    have hr : (-2 * π * w : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw
    exact mul_ne_zero (by simpa using hr) Complex.I_ne_zero
  have h1 : 𝓕 tri w = ∫ v : ℝ, Complex.exp (z * v) * tri v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, hzdef]
    congr 2
    push_cast
    ring
  rw [h1, integral_exp_mul_tri z hz, quotient_eval w hw z hzdef]

/-! ## Integrability of the squared sinc function -/

lemma sq_sin_div_le (t : ℝ) : (Real.sin t / t) ^ 2 ≤ 2 * (1 + t ^ 2)⁻¹ := by
  rcases eq_or_ne t 0 with rfl | ht
  · norm_num
  have ht2 : 0 < t ^ 2 := by positivity
  have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hs1 : Real.sin t ^ 2 ≤ t ^ 2 := Real.sin_sq_le_sq
  have hs2 : Real.sin t ^ 2 ≤ 1 := Real.sin_sq_le_one t
  have hs0 : (0 : ℝ) ≤ Real.sin t ^ 2 := sq_nonneg _
  rw [div_pow, mul_comm 2 _, ← div_eq_inv_mul, div_le_div_iff₀ ht2 h1]
  nlinarith

lemma integrable_sin_div_sq : Integrable (fun w : ℝ => (Real.sin (π * w) / (π * w)) ^ 2) := by
  have h0 : Integrable (fun w : ℝ => (1 + (π * w) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' (R := π) Real.pi_ne_zero
  have hbig : Integrable (fun w : ℝ => 2 * (1 + (π * w) ^ 2)⁻¹) := h0.const_mul 2
  refine Integrable.mono' hbig
    ((by measurability : Measurable fun w : ℝ =>
      (Real.sin (π * w) / (π * w)) ^ 2).aestronglyMeasurable) ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact sq_sin_div_le (π * w)

/-! ## Fourier inversion -/

lemma ae_ne_zero : ∀ᵐ w : ℝ, w ≠ 0 := by
  filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := (0:ℝ)))] with w hw
  simpa using hw

lemma fourier_tri_ae :
    𝓕 tri =ᵐ[volume] fun w : ℝ => (((Real.sin (π * w) / (π * w)) ^ 2 : ℝ) : ℂ) := by
  filter_upwards [ae_ne_zero] with w hw
  exact fourier_tri w hw

lemma integrable_fourier_tri : Integrable (𝓕 tri) :=
  (integrable_sin_div_sq.ofReal).congr fourier_tri_ae.symm

lemma integral_sin_div_pi_sq : (∫ w : ℝ, (Real.sin (π * w) / (π * w)) ^ 2) = 1 := by
  have hinv : 𝓕⁻ (𝓕 tri) 0 = tri 0 :=
    integrable_tri.fourierInv_fourier_eq integrable_fourier_tri continuous_tri.continuousAt
  have hleft : 𝓕⁻ (𝓕 tri) 0 = ∫ w : ℝ, 𝓕 tri w := by
    rw [Real.fourierInv_eq]
    simp
  rw [hleft, tri_zero, integral_congr_ae fourier_tri_ae, integral_complex_ofReal] at hinv
  exact_mod_cast hinv

/-- The normalization integral of the sine kernel: `∫ (sin x / x) ^ 2 dx = π`
over the real line, as a Bochner integral with respect to Lebesgue measure.
(The integrand is given the value `0` at `x = 0`, which does not affect the integral.) -/
theorem integral_sinc_sq : (∫ x : ℝ, (Real.sin x / x) ^ 2) = π := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => (Real.sin x / x) ^ 2) π
  rw [integral_sin_div_pi_sq] at h
  rw [smul_eq_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ π⁻¹)] at h
  have h2 : π * 1 = π * (π⁻¹ * ∫ y : ℝ, (Real.sin y / y) ^ 2) := by rw [← h]
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul] at h2
  exact h2.symm

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

