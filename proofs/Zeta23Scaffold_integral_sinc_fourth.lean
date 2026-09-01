import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
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

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform intervalIntegral

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/
noncomputable def tent (x : ℝ) : ℝ := max 0 (1 - |x|)

lemma tent_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : tent x = 0 := by
  simp [tent, sub_nonpos.2 hx]

lemma tent_of_mem {x : ℝ} (hx : |x| ≤ 1) : tent x = 1 - |x| := by
  simp [tent, sub_nonneg.2 hx]

lemma tent_neg (x : ℝ) : tent (-x) = tent x := by simp [tent]

lemma continuous_tent : Continuous tent := by unfold tent; fun_prop

/-- Points outside `Ioc (-1) 1` have `1 ≤ |x|`. -/
lemma one_le_abs_of_notMem_Ioc {x : ℝ} (hx : x ∉ Set.Ioc (-1 : ℝ) 1) : 1 ≤ |x| := by
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The complex-valued tent function. -/
noncomputable def tentC (x : ℝ) : ℂ := (tent x : ℂ)

lemma continuous_tentC : Continuous tentC :=
  Complex.continuous_ofReal.comp continuous_tent

lemma hasCompactSupport_tentC : HasCompactSupport tentC := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  have h : 1 ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp [tentC, tent_eq_zero h]

lemma integrable_tentC : Integrable tentC :=
  continuous_tentC.integrable_of_hasCompactSupport hasCompactSupport_tentC

/-- An explicit antiderivative computation: `∫_0^1 2 (1-x) cos (a x) dx = 2 (1 - cos a) / a²`. -/
lemma integral_two_mul_one_sub_mul_cos (a : ℝ) (ha : a ≠ 0) :
    ∫ x in (0:ℝ)..1, 2 * (1 - x) * Real.cos (a * x) = 2 * (1 - Real.cos a) / a ^ 2 := by
  have key : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y : ℝ => 2 * ((1 - y) * Real.sin (a * y) / a - Real.cos (a * y) / a ^ 2))
        (2 * (1 - x) * Real.cos (a * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => Real.sin (a * y)) (Real.cos (a * x) * a) x := by
      simpa using (Real.hasDerivAt_sin (a * x)).comp x ((hasDerivAt_id x).const_mul a)
    have h2 : HasDerivAt (fun y : ℝ => Real.cos (a * y)) (-Real.sin (a * x) * a) x := by
      simpa using (Real.hasDerivAt_cos (a * x)).comp x ((hasDerivAt_id x).const_mul a)
    have h3 : HasDerivAt (fun y : ℝ => (1 - y)) (-1 : ℝ) x := by
      simpa using (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    have h4 := (((h3.mul h1).div_const a).sub (h2.div_const (a ^ 2))).const_mul (2:ℝ)
    convert h4 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key
    ((by fun_prop : Continuous fun x : ℝ => 2 * (1 - x) * Real.cos (a * x)).intervalIntegrable _ _)]
  simp only [Real.sin_zero, Real.cos_zero, mul_zero, mul_one, sub_zero, sub_self, zero_mul,
    zero_div]
  field_simp
  ring

/-- The Fourier transform of the tent function is `sinc (π ξ) ^ 2`. -/
lemma fourier_tentC {ξ : ℝ} (hξ : ξ ≠ 0) : 𝓕 tentC ξ = ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun v => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • tentC v with hF
  have hcF : Continuous F := by
    apply Continuous.smul _ continuous_tentC
    fun_prop
  have step1 : 𝓕 tentC ξ = ∫ v in Set.Ioc (-1:ℝ) 1, F v := by
    rw [Real.fourier_real_eq_integral_exp_smul,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    simp [hF, tentC, tent_eq_zero (one_le_abs_of_notMem_Ioc hx)]
  rw [step1, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  have step2 : ∫ v in (-1:ℝ)..1, F v = ∫ x in (0:ℝ)..1, (F (-x) + F x) := by
    have h1 : IntervalIntegrable (fun x => F (-x)) volume 0 1 :=
      (hcF.comp continuous_neg).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h1 (hcF.intervalIntegrable _ _),
      intervalIntegral.integral_comp_neg F,
      ← intervalIntegral.integral_add_adjacent_intervals (a := (-1:ℝ)) (b := 0) (c := 1)
        (hcF.intervalIntegrable _ _) (hcF.intervalIntegrable _ _)]
    norm_num
  rw [step2]
  have step3 : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      F (-x) + F x = ((2 * (1 - x) * Real.cos ((2 * π * ξ) * x) : ℝ) : ℂ) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h0, h1⟩ := hx
    have habs : |x| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
    have habs' : |(-x)| ≤ 1 := by rwa [abs_neg]
    simp only [hF, tentC, tent_of_mem habs, tent_of_mem habs', abs_neg, abs_of_nonneg h0,
      smul_eq_mul]
    push_cast
    rw [Complex.cos]
    ring_nf
  rw [intervalIntegral.integral_congr step3, intervalIntegral.integral_ofReal,
    integral_two_mul_one_sub_mul_cos (2 * π * ξ) (by positivity)]
  congr 1
  have hpξ : π * ξ ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hpξ]
  have h2 : Real.cos (2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
    have h3 : (2:ℝ) * π * ξ = 2 * (π * ξ) := by ring
    rw [h3, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
  rw [h2, div_pow]
  field_simp
  ring

/-! ## Integrability of `sinc²` -/

lemma sinc_sq_le (y : ℝ) : Real.sinc y ^ 2 ≤ 2 * (1 + y ^ 2)⁻¹ := by
  rcases le_or_gt |y| 1 with h | h
  · have h1 : Real.sinc y ^ 2 ≤ 1 := by
      have := Real.abs_sinc_le_one y
      nlinarith [abs_nonneg (Real.sinc y), sq_abs (Real.sinc y)]
    have h2 : (1:ℝ) ≤ 2 * (1 + y ^ 2)⁻¹ := by
      have hy : y ^ 2 ≤ 1 := by nlinarith [sq_abs y, abs_nonneg y]
      rw [le_mul_inv_iff₀ (by positivity)]
      linarith
    linarith
  · have hy0 : y ≠ 0 := by
      intro h0; rw [h0] at h; simp at h; linarith
    have hs : Real.sinc y ^ 2 ≤ (y ^ 2)⁻¹ := by
      rw [Real.sinc_of_ne_zero hy0, div_pow]
      have h1 : Real.sin y ^ 2 ≤ 1 := by
        nlinarith [Real.neg_one_le_sin y, Real.sin_le_one y]
      have hy2 : 0 < y ^ 2 := by positivity
      rw [div_le_iff₀ hy2, inv_mul_cancel₀ hy2.ne']
      linarith
    have h2 : (y ^ 2)⁻¹ ≤ 2 * (1 + y ^ 2)⁻¹ := by
      have hy2 : 1 < y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
      rw [inv_le_iff_one_le_mul₀ (by linarith), mul_assoc, mul_comm ((1 + y ^ 2)⁻¹) (y ^ 2),
        ← mul_assoc, le_mul_inv_iff₀ (show (0:ℝ) < 1 + y ^ 2 by positivity)]
      linarith
    linarith

lemma integrable_sincSq : Integrable (fun ξ : ℝ => Real.sinc (π * ξ) ^ 2) := by
  have hb : Integrable (fun ξ : ℝ => 2 * (1 + (π * ξ) ^ 2)⁻¹) := by
    have h : Integrable (fun x : ℝ => (1 + (π * x) ^ 2)⁻¹) :=
      (integrable_comp_mul_left_iff (fun x : ℝ => (1 + x ^ 2)⁻¹) Real.pi_ne_zero).2
        integrable_inv_one_add_sq
    exact h.const_mul 2
  refine hb.mono' ?_ ?_
  · exact ((Real.continuous_sinc.comp (by fun_prop)).pow 2).aestronglyMeasurable
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sinc_sq_le _

lemma ae_ne_zero : ∀ᵐ x : ℝ, x ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  simp

lemma fourier_tentC_ae : (𝓕 tentC) =ᵐ[volume] (fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ)) := by
  filter_upwards [ae_ne_zero] with ξ hξ using fourier_tentC hξ

lemma integrable_fourier_tentC : Integrable (𝓕 tentC) := by
  refine (Integrable.congr ?_ fourier_tentC_ae.symm)
  exact integrable_sincSq.ofReal

/-! ## Plancherel step -/

/-- The multiplication formula for the Fourier transform on `ℝ`. -/
lemma integral_fourier_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ : ℝ, (𝓕 f ξ) * (g ξ) = ∫ x : ℝ, f x * 𝓕 g x := by
  have hflip : (innerₗ ℝ).flip = (innerₗ ℝ) := by ext; simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (L := innerₗ ℝ) (e := 𝐞) (f := f) (g := g)
    Real.continuous_fourierChar (by fun_prop) hf hg
  rw [hflip] at h
  simpa [smul_eq_mul] using h

/-- Fourier inversion, in the form `𝓕 (𝓕 f) x = f (-x)`. -/
lemma fourier_fourier_eq {f : ℝ → ℂ} (hc : Continuous f) (hf : Integrable f)
    (hFf : Integrable (𝓕 f)) (x : ℝ) : 𝓕 (𝓕 f) x = f (-x) := by
  have h := congrFun (hc.fourierInv_fourier_eq hf hFf) (-x)
  rwa [Real.fourierInv_eq_fourier_neg, neg_neg] at h

lemma integral_fourier_sq :
    ∫ ξ : ℝ, (𝓕 tentC ξ) * (𝓕 tentC ξ) = ∫ x : ℝ, tentC x * tentC (-x) := by
  rw [integral_fourier_mul integrable_tentC integrable_fourier_tentC]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fourier_fourier_eq continuous_tentC integrable_tentC integrable_fourier_tentC]

/-! ## The elementary integral `∫ tent² = 2/3` -/

lemma integral_tent_sq : ∫ x : ℝ, tent x ^ 2 = 2 / 3 := by
  have hc : Continuous (fun x : ℝ => tent x ^ 2) := continuous_tent.pow 2
  have h1 : ∫ x in Set.Ioc (-1:ℝ) 1, tent x ^ 2 = ∫ x : ℝ, tent x ^ 2 := by
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [tent_eq_zero (one_le_abs_of_notMem_Ioc hx)]
  rw [← h1, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  have hsplit : ∫ x in (-1:ℝ)..1, tent x ^ 2 = ∫ x in (0:ℝ)..1, (tent (-x) ^ 2 + tent x ^ 2) := by
    have h2 : IntervalIntegrable (fun x : ℝ => tent (-x) ^ 2) volume 0 1 :=
      (hc.comp continuous_neg).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h2 (hc.intervalIntegrable _ _),
      intervalIntegral.integral_comp_neg (fun x : ℝ => tent x ^ 2),
      ← intervalIntegral.integral_add_adjacent_intervals (a := (-1:ℝ)) (b := 0) (c := 1)
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    norm_num
  rw [hsplit]
  have hcongr : ∀ x ∈ Set.uIcc (0:ℝ) 1, tent (-x) ^ 2 + tent x ^ 2 = 2 * (1 - x) ^ 2 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h0, h1⟩ := hx
    have habs : |x| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
    rw [tent_of_mem habs, tent_of_mem (by rwa [abs_neg]), abs_neg, abs_of_nonneg h0]
    ring
  rw [intervalIntegral.integral_congr hcongr]
  simp only [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2) 1]
  norm_num

/-! ## Assembling the pieces -/

lemma integral_sincSq_sq : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = 2 / 3 := by
  have hL : ∫ ξ : ℝ, (𝓕 tentC ξ) * (𝓕 tentC ξ)
      = ((∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := by
    have e1 : ∫ ξ : ℝ, (𝓕 tentC ξ) * (𝓕 tentC ξ)
        = ∫ ξ : ℝ, ((Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [fourier_tentC_ae] with ξ hξ
      rw [hξ]
      push_cast
      ring
    rw [e1]
    exact _root_.integral_complex_ofReal
  have hR : ∫ x : ℝ, tentC x * tentC (-x) = ((∫ x : ℝ, tent x ^ 2 : ℝ) : ℂ) := by
    have e2 : ∫ x : ℝ, tentC x * tentC (-x) = ∫ x : ℝ, ((tent x ^ 2 : ℝ) : ℂ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [tentC, tent_neg]
      push_cast
      ring
    rw [e2]
    exact _root_.integral_complex_ofReal
  have h := integral_fourier_sq
  rw [hL, hR, integral_tent_sq] at h
  exact_mod_cast h

lemma integral_sinc_pow_four : ∫ x : ℝ, Real.sinc x ^ 4 = 2 * π / 3 := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun u : ℝ => Real.sinc u ^ 4) π
  rw [integral_sincSq_sq] at h
  rw [abs_of_pos (inv_pos.2 Real.pi_pos), smul_eq_mul] at h
  field_simp at h
  linarith [h, Real.pi_pos]

/-- `∫_ℝ (sin x / x)^4 dx = 2π/3`. -/
theorem integral_sinc_fourth : ∫ x : ℝ, (Real.sin x / x) ^ 4 = 2 * Real.pi / 3 := by
  rw [← integral_sinc_pow_four]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_ne_zero] with x hx
  rw [Real.sinc_of_ne_zero hx]

end Zeta23Scaffold

