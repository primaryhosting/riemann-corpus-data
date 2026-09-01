/-
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is rendered as a plain block comment because Lean 4 requires
-- `import` commands to precede every command, including module docstrings `/-! ... -/`.)

import Mathlib

/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Set
open scoped ContDiff

namespace Brockian.DilationGenerator

/-- The Berry–Keating dilation generator `A f = i·((1/2)·f + x·f')` is symmetric on the
`C_c^∞(0,∞)` core: `∫ (A f) · conj g = ∫ f · conj (A g)` over `(0, ∞)`. -/
theorem symmetric_on_core (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfs : tsupport f ⊆ Set.Ioi 0) (hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi (0:ℝ),
        (Complex.I * ((1/2) * f x + x * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0:ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + x * deriv g x)) := by
  -- Smoothness at order 1.
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hfd : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    (hf1.differentiable (by norm_num) x).hasDerivAt
  have hgd : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    (hg1.differentiable (by norm_num) x).hasDerivAt
  have hfc' : Continuous f := hf1.continuous
  have hgc' : Continuous g := hg1.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hdgc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  -- The conjugate of `g`.
  set G : ℝ → ℂ := fun x => starRingEnd ℂ (g x) with hG
  have hGd : ∀ x, HasDerivAt G (starRingEnd ℂ (deriv g x)) x := fun x => by
    simpa [hG, Complex.star_def] using (hgd x).star
  have hG1 : ContDiff ℝ 1 G := (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hg1
  have hGcont : Continuous G := hG1.continuous
  -- The primitive `H x = x * f x * conj (g x)` and its derivative `F`.
  set H : ℝ → ℂ := fun x => (x : ℂ) * f x * G x with hH
  set F : ℝ → ℂ := fun x =>
    f x * G x + (x : ℂ) * deriv f x * G x + (x : ℂ) * f x * starRingEnd ℂ (deriv g x) with hF
  have hid1 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := fun x => by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have hHd : ∀ x, HasDerivAt H (F x) x := by
    intro x
    have h := ((hid1 x).mul (hfd x)).mul (hGd x)
    refine h.congr_deriv ?_
    simp [hF]; ring
  have hderivH : deriv H = F := funext fun x => (hHd x).deriv
  have hHcd : ContDiff ℝ 1 H := by
    have hid : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ)) :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff.of_le le_top
    exact (hid.mul hf1).mul hG1
  -- Vanishing outside the support of `f`.
  have hzero : ∀ x ∉ tsupport f, f x = 0 ∧ deriv f x = 0 := by
    intro x hx
    refine ⟨image_eq_zero_of_notMem_tsupport hx, ?_⟩
    by_contra hne
    exact hx (support_deriv_subset (by simpa [Function.mem_support] using hne))
  have hHcs : HasCompactSupport H := by
    refine HasCompactSupport.intro hfc (fun x hx => ?_)
    simp [hH, (hzero x hx).1]
  have hFcs : HasCompactSupport F := by
    refine HasCompactSupport.intro hfc (fun x hx => ?_)
    simp [hF, (hzero x hx).1, (hzero x hx).2]
  have hFcont : Continuous F := by
    have : Continuous fun x : ℝ => (x : ℂ) := Complex.continuous_ofReal
    fun_prop
  -- The boundary term vanishes: `∫_{(0,∞)} H' = -H 0 = 0`.
  have key : ∫ x in Set.Ioi (0:ℝ), F x = 0 := by
    have h := HasCompactSupport.integral_Ioi_deriv_eq hHcd hHcs 0
    rw [hderivH] at h
    simpa [hH] using h
  -- Pointwise algebraic identity.
  set A : ℝ → ℂ := fun x =>
    (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x) with hA
  have hpt : ∀ x : ℝ,
      f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x))
        = A x - Complex.I * F x := by
    intro x
    simp only [hA, hF, hG, map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  -- Integrability.
  have hAcont : Continuous A := by
    have : Continuous fun x : ℝ => (x : ℂ) := Complex.continuous_ofReal
    have : Continuous fun x : ℝ => starRingEnd ℂ (g x) := hGcont
    fun_prop
  have hAcs : HasCompactSupport A := by
    refine HasCompactSupport.intro hfc (fun x hx => ?_)
    simp [hA, (hzero x hx).1, (hzero x hx).2]
  have hAint : IntegrableOn A (Set.Ioi (0:ℝ)) :=
    (hAcont.integrable_of_hasCompactSupport hAcs).integrableOn
  have hFint : IntegrableOn (fun x => Complex.I * F x) (Set.Ioi (0:ℝ)) :=
    (((continuous_const.mul hFcont)).integrable_of_hasCompactSupport
      (hFcs.mul_left)).integrableOn
  calc ∫ x in Set.Ioi (0:ℝ),
        (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0:ℝ), A x := rfl
    _ = (∫ x in Set.Ioi (0:ℝ), A x) - Complex.I * ∫ x in Set.Ioi (0:ℝ), F x := by
        rw [key, mul_zero, sub_zero]
    _ = ∫ x in Set.Ioi (0:ℝ), (A x - Complex.I * F x) := by
        rw [integral_sub hAint hFint, integral_const_mul]
    _ = ∫ x in Set.Ioi (0:ℝ),
          f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)) := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hpt x).symm)

end Brockian.DilationGenerator

