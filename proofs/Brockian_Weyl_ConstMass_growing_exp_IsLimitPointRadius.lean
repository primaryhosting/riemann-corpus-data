/-
  Brockian/WeylConstMass.lean — growing exponential mode: L² mass diverges and
  Weyl radius collapses. Imports Dichotomy only.
-/
import Mathlib
import Brockian.WeylDichotomy

open Filter Topology MeasureTheory intervalIntegral Set
open Brockian.Weyl.Dichotomy

namespace Brockian.Weyl.ConstMass

/-- For continuous `f ≥ 0`, `b ↦ ∫₀ᵇ f` is monotone. -/
theorem integral_nonneg_mono {f : ℝ → ℝ} (hfc : Continuous f) (hf : ∀ x, 0 ≤ f x) :
    Monotone (fun b => ∫ x in 0..b, f x) := by
  intro a b hab
  have h1 : IntervalIntegrable f volume 0 a := hfc.intervalIntegrable _ _
  have h2 : IntervalIntegrable f volume a b := hfc.intervalIntegrable _ _
  have hadd := integral_add_adjacent_intervals h1 h2
  have hnn : 0 ≤ ∫ x in a..b, f x := integral_nonneg hab fun x _ => hf x
  linarith [hadd, hnn]

/-- `∫₀ᵇ e^{r x} → +∞` for `r > 0`. -/
theorem integral_exp_mul_tendsto_atTop {r : ℝ} (hr : 0 < r) :
    Tendsto (fun b : ℝ => ∫ x in 0..b, Real.exp (r * x)) atTop atTop := by
  have hval : (fun b => ∫ x in 0..b, Real.exp (r * x))
      = fun b => r⁻¹ * (Real.exp (r * b) - 1) := by
    funext b
    rw [intervalIntegral.integral_comp_mul_left Real.exp (ne_of_gt hr), integral_exp]
    simp [smul_eq_mul, mul_zero, Real.exp_zero]
  rw [hval]
  have hexp : Tendsto (fun b : ℝ => Real.exp (r * b)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hr tendsto_id)
  have hdiff : Tendsto (fun b : ℝ => Real.exp (r * b) - 1) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-1) hexp).congr (by intro x; ring)
  exact Tendsto.const_mul_atTop (by positivity) hdiff

/-- Norm-square identity for complex exponentials along ℝ. -/
theorem normSq_cexp_eq (μ : ℂ) (x : ℝ) :
    ‖Complex.exp (μ * (x : ℂ))‖ ^ 2 = Real.exp ((2 * μ.re) * x) := by
  have hnorm : ‖Complex.exp (μ * (x : ℂ))‖ = Real.exp (μ.re * x) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [hnorm, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- L² mass of growing complex exponential diverges. -/
theorem growing_exp_mass_tendsto_atTop {μ : ℂ} (hμ : 0 < μ.re) :
    Tendsto (fun b : ℝ => ∫ x in 0..b, ‖Complex.exp (μ * (x : ℂ))‖ ^ 2) atTop atTop := by
  have hfun :
      (fun b => ∫ x in 0..b, ‖Complex.exp (μ * (x : ℂ))‖ ^ 2)
        = fun b => ∫ x in 0..b, Real.exp ((2 * μ.re) * x) := by
    funext b
    apply intervalIntegral.integral_congr
    intro x _
    exact normSq_cexp_eq μ x
  rw [hfun]
  exact integral_exp_mul_tendsto_atTop (by positivity : 0 < 2 * μ.re)

/-- Mass unbounded above. -/
theorem growing_exp_IsLimitPointRadius {μ : ℂ} (hμ : 0 < μ.re) :
    IsLimitPointRadius (fun b => ∫ x in 0..b, ‖Complex.exp (μ * (x : ℂ))‖ ^ 2) := by
  intro hBdd
  obtain ⟨M, hM⟩ := hBdd
  have htend := growing_exp_mass_tendsto_atTop hμ
  obtain ⟨B, hB⟩ := (tendsto_atTop_atTop.mp htend) (M + 1)
  have hge : M + 1 ≤ ∫ x in 0..B, ‖Complex.exp (μ * (x : ℂ))‖ ^ 2 := hB B le_rfl
  have hle : ∫ x in 0..B, ‖Complex.exp (μ * (x : ℂ))‖ ^ 2 ≤ M :=
    hM (Set.mem_range_self B)
  linarith

theorem continuous_growing_exp_normSq (μ : ℂ) :
    Continuous (fun x : ℝ => ‖Complex.exp (μ * (x : ℂ))‖ ^ 2) := by continuity

theorem growing_exp_mass_monotone (μ : ℂ) :
    Monotone (fun b => ∫ x in 0..b, ‖Complex.exp (μ * (x : ℂ))‖ ^ 2) :=
  integral_nonneg_mono (continuous_growing_exp_normSq μ) (fun _ => sq_nonneg _)

/-- Growing-mode Weyl radius → 0. -/
theorem growing_exp_radius_tendsto_zero {c : ℝ} (hc : 0 < c) {μ : ℂ} (hμ : 0 < μ.re) :
    Tendsto
      (weylRadius c (fun b => ∫ x in 0..b, ‖Complex.exp (μ * (x : ℂ))‖ ^ 2))
      atTop (nhds 0) :=
  limitPointRadius_radius_tendsto_zero hc
    (growing_exp_mass_monotone μ) (growing_exp_IsLimitPointRadius hμ)

/-- For non-real λ and real c, a growing mode with limit-point radius exists. -/
theorem exists_growing_mode_limitPointRadius (c : ℝ) {lam : ℂ} (hlam : lam.im ≠ 0) :
    ∃ μ : ℂ, μ ^ 2 = (c : ℂ) - lam ∧ 0 < μ.re ∧
      IsLimitPointRadius (fun b => ∫ x in 0..b, ‖Complex.exp (μ * (x : ℂ))‖ ^ 2) := by
  have hznr : ((c : ℂ) - lam).im ≠ 0 := by
    rw [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_ne_zero]; exact hlam
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((c : ℂ) - lam) (n := 2) (by norm_num)
  have hwre : w.re ≠ 0 := by
    intro h0
    apply hznr
    rw [← hw, pow_two, Complex.mul_im, h0]
    ring
  rcases lt_or_gt_of_ne hwre with hneg | hpos
  · refine ⟨-w, by rw [neg_sq]; exact hw, ?_, ?_⟩
    · rw [Complex.neg_re]; linarith
    · exact growing_exp_IsLimitPointRadius (by rw [Complex.neg_re]; linarith)
  · exact ⟨w, hw, hpos, growing_exp_IsLimitPointRadius hpos⟩

end Brockian.Weyl.ConstMass
