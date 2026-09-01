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

import RequestProject.QI.Spectral

/-!
# An integral formula for the relative entropy

The elementary scalar identity

`∫_0^∞ (a²/(b + t a) - a/(1 + t)) dt = a (log a - log b)`  (`QI.integral_scalar`)

for `a, b > 0`, combined with the spectral formulas of `RequestProject.QI.Spectral`, gives the
integral representation

`relEntropy ρ σ = ∫_{t ∈ (0, ∞)} (Rval ρ σ t - (tr ρ).re / (1 + t)) dt`

(`QI.relEntropy_eq_integral`) for positive definite `ρ`, `σ`.  Since `Rval` is monotone under
quantum channels, this immediately yields the data-processing inequality.
-/

namespace QI

open Real MeasureTheory Filter Set Matrix
open scoped Topology ComplexOrder BigOperators MatrixOrder

/-! ### The scalar integral -/

/-- The antiderivative of `t ↦ a²/(b + t a) - a/(1 + t)`. -/
noncomputable def logAnti (a b : ℝ) (t : ℝ) : ℝ := a * (Real.log (b + t * a) - Real.log (1 + t))

theorem hasDerivAt_logAnti {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (logAnti a b) (a ^ 2 / (b + t * a) - a / (1 + t)) t := by
  have hden : b + t * a ≠ 0 := by positivity
  have hden2 : (1 : ℝ) + t ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => b + s * a) a t := by
    simpa using ((hasDerivAt_id t).mul_const a).const_add b
  have h2 : HasDerivAt (fun s : ℝ => Real.log (b + s * a)) (a / (b + t * a)) t := h1.log hden
  have h3 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
    have h : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by simpa using (hasDerivAt_id t).const_add 1
    exact h.log hden2
  have h4 := (h2.sub h3).const_mul a
  have heq : a * (a / (b + t * a) - 1 / (1 + t)) = a ^ 2 / (b + t * a) - a / (1 + t) := by
    field_simp
  rwa [heq] at h4

theorem tendsto_logAnti {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (logAnti a b) atTop (𝓝 (a * Real.log a)) := by
  have hfrac : Tendsto (fun t : ℝ => (b + t * a) / (1 + t)) atTop (𝓝 a) := by
    have h1 : Tendsto (fun t : ℝ => (b - a) / (1 + t)) atTop (𝓝 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_left _ 1 tendsto_id
    have h2 := (tendsto_const_nhds (x := a) (f := atTop (α := ℝ))).add h1
    rw [add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h2' : (0 : ℝ) < 1 + t := by positivity
    field_simp
    ring
  have hlog := (Real.continuousAt_log ha.ne').tendsto.comp hfrac
  refine (hlog.const_mul a).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have h1 : (0 : ℝ) < b + t * a := by positivity
  have h2 : (0 : ℝ) < 1 + t := by positivity
  simp [logAnti, Function.comp, Real.log_div h1.ne' h2.ne']

/-- The scalar integrand, in factored form; note that its sign does not depend on `t`. -/
theorem scalar_integrand_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 ≤ x) :
    a ^ 2 / (b + x * a) - a / (1 + x) = a * (a - b) / ((b + x * a) * (1 + x)) := by
  have h1 : (0 : ℝ) < b + x * a := by positivity
  have h2 : (0 : ℝ) < 1 + x := by positivity
  field_simp
  ring

theorem integrableOn_scalar {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => a ^ 2 / (b + t * a) - a / (1 + t)) (Ioi 0) := by
  rcases le_total b a with hab | hab
  · refine integrableOn_Ioi_deriv_of_nonneg' (g := logAnti a b)
      (fun x hx => hasDerivAt_logAnti ha hb hx) (fun x hx => ?_) (tendsto_logAnti ha hb)
    have hx' : (0 : ℝ) < x := hx
    rw [scalar_integrand_eq ha hb hx'.le]
    have h1 : (0 : ℝ) < b + x * a := by positivity
    have h2 : (0 : ℝ) < 1 + x := by positivity
    have h3 : 0 ≤ a * (a - b) := by nlinarith
    positivity
  · refine integrableOn_Ioi_deriv_of_nonpos' (g := logAnti a b)
      (fun x hx => hasDerivAt_logAnti ha hb hx) (fun x hx => ?_) (tendsto_logAnti ha hb)
    have hx' : (0 : ℝ) < x := hx
    rw [scalar_integrand_eq ha hb hx'.le]
    have h1 : (0 : ℝ) < b + x * a := by positivity
    have h2 : (0 : ℝ) < 1 + x := by positivity
    have h3 : a * (a - b) ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg h3 (by positivity)

/-- The scalar integral underlying the integral representation of the relative entropy. -/
theorem integral_scalar {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), (a ^ 2 / (b + t * a) - a / (1 + t))) = a * (Real.log a - Real.log b) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x hx => hasDerivAt_logAnti ha hb hx)
    (integrableOn_scalar ha hb) (tendsto_logAnti ha hb)]
  simp [logAnti]
  ring

/-! ### The integral representation of the relative entropy -/

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ}

/-- The spectral formula for the resolvent quantity `Rval`. -/
theorem Rval_eq_sum (hρ : ρ.PosDef) (hσ : σ.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    Rval ρ σ t = ∑ j, ∑ i, ‖eigOverlap hρ.isHermitian hσ.isHermitian i j‖ ^ 2 *
      (hρ.isHermitian.eigenvalues j ^ 2 /
        (hσ.isHermitian.eigenvalues i + t * hρ.isHermitian.eigenvalues j)) := by
  obtain ⟨B₀, hB, hval⟩ := exists_sylvester hρ hσ ht
  rw [Rval_eq_of_sylvester hρ.posSemidef hσ.posSemidef ht hB, hval]

/-- The integrand of the integral representation, expanded in the spectral data. -/
theorem relIntegrand_eq_sum (hρ : ρ.PosDef) (hσ : σ.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    Rval ρ σ t - (Matrix.trace ρ).re / (1 + t)
      = ∑ j, ∑ i, ‖eigOverlap hρ.isHermitian hσ.isHermitian i j‖ ^ 2 *
          (hρ.isHermitian.eigenvalues j ^ 2 /
            (hσ.isHermitian.eigenvalues i + t * hρ.isHermitian.eigenvalues j)
            - hρ.isHermitian.eigenvalues j / (1 + t)) := by
  rw [Rval_eq_sum hρ hσ ht, re_trace_eq_sum hρ.isHermitian, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : hρ.isHermitian.eigenvalues j / (1 + t)
      = ∑ i, ‖eigOverlap hρ.isHermitian hσ.isHermitian i j‖ ^ 2 *
        (hρ.isHermitian.eigenvalues j / (1 + t)) := by
    rw [← Finset.sum_mul, sum_normSq_eigOverlap hρ.isHermitian hσ.isHermitian j, one_mul]
  conv_lhs => rw [h1]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem integrableOn_relIntegrand (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    IntegrableOn (fun t : ℝ => Rval ρ σ t - (Matrix.trace ρ).re / (1 + t)) (Ioi 0) := by
  have hsum : IntegrableOn (fun t : ℝ => ∑ j, ∑ i,
      ‖eigOverlap hρ.isHermitian hσ.isHermitian i j‖ ^ 2 *
        (hρ.isHermitian.eigenvalues j ^ 2 /
          (hσ.isHermitian.eigenvalues i + t * hρ.isHermitian.eigenvalues j)
          - hρ.isHermitian.eigenvalues j / (1 + t))) (Ioi 0) := by
    refine integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun i _ => ?_
    exact ((integrableOn_scalar (hρ.eigenvalues_pos j) (hσ.eigenvalues_pos i)).const_mul _)
  refine hsum.congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact (relIntegrand_eq_sum hρ hσ (le_of_lt ht)).symm

/-- **Integral representation of the Umegaki relative entropy.** -/
theorem relEntropy_eq_integral (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEntropy ρ σ = ∫ t in Ioi (0 : ℝ), (Rval ρ σ t - (Matrix.trace ρ).re / (1 + t)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => relIntegrand_eq_sum hρ hσ (le_of_lt ht))]
  rw [MeasureTheory.integral_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun i _ =>
      (integrableOn_scalar (hρ.eigenvalues_pos j) (hσ.eigenvalues_pos i)).const_mul _]
  rw [relEntropy_eq_sum hρ.isHermitian hσ.isHermitian]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_finset_sum _ fun i _ =>
    (integrableOn_scalar (hρ.eigenvalues_pos j) (hσ.eigenvalues_pos i)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_const_mul,
    integral_scalar (hρ.eigenvalues_pos j) (hσ.eigenvalues_pos i)]

end QI

import RequestProject.QI.Basic

/-!
# A variational quantity that is monotone under quantum channels

For positive semidefinite matrices `ρ σ` and a parameter `t ≥ 0` we consider the quadratic
functional
`Qform ρ σ t B = 2 Re tr(ρ B) - Re tr(Bᴴ σ B) - t Re tr(Bᴴ B ρ)`
and its supremum `Rval ρ σ t = ⨆ B, Qform ρ σ t B`.

In terms of the relative modular operator `Δ X = σ X ρ⁻¹` acting on the Hilbert–Schmidt space,
`Rval ρ σ t = ⟪ρ^{1/2}, (Δ + t)⁻¹ ρ^{1/2}⟫`; the supremum is attained at the solution `B₀`
of the Sylvester equation `σ B₀ + t B₀ ρ = ρ`.

The main results are:

* `QI.Qform_le_of_sylvester`, `QI.Qform_eq_of_sylvester`: a solution of the Sylvester
  equation maximises `Qform`, with value `Re tr(ρ B₀)`;
* `QI.Qform_apply_le`: `Qform (Φ ρ) (Φ σ) t B ≤ Qform ρ σ t (Φ* B)` for a channel `Φ`
  (a consequence of the Kadison–Schwarz inequality);
* `QI.Rval_apply_le`: `Rval (Φ ρ) (Φ σ) t ≤ Rval ρ σ t`, i.e. `Rval` is monotone under
  quantum channels.
-/

namespace QI

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- The quadratic functional whose supremum is the resolvent form of the relative modular
operator. -/
noncomputable def Qform (ρ σ : Matrix n n ℂ) (t : ℝ) (B : Matrix n n ℂ) : ℝ :=
  2 * (Matrix.trace (ρ * B)).re - (Matrix.trace (Bᴴ * σ * B)).re
    - t * (Matrix.trace (Bᴴ * B * ρ)).re

/-- The supremum of `Qform` over all `B`. -/
noncomputable def Rval (ρ σ : Matrix n n ℂ) (t : ℝ) : ℝ := ⨆ B : Matrix n n ℂ, Qform ρ σ t B

/-! ### The Sylvester equation and maximality -/

section Sylvester

variable {ρ σ B₀ : Matrix n n ℂ} {t : ℝ}

/-- The positive form associated with the Sylvester operator `X ↦ σ X + t X ρ`. -/
private noncomputable def Sform (ρ σ : Matrix n n ℂ) (t : ℝ) (X : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (Xᴴ * σ * X)).re + t * (Matrix.trace (Xᴴ * X * ρ)).re

private theorem Sform_nonneg (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (X : Matrix n n ℂ) : 0 ≤ Sform ρ σ t X := by
  have h1 : 0 ≤ (Matrix.trace (Xᴴ * σ * X)).re := by
    have := (hσ.conjTranspose_mul_mul_same X).trace_nonneg
    simpa using (Complex.le_def.mp this).1
  have h2 : 0 ≤ (Matrix.trace (Xᴴ * X * ρ)).re :=
    trace_mul_re_nonneg (Matrix.posSemidef_conjTranspose_mul_self X) hρ
  have := mul_nonneg ht h2
  simp only [Sform]
  linarith

section NoDecEq

omit [DecidableEq n]

/-- The Sylvester operator. -/
private noncomputable def Lmap (ρ σ : Matrix n n ℂ) (t : ℝ) (Y : Matrix n n ℂ) : Matrix n n ℂ :=
  σ * Y + (t : ℂ) • (Y * ρ)

private theorem trace_Lmap (X Y : Matrix n n ℂ) :
    Matrix.trace (Xᴴ * σ * Y) + (t : ℂ) * Matrix.trace (Xᴴ * Y * ρ)
      = Matrix.trace (Xᴴ * Lmap ρ σ t Y) := by
  simp only [Lmap, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]

private theorem re_trace_Lmap (X Y : Matrix n n ℂ) :
    (Matrix.trace (Xᴴ * σ * Y)).re + t * (Matrix.trace (Xᴴ * Y * ρ)).re
      = (Matrix.trace (Xᴴ * Lmap ρ σ t Y)).re := by
  rw [← trace_Lmap]
  simp [Complex.add_re, Complex.mul_re]

private theorem trace_Lmap_symm (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (X Y : Matrix n n ℂ) :
    (starRingEnd ℂ) (Matrix.trace (Xᴴ * Lmap ρ σ t Y)) = Matrix.trace (Yᴴ * Lmap ρ σ t X) := by
  rw [← trace_Lmap, ← trace_Lmap, map_add, map_mul]
  congr 1
  · rw [show (starRingEnd ℂ) (Matrix.trace (Xᴴ * σ * Y)) = Matrix.trace ((Xᴴ * σ * Y)ᴴ) from
      (Matrix.trace_conjTranspose _).symm]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hσ.eq,
      Matrix.mul_assoc]
  · rw [show (starRingEnd ℂ) (Matrix.trace (Xᴴ * Y * ρ)) = Matrix.trace ((Xᴴ * Y * ρ)ᴴ) from
      (Matrix.trace_conjTranspose _).symm]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hρ.eq]
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    simp [Complex.conj_ofReal]

/-- For hermitian `ρ`, `tr(Xᴴ ρ)` is the complex conjugate of `tr(ρ X)`. -/
private theorem trace_conjTranspose_mul (hρ : ρ.IsHermitian) (X : Matrix n n ℂ) :
    Matrix.trace (Xᴴ * ρ) = (starRingEnd ℂ) (Matrix.trace (ρ * X)) := by
  rw [show (starRingEnd ℂ) (Matrix.trace (ρ * X)) = Matrix.trace ((ρ * X)ᴴ) from
    (Matrix.trace_conjTranspose _).symm]
  rw [Matrix.conjTranspose_mul, hρ.eq]

/-- The value of `Qform` at a solution of the Sylvester equation `σ B₀ + t B₀ ρ = ρ`. -/
theorem Qform_eq_of_sylvester (hρ : ρ.IsHermitian)
    (hB₀ : σ * B₀ + (t : ℂ) • (B₀ * ρ) = ρ) :
    Qform ρ σ t B₀ = (Matrix.trace (ρ * B₀)).re := by
  have hL : Lmap ρ σ t B₀ = ρ := hB₀
  have h := re_trace_Lmap (ρ := ρ) (σ := σ) (t := t) B₀ B₀
  rw [hL, trace_conjTranspose_mul hρ] at h
  simp only [Complex.conj_re] at h
  simp only [Qform]
  linarith

/-- The "distance to the maximiser" identity. -/
private theorem Qform_sub (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hB₀ : σ * B₀ + (t : ℂ) • (B₀ * ρ) = ρ) (B : Matrix n n ℂ) :
    Qform ρ σ t B₀ - Qform ρ σ t B = Sform ρ σ t (B₀ - B) := by
  have hL : Lmap ρ σ t B₀ = ρ := hB₀
  have hlin : Lmap ρ σ t (B₀ - B) = Lmap ρ σ t B₀ - Lmap ρ σ t B := by
    simp only [Lmap, Matrix.sub_mul, Matrix.mul_sub, smul_sub]; abel
  -- expand the quadratic form at `B₀ - B`
  have e1 : Sform ρ σ t (B₀ - B) = (Matrix.trace ((B₀ - B)ᴴ * Lmap ρ σ t (B₀ - B))).re :=
    re_trace_Lmap _ _
  have e2 : Matrix.trace ((B₀ - B)ᴴ * Lmap ρ σ t (B₀ - B))
      = Matrix.trace (B₀ᴴ * Lmap ρ σ t B₀) + Matrix.trace (Bᴴ * Lmap ρ σ t B)
        - Matrix.trace (B₀ᴴ * Lmap ρ σ t B) - Matrix.trace (Bᴴ * Lmap ρ σ t B₀) := by
    rw [hlin]
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
    abel
  -- the four terms
  have v1 : (Matrix.trace (B₀ᴴ * Lmap ρ σ t B₀)).re = (Matrix.trace (ρ * B₀)).re := by
    rw [hL, trace_conjTranspose_mul hρ]; simp
  have v2 : (Matrix.trace (Bᴴ * Lmap ρ σ t B₀)).re = (Matrix.trace (ρ * B)).re := by
    rw [hL, trace_conjTranspose_mul hρ]; simp
  have v3 : (Matrix.trace (B₀ᴴ * Lmap ρ σ t B)).re = (Matrix.trace (ρ * B)).re := by
    have hs := trace_Lmap_symm hρ hσ (t := t) B₀ B
    have : (Matrix.trace (B₀ᴴ * Lmap ρ σ t B)).re = (Matrix.trace (Bᴴ * Lmap ρ σ t B₀)).re := by
      rw [← hs]; simp
    rw [this, v2]
  have v4 : (Matrix.trace (Bᴴ * Lmap ρ σ t B)).re
      = (Matrix.trace (Bᴴ * σ * B)).re + t * (Matrix.trace (Bᴴ * B * ρ)).re :=
    (re_trace_Lmap B B).symm
  have hQ₀ : Qform ρ σ t B₀ = (Matrix.trace (ρ * B₀)).re := Qform_eq_of_sylvester hρ hB₀
  rw [e1, e2]
  simp only [Complex.sub_re, Complex.add_re]
  rw [v1, v2, v3, v4, hQ₀]
  simp only [Qform]
  ring

end NoDecEq

/-- A solution of the Sylvester equation maximises `Qform`. -/
theorem Qform_le_of_sylvester (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (hB₀ : σ * B₀ + (t : ℂ) • (B₀ * ρ) = ρ) (B : Matrix n n ℂ) :
    Qform ρ σ t B ≤ Qform ρ σ t B₀ := by
  have h := Qform_sub hρ.isHermitian hσ.isHermitian hB₀ B
  have := Sform_nonneg hρ hσ ht (B₀ - B)
  linarith

theorem isGreatest_range_Qform (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (hB₀ : σ * B₀ + (t : ℂ) • (B₀ * ρ) = ρ) :
    IsGreatest (Set.range (Qform ρ σ t)) (Qform ρ σ t B₀) :=
  ⟨⟨B₀, rfl⟩, by rintro _ ⟨B, rfl⟩; exact Qform_le_of_sylvester hρ hσ ht hB₀ B⟩

/-- The supremum `Rval` is attained at a solution of the Sylvester equation. -/
theorem Rval_eq_of_sylvester (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (hB₀ : σ * B₀ + (t : ℂ) • (B₀ * ρ) = ρ) :
    Rval ρ σ t = (Matrix.trace (ρ * B₀)).re := by
  have h := (isGreatest_range_Qform hρ hσ ht hB₀).csSup_eq
  rw [Rval, iSup, h, Qform_eq_of_sylvester hρ.isHermitian hB₀]

end Sylvester

/-! ### Monotonicity under quantum channels -/

variable {ρ σ : Matrix n n ℂ} {t : ℝ}

/-- Pulling a test matrix back through the channel does not decrease `Qform`. This is the
Kadison–Schwarz inequality in disguise. -/
theorem Qform_apply_le (Φ : Channel n m ι) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (B : Matrix m m ℂ) :
    Qform (Φ.apply ρ) (Φ.apply σ) t B ≤ Qform ρ σ t (Φ.adjoint B) := by
  have hlin : (Matrix.trace (Φ.apply ρ * B)).re = (Matrix.trace (ρ * Φ.adjoint B)).re := by
    rw [Φ.trace_apply_mul]
  have h2 : (Matrix.trace ((Φ.adjoint B)ᴴ * σ * Φ.adjoint B)).re
      ≤ (Matrix.trace (Bᴴ * Φ.apply σ * B)).re := by
    have e1 : Matrix.trace ((Φ.adjoint B)ᴴ * σ * Φ.adjoint B)
        = Matrix.trace ((Φ.adjoint B * (Φ.adjoint B)ᴴ) * σ) := by
      rw [Matrix.trace_mul_comm ((Φ.adjoint B)ᴴ * σ) (Φ.adjoint B), ← Matrix.mul_assoc]
    have e2 : Matrix.trace (Bᴴ * Φ.apply σ * B) = Matrix.trace (Φ.adjoint (B * Bᴴ) * σ) := by
      rw [Matrix.trace_mul_comm (Bᴴ * Φ.apply σ) B, ← Matrix.mul_assoc,
        Matrix.trace_mul_comm (B * Bᴴ) (Φ.apply σ), Φ.trace_apply_mul σ (B * Bᴴ),
        Matrix.trace_mul_comm]
    rw [e1, e2]
    exact trace_mul_re_mono (Φ.kadison_schwarz' B) hσ
  have h3 : (Matrix.trace ((Φ.adjoint B)ᴴ * Φ.adjoint B * ρ)).re
      ≤ (Matrix.trace (Bᴴ * B * Φ.apply ρ)).re := by
    have e2 : Matrix.trace (Bᴴ * B * Φ.apply ρ) = Matrix.trace (Φ.adjoint (Bᴴ * B) * ρ) := by
      rw [Matrix.trace_mul_comm (Bᴴ * B) (Φ.apply ρ), Φ.trace_apply_mul ρ (Bᴴ * B),
        Matrix.trace_mul_comm]
    rw [e2]
    exact trace_mul_re_mono (Φ.kadison_schwarz B) hρ
  have h3' : t * (Matrix.trace ((Φ.adjoint B)ᴴ * Φ.adjoint B * ρ)).re
      ≤ t * (Matrix.trace (Bᴴ * B * Φ.apply ρ)).re := mul_le_mul_of_nonneg_left h3 ht
  simp only [Qform]
  rw [hlin]
  linarith

/-- **Monotonicity of the resolvent form under quantum channels.** -/
theorem Rval_apply_le (Φ : Channel n m ι) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    {B₀ : Matrix n n ℂ} (hB₀ : σ * B₀ + (t : ℂ) • (B₀ * ρ) = ρ) :
    Rval (Φ.apply ρ) (Φ.apply σ) t ≤ Rval ρ σ t := by
  rw [Rval_eq_of_sylvester hρ hσ ht hB₀, ← Qform_eq_of_sylvester hρ.isHermitian hB₀]
  exact ciSup_le fun B =>
    le_trans (Qform_apply_le Φ hρ hσ ht B) (Qform_le_of_sylvester hρ hσ ht hB₀ _)

end QI

import Mathlib

/-!
# Basic finite-dimensional quantum-information setup

This file sets up:

* elementary facts about traces of products of positive semidefinite matrices;
* quantum channels in Kraus form (`QI.Channel`), their action `Φ.apply` on states and
  the adjoint (Heisenberg picture) map `Φ.adjoint`;
* the Kadison–Schwarz inequality for the adjoint map.

By the Choi–Kraus theorem, the maps of the form `Φ.apply` for `Φ : QI.Channel n m ι` are
exactly the completely positive trace preserving (CPTP) maps from `n × n` matrices to
`m × m` matrices.
-/

namespace QI

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-! ### Traces of products of positive semidefinite matrices -/

/-- The trace of a product of two positive semidefinite matrices is a nonnegative real. -/
theorem trace_mul_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)) := by
  have hs : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hmul : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A
  have h : Matrix.trace (A * B) = Matrix.trace ((CFC.sqrt A)ᴴ * B * CFC.sqrt A) := by
    rw [hs.isHermitian.eq]
    conv_lhs => rw [← hmul]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [h]
  exact (hB.conjTranspose_mul_mul_same (CFC.sqrt A)).trace_nonneg

theorem trace_mul_re_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  have := trace_mul_nonneg hA hB
  simpa using (Complex.le_def.mp this).1

/-- Monotonicity of `X ↦ (trace (X * ρ)).re` in the Loewner order, for `ρ` psd. -/
theorem trace_mul_re_mono {A B ρ : Matrix n n ℂ} (h : (B - A).PosSemidef) (hρ : ρ.PosSemidef) :
    (Matrix.trace (A * ρ)).re ≤ (Matrix.trace (B * ρ)).re := by
  have := trace_mul_re_nonneg h hρ
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at this
  linarith

/-! ### Quantum channels in Kraus form -/

/-- A quantum channel from `n × n` matrices to `m × m` matrices, presented by a
finite family of Kraus operators satisfying the trace-preservation (completeness)
relation `∑ i, (K i)ᴴ * K i = 1`. -/
structure Channel (n m ι : Type*) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype ι] where
  /-- The Kraus operators of the channel. -/
  K : ι → Matrix m n ℂ
  /-- Completeness relation, equivalent to trace preservation. -/
  complete : ∑ i, (K i)ᴴ * K i = 1

namespace Channel

variable (Φ : Channel n m ι)

/-- The action of the channel on states (Schrödinger picture): `X ↦ ∑ i, K i * X * (K i)ᴴ`. -/
noncomputable def apply (X : Matrix n n ℂ) : Matrix m m ℂ := ∑ i, Φ.K i * X * (Φ.K i)ᴴ

/-- The adjoint of the channel (Heisenberg picture): `Y ↦ ∑ i, (K i)ᴴ * Y * K i`. -/
noncomputable def adjoint (Y : Matrix m m ℂ) : Matrix n n ℂ := ∑ i, (Φ.K i)ᴴ * Y * Φ.K i

@[simp] theorem adjoint_one : Φ.adjoint 1 = 1 := by
  simp [adjoint, Φ.complete]

theorem adjoint_conjTranspose (Y : Matrix m m ℂ) : Φ.adjoint (Yᴴ) = (Φ.adjoint Y)ᴴ := by
  simp [adjoint, Matrix.conjTranspose_sum, Matrix.mul_assoc]

/-- The channel is trace preserving. -/
theorem trace_apply (X : Matrix n n ℂ) : Matrix.trace (Φ.apply X) = Matrix.trace X := by
  have h : Matrix.trace (Φ.apply X) = Matrix.trace ((∑ i, (Φ.K i)ᴴ * Φ.K i) * X) := by
    rw [apply, Matrix.trace_sum, Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.trace_mul_comm (Φ.K i * X) ((Φ.K i)ᴴ), ← Matrix.mul_assoc]
  rw [h, Φ.complete, Matrix.one_mul]

/-- Duality between the channel and its adjoint. -/
theorem trace_apply_mul (X : Matrix n n ℂ) (Y : Matrix m m ℂ) :
    Matrix.trace (Φ.apply X * Y) = Matrix.trace (X * Φ.adjoint Y) := by
  rw [apply, adjoint, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_mul_comm (Φ.K i * X * (Φ.K i)ᴴ) Y]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (Y * Φ.K i * X) ((Φ.K i)ᴴ)]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc]

/-- The channel maps positive semidefinite matrices to positive semidefinite matrices. -/
theorem apply_posSemidef {X : Matrix n n ℂ} (hX : X.PosSemidef) : (Φ.apply X).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun i _ => ?_
  simpa [Matrix.mul_assoc] using hX.mul_mul_conjTranspose_same (Φ.K i)

/-- The quadratic form of `Φ.apply X` in terms of the Kraus operators. -/
theorem dotProduct_apply_mulVec (X : Matrix n n ℂ) (v : m → ℂ) :
    star v ⬝ᵥ (Φ.apply X *ᵥ v) = ∑ i, star ((Φ.K i)ᴴ *ᵥ v) ⬝ᵥ (X *ᵥ ((Φ.K i)ᴴ *ᵥ v)) := by
  rw [apply, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.vecMul_vecMul]

/-- If the image of *some* matrix under the channel is positive definite, then the image of
*any* positive definite matrix is positive definite. -/
theorem apply_posDef_of_apply_posDef {X Y : Matrix n n ℂ} (hX : X.PosDef)
    (hY : (Φ.apply Y).PosDef) : (Φ.apply X).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (Φ.apply_posSemidef hX.posSemidef).isHermitian
    fun v hv => ?_
  have hYv := hY.dotProduct_mulVec_pos hv
  rw [Φ.dotProduct_apply_mulVec Y v] at hYv
  have hex : ∃ i : ι, (Φ.K i)ᴴ *ᵥ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    have hzero : ∀ i : ι, star ((Φ.K i)ᴴ *ᵥ v) ⬝ᵥ (Y *ᵥ ((Φ.K i)ᴴ *ᵥ v)) = 0 := by
      intro i; rw [hc i]; simp
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hzero i] at hYv
    simp at hYv
  obtain ⟨i₀, hi₀⟩ := hex
  rw [Φ.dotProduct_apply_mulVec X v]
  refine lt_of_lt_of_le (hX.dotProduct_mulVec_pos hi₀) ?_
  exact Finset.single_le_sum (f := fun i => star ((Φ.K i)ᴴ *ᵥ v) ⬝ᵥ (X *ᵥ ((Φ.K i)ᴴ *ᵥ v)))
    (fun i _ => hX.posSemidef.dotProduct_mulVec_nonneg _) (Finset.mem_univ i₀)

/-- The adjoint map is positive. -/
theorem adjoint_posSemidef {Y : Matrix m m ℂ} (hY : Y.PosSemidef) : (Φ.adjoint Y).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun i _ => ?_
  simpa [Matrix.mul_assoc] using hY.conjTranspose_mul_mul_same (Φ.K i)

/-- **Kadison–Schwarz inequality** for the (unital, completely positive) adjoint map:
`(Φ*Y)ᴴ (Φ*Y) ≤ Φ*(Yᴴ Y)`. -/
theorem kadison_schwarz (Y : Matrix m m ℂ) :
    (Φ.adjoint (Yᴴ * Y) - (Φ.adjoint Y)ᴴ * Φ.adjoint Y).PosSemidef := by
  set A := Φ.adjoint Y with hA
  have key : ∑ i, (Y * Φ.K i - Φ.K i * A)ᴴ * (Y * Φ.K i - Φ.K i * A)
      = Φ.adjoint (Yᴴ * Y) - Aᴴ * A := by
    have expand : ∀ i : ι, (Y * Φ.K i - Φ.K i * A)ᴴ * (Y * Φ.K i - Φ.K i * A)
        = (Φ.K i)ᴴ * (Yᴴ * Y) * Φ.K i - ((Φ.K i)ᴴ * Yᴴ * Φ.K i) * A
          - Aᴴ * ((Φ.K i)ᴴ * Y * Φ.K i) + Aᴴ * ((Φ.K i)ᴴ * Φ.K i) * A := by
      intro i
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul,
        Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
      abel
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => expand i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have h1 : ∑ i : ι, (Φ.K i)ᴴ * (Yᴴ * Y) * Φ.K i = Φ.adjoint (Yᴴ * Y) := rfl
    have h2 : ∑ i : ι, ((Φ.K i)ᴴ * Yᴴ * Φ.K i) * A = Aᴴ * A := by
      rw [← Finset.sum_mul]
      congr 1
      rw [hA, ← Φ.adjoint_conjTranspose]
      simp [adjoint, Matrix.mul_assoc]
    have h3 : ∑ i : ι, Aᴴ * ((Φ.K i)ᴴ * Y * Φ.K i) = Aᴴ * A := by
      rw [← Finset.mul_sum]
      rfl
    have h4 : ∑ i : ι, Aᴴ * ((Φ.K i)ᴴ * Φ.K i) * A = Aᴴ * A := by
      have hstep : ∑ i : ι, Aᴴ * ((Φ.K i)ᴴ * Φ.K i) * A
          = Aᴴ * ((∑ i : ι, (Φ.K i)ᴴ * Φ.K i) * A) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mul_assoc]
      rw [hstep, Φ.complete, Matrix.one_mul]
    rw [h1, h2, h3, h4]
    abel
  rw [← key]
  exact Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_conjTranspose_mul_self _

/-- The other form of the Kadison–Schwarz inequality: `(Φ*Y) (Φ*Y)ᴴ ≤ Φ*(Y Yᴴ)`. -/
theorem kadison_schwarz' (Y : Matrix m m ℂ) :
    (Φ.adjoint (Y * Yᴴ) - Φ.adjoint Y * (Φ.adjoint Y)ᴴ).PosSemidef := by
  have h := Φ.kadison_schwarz (Yᴴ)
  rwa [Matrix.conjTranspose_conjTranspose, Φ.adjoint_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at h

end Channel

end QI

import RequestProject.QI.Variational

/-!
# Quantum relative entropy and its spectral formulas

This file defines the matrix logarithm `QI.mlog` (via the continuous functional calculus) and
the Umegaki relative entropy

`QI.relEntropy ρ σ = Re tr (ρ (log ρ - log σ))`.

It then computes, for positive definite `ρ σ`, both `relEntropy ρ σ` and the variational
quantity `QI.Rval ρ σ t` in terms of the spectral data of `ρ` and `σ`:
if `ρ = U diag(p) U*`, `σ = V diag(q) V*` and `W = V* U`, then

* `relEntropy ρ σ = ∑ i j, ‖W i j‖² * (p j * (log (p j) - log (q i)))`,
* `Rval ρ σ t = ∑ i j, ‖W i j‖² * (p j ^ 2 / (q i + t * p j))`.
-/

namespace QI

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix logarithm of a hermitian matrix, defined by the continuous functional calculus.
(Recall the junk-value convention `Real.log 0 = 0`.) -/
noncomputable def mlog (A : Matrix n n ℂ) : Matrix n n ℂ := cfc Real.log A

/-- The Umegaki relative entropy `D(ρ‖σ) = Re tr (ρ (log ρ - log σ))`. -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (ρ * (mlog ρ - mlog σ))).re

/-! ### Auxiliary trace computations -/

theorem trace_conj_diag (U V : Matrix n n ℂ) (d1 d2 : n → ℂ) :
    Matrix.trace (U * diagonal d1 * star U * (V * diagonal d2 * star V))
      = Matrix.trace (diagonal d1 * (star V * U)ᴴ * diagonal d2 * (star V * U)) := by
  have hH : (star V * U)ᴴ = star U * V := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  rw [hH]
  have h := Matrix.trace_mul_comm (V * diagonal d2 * star V * U) (diagonal d1 * star U)
  have h2 := Matrix.trace_mul_comm (U * diagonal d1 * star U) (V * diagonal d2 * star V)
  simp only [Matrix.mul_assoc] at h h2 ⊢
  rw [h2, h]

theorem trace_diag_conj (d1 d2 : n → ℂ) (W : Matrix n n ℂ) :
    Matrix.trace (diagonal d1 * Wᴴ * diagonal d2 * W)
      = ∑ j, ∑ i, d1 j * d2 i * ((starRingEnd ℂ) (W i j) * W i j) := by
  have hM : ∀ j, (Wᴴ * diagonal d2 * W) j j
      = ∑ i, (starRingEnd ℂ) (W i j) * d2 i * W i j := by
    intro j
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_diagonal]
    simp [Matrix.conjTranspose_apply]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.diagonal_mul, hM j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem conj_mul_self (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h : ((‖z‖ ^ 2 : ℝ) : ℂ) = (Complex.normSq z : ℂ) := by rw [Complex.normSq_eq_norm_sq]
  rw [h, Complex.normSq_eq_conj_mul_self]

theorem cfc_eq_conj {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *
      (star hA.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [hA.cfc_eq]; rfl

/-- The fundamental spectral formula: the trace of a product of two functions of hermitian
matrices, in terms of the eigenvalues and the overlap matrix `W = V* U`. -/
theorem trace_cfc_mul_cfc {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (f g : ℝ → ℝ) :
    Matrix.trace (cfc f ρ * cfc g σ)
      = ((∑ j, ∑ i, f (hρ.eigenvalues j) * g (hσ.eigenvalues i) *
          ‖((star (hσ.eigenvectorUnitary : Matrix n n ℂ)) *
            (hρ.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [cfc_eq_conj hρ f, cfc_eq_conj hσ g, trace_conj_diag, trace_diag_conj]
  push_cast
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply,
    show ∀ x : ℝ, (RCLike.ofReal x : ℂ) = (x : ℂ) from fun _ => rfl]
  rw [conj_mul_self]
  push_cast
  ring

variable {ρ σ : Matrix n n ℂ}

/-- The overlap matrix `W = V* U` between the eigenbases of `ρ` (columns of `U`) and of `σ`
(columns of `V`). -/
noncomputable def eigOverlap (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : Matrix n n ℂ :=
  star (hσ.eigenvectorUnitary : Matrix n n ℂ) * (hρ.eigenvectorUnitary : Matrix n n ℂ)

theorem eigOverlap_unitary (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (eigOverlap hρ hσ)ᴴ * eigOverlap hρ hσ = 1 := by
  have hU : star (hρ.eigenvectorUnitary : Matrix n n ℂ) * (hρ.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := UnitaryGroup.star_mul_self _
  have hV : (hσ.eigenvectorUnitary : Matrix n n ℂ) * star (hσ.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := (Unitary.mem_iff.mp hσ.eigenvectorUnitary.2).2
  simp only [eigOverlap, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (hρ.eigenvectorUnitary : Matrix n n ℂ)]
  rw [show (hσ.eigenvectorUnitary : Matrix n n ℂ) * (hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 by
    rw [← Matrix.star_eq_conjTranspose]; exact hV]
  rw [Matrix.one_mul]
  rw [← Matrix.star_eq_conjTranspose]
  exact hU

theorem sum_normSq_eigOverlap (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (j : n) :
    ∑ i, ‖eigOverlap hρ hσ i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (eigOverlap_unitary hρ hσ) j) j
  rw [Matrix.mul_apply] at h
  have h2 : ∑ i, (starRingEnd ℂ) (eigOverlap hρ hσ i j) * eigOverlap hρ hσ i j = (1 : ℂ) := by
    rw [show (1 : ℂ) = (1 : Matrix n n ℂ) j j by simp, ← h]
    exact Finset.sum_congr rfl fun i _ => by simp [Matrix.conjTranspose_apply]
  have h3 : ((∑ i, ‖eigOverlap hρ hσ i j‖ ^ 2 : ℝ) : ℂ) = (1 : ℂ) := by
    rw [← h2, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← conj_mul_self]
  exact_mod_cast h3


/-! ### Spectral formulas for the relative entropy -/

theorem trace_mul_mlog (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    Matrix.trace (ρ * mlog σ)
      = ((∑ j, ∑ i, hρ.eigenvalues j * Real.log (hσ.eigenvalues i) *
          ‖eigOverlap hρ hσ i j‖ ^ 2 : ℝ) : ℂ) := by
  have hid : cfc (id : ℝ → ℝ) ρ = ρ := cfc_id ℝ ρ (Matrix.isHermitian_iff_isSelfAdjoint.mp hρ)
  have hstep : Matrix.trace (ρ * mlog σ) = Matrix.trace (cfc (id : ℝ → ℝ) ρ * cfc Real.log σ) := by
    rw [hid, mlog]
  rw [hstep, trace_cfc_mul_cfc hρ hσ id Real.log]
  rfl

theorem trace_mul_mlog_self (hρ : ρ.IsHermitian) :
    Matrix.trace (ρ * mlog ρ)
      = ((∑ j, hρ.eigenvalues j * Real.log (hρ.eigenvalues j) : ℝ) : ℂ) := by
  rw [trace_mul_mlog hρ hρ]
  norm_cast
  have hW : eigOverlap hρ hρ = 1 := UnitaryGroup.star_mul_self _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · rw [hW]; simp
  · intro i _ hij; rw [hW]; simp [hij]
  · simp

/-- The relative entropy in terms of the spectral data of `ρ` and `σ`. -/
theorem relEntropy_eq_sum (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy ρ σ = ∑ j, ∑ i, ‖eigOverlap hρ hσ i j‖ ^ 2 *
      (hρ.eigenvalues j * (Real.log (hρ.eigenvalues j) - Real.log (hσ.eigenvalues i))) := by
  have hsplit : relEntropy ρ σ
      = (Matrix.trace (ρ * mlog ρ)).re - (Matrix.trace (ρ * mlog σ)).re := by
    rw [relEntropy, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [hsplit, trace_mul_mlog_self hρ, trace_mul_mlog hρ hσ]
  simp only [Complex.ofReal_re]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : hρ.eigenvalues j * Real.log (hρ.eigenvalues j)
      = ∑ i, ‖eigOverlap hρ hσ i j‖ ^ 2 * (hρ.eigenvalues j * Real.log (hρ.eigenvalues j)) := by
    rw [← Finset.sum_mul, sum_normSq_eigOverlap hρ hσ j, one_mul]
  rw [h1, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The trace of `ρ` is the sum of its eigenvalues. -/
theorem re_trace_eq_sum (hρ : ρ.IsHermitian) :
    (Matrix.trace ρ).re = ∑ j, hρ.eigenvalues j := by
  rw [hρ.trace_eq_sum_eigenvalues]
  simp

/-! ### The Sylvester equation -/

theorem trace_diag_mul_mul (d : n → ℂ) (M C : Matrix n n ℂ) :
    Matrix.trace (diagonal d * M * C) = ∑ j, ∑ i, d j * (M j i * C i j) := by
  rw [Matrix.mul_assoc, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.diagonal_mul, Matrix.mul_apply, Finset.mul_sum]

theorem trace_conj_mul_gen (U V C : Matrix n n ℂ) (hU : star U * U = 1) (d : n → ℂ) :
    Matrix.trace (U * diagonal d * star U * (V * C * star U))
      = Matrix.trace (diagonal d * (star U * V) * C) := by
  have h := Matrix.trace_mul_comm U (diagonal d * star U * (V * C * star U))
  simp only [Matrix.mul_assoc] at h ⊢
  rw [h, hU, Matrix.mul_one]

/-- For positive definite `ρ σ` and `t ≥ 0`, the Sylvester equation `σ B + t B ρ = ρ` has a
solution, and the value of `Re tr (ρ B)` at this solution is the explicit spectral sum. -/
theorem exists_sylvester (hρ : ρ.PosDef) (hσ : σ.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    ∃ B₀ : Matrix n n ℂ, σ * B₀ + (t : ℂ) • (B₀ * ρ) = ρ ∧
      (Matrix.trace (ρ * B₀)).re =
        ∑ j, ∑ i, ‖eigOverlap hρ.isHermitian hσ.isHermitian i j‖ ^ 2 *
          (hρ.isHermitian.eigenvalues j ^ 2 /
            (hσ.isHermitian.eigenvalues i + t * hρ.isHermitian.eigenvalues j)) := by
  classical
  have hρ' : ρ.IsHermitian := hρ.isHermitian
  have hσ' : σ.IsHermitian := hσ.isHermitian
  set p : n → ℝ := hρ'.eigenvalues with hp
  set q : n → ℝ := hσ'.eigenvalues with hq
  set U : Matrix n n ℂ := (hρ'.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set V : Matrix n n ℂ := (hσ'.eigenvectorUnitary : Matrix n n ℂ) with hVdef
  set W : Matrix n n ℂ := eigOverlap hρ' hσ' with hWdef
  have hpos : ∀ i j, (0:ℝ) < q i + t * p j := by
    intro i j
    have h1 : 0 < q i := hσ.eigenvalues_pos i
    have h2 : 0 < p j := hρ.eigenvalues_pos j
    nlinarith
  have hne : ∀ i j, ((q i : ℂ) + (t : ℂ) * (p j : ℂ)) ≠ 0 := by
    intro i j
    have : ((q i : ℂ) + (t : ℂ) * (p j : ℂ)) = ((q i + t * p j : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast (hpos i j).ne'
  have hUU : star U * U = 1 := UnitaryGroup.star_mul_self _
  have hVV' : V * star V = 1 := (Unitary.mem_iff.mp hσ'.eigenvectorUnitary.2).2
  have hVV : star V * V = 1 := UnitaryGroup.star_mul_self _
  have hspecρ : ρ = U * diagonal (RCLike.ofReal ∘ p) * star U := hρ'.spectral_theorem
  have hspecσ : σ = V * diagonal (RCLike.ofReal ∘ q) * star V := hσ'.spectral_theorem
  have hVW : V * W = U := by
    rw [hWdef, eigOverlap, ← Matrix.mul_assoc, hVV', Matrix.one_mul]
  set C : Matrix n n ℂ :=
    Matrix.of (fun i j => W i j * (p j : ℂ) / ((q i : ℂ) + (t : ℂ) * (p j : ℂ))) with hC
  refine ⟨V * C * star U, ?_, ?_⟩
  · -- the Sylvester equation
    have key : diagonal (RCLike.ofReal ∘ q) * C + (t : ℂ) • (C * diagonal (RCLike.ofReal ∘ p))
        = W * diagonal (RCLike.ofReal ∘ p) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Function.comp_apply, smul_eq_mul, hC, Matrix.of_apply,
        show ∀ x : ℝ, (RCLike.ofReal x : ℂ) = (x : ℂ) from fun _ => rfl]
      simp only [div_mul_eq_mul_div, mul_div_assoc']
      rw [← add_div, div_eq_iff (hne i j)]
      ring
    calc σ * (V * C * star U) + (t : ℂ) • (V * C * star U * ρ)
        = V * (diagonal (RCLike.ofReal ∘ q) * C) * star U
          + (t : ℂ) • (V * (C * diagonal (RCLike.ofReal ∘ p)) * star U) := by
          rw [hspecσ]
          conv_lhs => rw [hspecρ]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (star V) V, hVV, Matrix.one_mul,
            ← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
      _ = V * (diagonal (RCLike.ofReal ∘ q) * C
            + (t : ℂ) • (C * diagonal (RCLike.ofReal ∘ p))) * star U := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = V * (W * diagonal (RCLike.ofReal ∘ p)) * star U := by rw [key]
      _ = ρ := by
          rw [← Matrix.mul_assoc, hVW, hspecρ]
  · -- the value of the trace
    rw [hspecρ]
    rw [trace_conj_mul_gen U V C hUU]
    have hWH : star U * V = Wᴴ := by
      rw [hWdef, eigOverlap]
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hUdef, hVdef]
    rw [hWH, trace_diag_mul_mul]
    have : ∀ j i, (RCLike.ofReal (p j) : ℂ) * (Wᴴ j i * C i j)
        = ((‖W i j‖ ^ 2 * (p j ^ 2 / (q i + t * p j)) : ℝ) : ℂ) := by
      intro j i
      simp only [hC, Matrix.of_apply, Matrix.conjTranspose_apply, RCLike.star_def]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      push_cast
      rw [show ((starRingEnd ℂ) (W i j)) * ((W i j) * (p j : ℂ) *
          ((q i : ℂ) + (t : ℂ) * (p j : ℂ))⁻¹)
          = (((starRingEnd ℂ) (W i j)) * (W i j)) * ((p j : ℂ) *
            ((q i : ℂ) + (t : ℂ) * (p j : ℂ))⁻¹) by ring]
      rw [conj_mul_self]
      push_cast
      simp only [show ∀ x : ℝ, (RCLike.ofReal x : ℂ) = (x : ℂ) from fun _ => rfl]
      ring
    simp only [Function.comp_apply]
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => this j i]
    simp only [← Complex.ofReal_sum, Complex.ofReal_re]

end QI

import RequestProject.QI.Integral

/-!
# The data-processing inequality for the quantum relative entropy

The main result of this development is `QI.data_processing`: for a quantum channel `Φ`
(a completely positive trace preserving map, given in Kraus form) and positive definite
matrices `ρ`, `σ`,

`D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)`,

where `D` is the Umegaki relative entropy `QI.relEntropy`.

The proof combines two ingredients:

* the integral representation
  `relEntropy ρ σ = ∫_{t>0} (Rval ρ σ t - (tr ρ).re/(1+t)) dt` (`QI.relEntropy_eq_integral`),
  where `Rval ρ σ t` is the supremum of an explicit quadratic functional;
* the monotonicity `Rval (Φ ρ) (Φ σ) t ≤ Rval ρ σ t` (`QI.Rval_apply_le`), which follows from
  the Kadison–Schwarz inequality for the adjoint (Heisenberg picture) map of the channel.

Trace preservation of the channel makes the subtracted terms `(tr ρ).re/(1+t)` agree.
-/

namespace QI

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators MatrixOrder

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- **Data-processing inequality (monotonicity of the quantum relative entropy under CPTP
maps).** For a quantum channel `Φ` given in Kraus form and positive definite `ρ`, `σ` such that
`Φ(σ)` is positive definite, the Umegaki relative entropy satisfies
`D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)`. -/
theorem data_processing (Φ : Channel n m ι) {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef)
    (hσ : σ.PosDef) (hΦσ : (Φ.apply σ).PosDef) :
    relEntropy (Φ.apply ρ) (Φ.apply σ) ≤ relEntropy ρ σ := by
  have hΦρ : (Φ.apply ρ).PosDef := Φ.apply_posDef_of_apply_posDef hρ hΦσ
  have hint₁ := integrableOn_relIntegrand hΦρ hΦσ
  have hint₂ := integrableOn_relIntegrand hρ hσ
  rw [Φ.trace_apply ρ] at hint₁
  rw [relEntropy_eq_integral hΦρ hΦσ, relEntropy_eq_integral hρ hσ, Φ.trace_apply ρ]
  refine setIntegral_mono_on hint₁ hint₂ measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  obtain ⟨B₀, hB₀, -⟩ := exists_sylvester hρ hσ ht'
  have := Rval_apply_le Φ hρ.posSemidef hσ.posSemidef ht' hB₀
  linarith

end QI

