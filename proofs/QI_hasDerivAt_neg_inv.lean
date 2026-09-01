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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI

theorem hasDerivAt_neg_inv {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => -(c + t)⁻¹) ((c + t)⁻¹ * (c + t)⁻¹) t := by
  have h0 : c + t ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => c + t) 1 t := by simpa using (hasDerivAt_id t).const_add c
  have h2 := (h1.inv h0).neg
  convert h2 using 1
  field_simp

theorem continuousWithinAt_neg_inv {c : ℝ} (hc : 0 < c) :
    ContinuousWithinAt (fun t : ℝ => -(c + t)⁻¹) (Ici 0) 0 := by
  apply ContinuousAt.continuousWithinAt
  refine ((continuousAt_const.add continuousAt_id).inv₀ ?_).neg
  simpa using hc.ne'

theorem tendsto_neg_inv_atTop {c : ℝ} : Tendsto (fun t : ℝ => -(c + t)⁻¹) atTop (𝓝 0) := by
  have : Tendsto (fun t : ℝ => c + t) atTop atTop := tendsto_atTop_add_const_left _ c tendsto_id
  simpa using (this.inv_tendsto_atTop).neg

/-- Integrability of the square of a resolvent. -/
theorem integrableOn_resSq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (c + t)⁻¹ * (c + t)⁻¹) (Ioi 0) := by
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (g := fun t : ℝ => -(c + t)⁻¹) (l := 0)
    (continuousWithinAt_neg_inv hc) (fun t ht => hasDerivAt_neg_inv hc (le_of_lt ht))
    (fun t ht => ?_) tendsto_neg_inv_atTop
  have : 0 < c + t := by simp only [mem_Ioi] at ht; linarith
  positivity

/-- `∫₀^∞ c/(c+t)² dt = 1`. -/
theorem integral_resSq {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0:ℝ), c * ((c + t)⁻¹ * (c + t)⁻¹) = 1 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun t : ℝ => c * -(c + t)⁻¹) (f' := fun t : ℝ => c * ((c + t)⁻¹ * (c + t)⁻¹))
    (a := 0) (m := 0) ((continuousWithinAt_neg_inv hc).const_smul c)
    (fun t ht => (hasDerivAt_neg_inv hc (le_of_lt ht)).const_mul c)
    ((integrableOn_resSq hc).const_mul c)
    (by simpa using (tendsto_neg_inv_atTop (c := c)).const_mul c)
  rw [h]
  field_simp
  ring

/-- Integrability of the product of two resolvents. -/
theorem integrableOn_resProd {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (a + t)⁻¹ * (b + t)⁻¹) (Ioi 0) := by
  set c := min a b with hc
  have hc0 : 0 < c := lt_min ha hb
  refine MeasureTheory.Integrable.mono' (integrableOn_resSq hc0) ?_ ?_
  · exact ((measurable_const.add measurable_id).inv.mul
      (measurable_const.add measurable_id).inv).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    have hat : 0 < a + t := by linarith
    have hbt : 0 < b + t := by linarith
    have hct : 0 < c + t := by linarith [lt_min ha hb]
    have h1 : c + t ≤ a + t := by simp [hc]
    have h2 : c + t ≤ b + t := by simp [hc]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr

/-- Integrability of `t ↦ (1+t)⁻¹ - (a+t)⁻¹` on `(0, ∞)`. -/
theorem integrableOn_logKernel {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (1 + t)⁻¹ - (a + t)⁻¹) (Ioi 0) := by
  refine MeasureTheory.IntegrableOn.congr_fun
    ((integrableOn_resProd one_pos ha).const_mul (a - 1)) ?_ measurableSet_Ioi
  intro t ht
  simp only [mem_Ioi] at ht
  have h1 : (1 : ℝ) + t ≠ 0 := by positivity
  have h2 : a + t ≠ 0 := by positivity
  field_simp
  ring

/-- `∫₀^∞ (1/(1+t) - 1/(a+t)) dt = log a`. -/
theorem integral_logKernel {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0:ℝ), ((1 + t)⁻¹ - (a + t)⁻¹) = Real.log a := by
  have hlim : Tendsto (fun t : ℝ => Real.log (1 + t) - Real.log (a + t)) atTop (𝓝 0) := by
    have hratio : Tendsto (fun t : ℝ => 1 + (1 - a) / (a + t)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun t : ℝ => (1 - a) / (a + t)) atTop (𝓝 0) := by
        apply Filter.Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_left _ a tendsto_id
      simpa using h0.const_add 1
    have heq : ∀ᶠ t : ℝ in atTop, Real.log (1 + t) - Real.log (a + t)
        = Real.log (1 + (1 - a) / (a + t)) := by
      filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (-a)] with t ht hta
      have h1 : (0:ℝ) < 1 + t := by linarith
      have h2 : (0:ℝ) < a + t := by linarith
      rw [← Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
      congr 1
      field_simp
      ring
    rw [tendsto_congr' heq]
    have := (Real.continuousAt_log (x := 1) one_ne_zero).tendsto.comp hratio
    simpa using this
  have hderiv : ∀ t ∈ Ioi (0:ℝ),
      HasDerivAt (fun t : ℝ => Real.log (1 + t) - Real.log (a + t)) ((1 + t)⁻¹ - (a + t)⁻¹) t := by
    intro t ht
    simp only [mem_Ioi] at ht
    have h1 : (1:ℝ) + t ≠ 0 := by positivity
    have h2 : a + t ≠ 0 := by positivity
    have d1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 + t)⁻¹ t := by
      simpa using ((hasDerivAt_id t).const_add (1:ℝ)).log h1
    have d2 : HasDerivAt (fun t : ℝ => Real.log (a + t)) (a + t)⁻¹ t := by
      simpa using ((hasDerivAt_id t).const_add a).log h2
    exact d1.sub d2
  have hcont : ContinuousWithinAt (fun t : ℝ => Real.log (1 + t) - Real.log (a + t)) (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    exact (ContinuousAt.log (by fun_prop) (by norm_num)).sub
      (ContinuousAt.log (by fun_prop) (by simpa using ha.ne'))
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_logKernel ha) hlim
  rw [h]
  simp

/-- The logarithmic mean is at most the arithmetic mean: `2/(a+b) ≤ ∫₀^∞ dt/((a+t)(b+t))`. -/
theorem two_div_add_le_integral_resProd {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 / (a + b) ≤ ∫ t in Ioi (0:ℝ), (a + t)⁻¹ * (b + t)⁻¹ := by
  set c := (a + b) / 2 with hcdef
  have hc : 0 < c := by positivity
  have hmono : ∫ t in Ioi (0:ℝ), (c + t)⁻¹ * (c + t)⁻¹
      ≤ ∫ t in Ioi (0:ℝ), (a + t)⁻¹ * (b + t)⁻¹ := by
    refine MeasureTheory.setIntegral_mono_on (integrableOn_resSq hc) (integrableOn_resProd ha hb)
      measurableSet_Ioi (fun t ht => ?_)
    simp only [mem_Ioi] at ht
    have hat : 0 < a + t := by linarith
    have hbt : 0 < b + t := by linarith
    rw [← mul_inv, ← mul_inv]
    apply inv_anti₀ (by positivity)
    rw [hcdef]
    nlinarith [sq_nonneg (a - b)]
  have hcinv : ∫ t in Ioi (0:ℝ), (c + t)⁻¹ * (c + t)⁻¹ = 1 / c := by
    have h := integral_resSq hc
    rw [MeasureTheory.integral_const_mul] at h
    field_simp at h ⊢
    linarith
  rw [hcinv] at hmono
  have heq : 2 / (a + b) = 1 / c := by rw [hcdef]; field_simp
  rw [heq]
  exact hmono

theorem pos_path {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : s ∈ uIcc (0:ℝ) 1) :
    0 < q + s * (p - q) := by
  rw [Set.uIcc_of_le (by norm_num)] at hs
  obtain ⟨h0, h1⟩ := hs
  have heq : q + s * (p - q) = (1 - s) * q + s * p := by ring
  rw [heq]
  rcases eq_or_lt_of_le h1 with h | h
  · subst h; simp; linarith
  · have : 0 < (1 - s) * q := by nlinarith
    nlinarith

theorem continuousOn_classical_path {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ContinuousOn (fun s : ℝ => (1 - s) * (p - q) ^ 2 / (q + s * (p - q))) (uIcc (0:ℝ) 1) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro s hs
  exact ne_of_gt (pos_path hp hq hs)

/-- The classical (scalar) path identity underlying the integral representation of the
Kullback-Leibler divergence. -/
theorem classical_path_identity {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ s in Ioo (0:ℝ) 1, (1 - s) * (p - q) ^ 2 / (q + s * (p - q))
      = p * Real.log p - p * Real.log q - p + q := by
  have hderiv : ∀ s ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => p * Real.log (q + s * (p - q)) - (q + s * (p - q)))
        ((1 - s) * (p - q) ^ 2 / (q + s * (p - q))) s := by
    intro s hs
    have hne : q + s * (p - q) ≠ 0 := ne_of_gt (pos_path hp hq hs)
    have h1 : HasDerivAt (fun s : ℝ => q + s * (p - q)) (p - q) s := by
      simpa using ((hasDerivAt_id s).mul_const (p - q)).const_add q
    have h3 := ((h1.log hne).const_mul p).sub h1
    convert h3 using 1
    field_simp
    ring
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_classical_path hp hq).intervalIntegrable
  rw [intervalIntegral.integral_of_le (by norm_num)] at key
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo] at key
  rw [key]
  simp
  ring

/-- Integrability of the classical path integrand. -/
theorem integrableOn_classical_path {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ => (1 - s) * (p - q) ^ 2 / (q + s * (p - q))) (Ioo 0 1) := by
  have h : IntegrableOn (fun s : ℝ => (1 - s) * (p - q) ^ 2 / (q + s * (p - q))) (Icc 0 1) := by
    apply ContinuousOn.integrableOn_Icc
    simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using continuousOn_classical_path hp hq
  exact h.mono_set Set.Ioo_subset_Icc_self

end QI

import RequestProject.QI.Measurement
import RequestProject.QI.PathIdentity

/-!
# Monotonicity of the relative entropy under measurements

The Umegaki relative entropy of two faithful states dominates the Kullback-Leibler divergence
of the outcome distributions of any POVM measurement performed on them.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ρ σ : Mat n} {Y : Type*} [Fintype Y] {E : Y → Mat n}

/-- **Data processing inequality for measurements.** -/
theorem relEntropy_measurement (hρ : ρ.PosDef) (hσ : σ.PosDef) (htr : ρ.trace = σ.trace)
    (hE : IsPOVM E) :
    ∑ y, ((ρ * E y).trace.re * Real.log ((ρ * E y).trace.re)
        - (ρ * E y).trace.re * Real.log ((σ * E y).trace.re)) ≤ relEntropy ρ σ := by
  classical
  set P : Y → ℝ := fun y => (ρ * E y).trace.re with hP
  set Q : Y → ℝ := fun y => (σ * E y).trace.re with hQ
  set S : Finset Y := Finset.univ.filter (fun y => E y ≠ 0) with hS
  have hPnn : ∀ y, 0 ≤ P y := fun y => trace_mul_nonneg hρ (hE.posSemidef y)
  have hQnn : ∀ y, 0 ≤ Q y := fun y => trace_mul_nonneg hσ (hE.posSemidef y)
  have hmemS : ∀ y, y ∈ S ↔ E y ≠ 0 := by intro y; simp [hS]
  have hPpos : ∀ y ∈ S, 0 < P y := by
    intro y hy
    rcases eq_or_lt_of_le (hPnn y) with h | h
    · exact absurd (eq_zero_of_trace_mul_eq_zero hρ (hE.posSemidef y) h.symm) ((hmemS y).mp hy)
    · exact h
  have hQpos : ∀ y ∈ S, 0 < Q y := by
    intro y hy
    rcases eq_or_lt_of_le (hQnn y) with h | h
    · exact absurd (eq_zero_of_trace_mul_eq_zero hσ (hE.posSemidef y) h.symm) ((hmemS y).mp hy)
    · exact h
  have hEzero : ∀ y ∉ S, E y = 0 := by
    intro y hy
    by_contra h
    exact hy ((hmemS y).mpr h)
  have hPzero : ∀ y ∉ S, P y = 0 := by intro y hy; simp [hP, hEzero y hy]
  have hQzero : ∀ y ∉ S, Q y = 0 := by intro y hy; simp [hQ, hEzero y hy]
  -- the two outcome distributions have equal total mass
  have htotal : ∀ (A : Mat n), ∑ y, (A * E y).trace.re = A.trace.re := by
    intro A
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hE.sum_eq_one, mul_one]
  have hsumP : ∑ y ∈ S, P y = ρ.trace.re := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun y _ hy => hPzero y hy)]
    exact htotal ρ
  have hsumQ : ∑ y ∈ S, Q y = σ.trace.re := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun y _ hy => hQzero y hy)]
    exact htotal σ
  have hsum_eq : ∑ y ∈ S, P y = ∑ y ∈ S, Q y := by rw [hsumP, hsumQ, htr]
  -- rewrite the left hand side as a sum of integrals
  have hLHS : ∑ y, (P y * Real.log (P y) - P y * Real.log (Q y))
      = ∑ y ∈ S, (P y * Real.log (P y) - P y * Real.log (Q y)) :=
    (Finset.sum_subset (Finset.subset_univ S) (fun y _ hy => by simp [hPzero y hy])).symm
  have hterm : ∀ y ∈ S, P y * Real.log (P y) - P y * Real.log (Q y)
      = (∫ s in Ioo (0:ℝ) 1, (1 - s) * (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)))
          + (P y - Q y) := by
    intro y hy
    rw [classical_path_identity (hPpos y hy) (hQpos y hy)]
    ring
  have hsplit : ∑ y ∈ S, (P y * Real.log (P y) - P y * Real.log (Q y))
      = ∑ y ∈ S, ∫ s in Ioo (0:ℝ) 1, (1 - s) * (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum_eq]
    ring
  have hswap : ∑ y ∈ S, (∫ s in Ioo (0:ℝ) 1, (1 - s) * (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)))
      = ∫ s in Ioo (0:ℝ) 1, ∑ y ∈ S, (1 - s) * (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)) :=
    (MeasureTheory.integral_finset_sum S
      (fun y hy => integrableOn_classical_path (hPpos y hy) (hQpos y hy))).symm
  rw [hLHS, hsplit, hswap, relEntropy_eq_path hρ hσ htr]
  refine MeasureTheory.setIntegral_mono_on
    (MeasureTheory.integrable_finset_sum S
      (fun y hy => integrableOn_classical_path (hPpos y hy) (hQpos y hy)))
    (integrableOn_path hρ hσ htr) measurableSet_Ioo (fun s hs => ?_)
  obtain ⟨hs0, hs1⟩ := hs
  have hωs : (pathState ρ σ s).PosDef := pathState_posDef hρ hσ hs0.le hs1.le
  have hΔ : (ρ - σ).IsHermitian := hρ.isHermitian.sub hσ.isHermitian
  have hnum : ∀ y, ((ρ - σ) * E y).trace.re = P y - Q y := by
    intro y
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  have hden : ∀ y, ((pathState ρ σ s) * E y).trace.re = Q y + s * (P y - Q y) := by
    intro y
    rw [trace_pathState, Complex.add_re, Complex.mul_re]
    simp [hP, hQ, Complex.sub_re]
  have key := meas_le_bkm hωs hΔ hE
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => by
    rw [hnum y, hden y] : ∀ _, _)] at key
  have hsubset : ∑ y ∈ S, (P y - Q y) ^ 2 / (Q y + s * (P y - Q y))
      = ∑ y, (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)) :=
    Finset.sum_subset (Finset.subset_univ S) (fun y _ hy => by
      simp [hPzero y hy, hQzero y hy])
  have hfac : ∑ y ∈ S, (1 - s) * (P y - Q y) ^ 2 / (Q y + s * (P y - Q y))
      = (1 - s) * ∑ y ∈ S, (P y - Q y) ^ 2 / (Q y + s * (P y - Q y)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hfac, hsubset]
  exact mul_le_mul_of_nonneg_left key (by linarith)

end QI

import RequestProject.QI.Bkm

/-!
# Uniform estimates on resolvents

Bounds on the traces `Tr (A R B R)` with `R = (ω + t)⁻¹`, uniform over families of matrices
whose spectra are bounded below.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ω : Mat n}

/-- The squared Frobenius norm of a matrix. -/
noncomputable def frobSq (A : Mat n) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem frobSq_nonneg (A : Mat n) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem frobSq_eq_trace (A : Mat n) : frobSq A = (Aᴴ * A).trace.re := by
  rw [trace_mul_eq_sum, Complex.re_sum, frobSq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm, mul_conj_norm]
  norm_cast

theorem frobSq_cj (hω : ω.PosDef) (A : Mat n) : frobSq (cj hω A) = frobSq A := by
  rw [frobSq_eq_trace, frobSq_eq_trace, ← cj_conjTranspose, ← cj_mul, trace_cj]

/-- If `ω - m` is positive semidefinite then all eigenvalues of `ω` are at least `m`. -/
theorem eigV_ge_of_sub_posSemidef (hω : ω.PosDef) {m : ℝ}
    (h : (ω - ((m : ℝ) : ℂ) • 1).PosSemidef) (i : Fin n) : m ≤ eigV hω i := by
  have hEq : ω + ((-m : ℝ) : ℂ) • 1 = ω - ((m : ℝ) : ℂ) • 1 := by
    push_cast
    module
  have hpsd : (cj hω (ω + ((-m : ℝ) : ℂ) • 1)).PosSemidef := by
    rw [hEq]
    exact cj_posSemidef hω h
  rw [cj_shift hω (-m)] at hpsd
  have hd : (0 : ℂ) ≤ Matrix.diagonal (fun i => ((eigV hω i + -m : ℝ) : ℂ)) i i :=
    hpsd.diag_nonneg
  rw [Matrix.diagonal_apply_eq] at hd
  have := (Complex.le_def.mp hd).1
  simp only [Complex.zero_re, Complex.ofReal_re] at this
  linarith

/-- Every positive definite matrix dominates a positive multiple of the identity. -/
theorem exists_pos_sub_posSemidef (hω : ω.PosDef) :
    ∃ m : ℝ, 0 < m ∧ (ω - ((m : ℝ) : ℂ) • 1).PosSemidef := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with he | hne
  · refine ⟨1, one_pos, ?_⟩
    have hzero : (ω - ((1 : ℝ) : ℂ) • 1 : Mat n) = 0 := by
      ext i j
      exact (IsEmpty.false i).elim
    rw [hzero]
    exact Matrix.PosSemidef.zero
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty (eigV hω), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      exact fun i _ => eigV_pos hω i
    · set m : ℝ := Finset.univ.inf' Finset.univ_nonempty (eigV hω) with hm
      refine posSemidef_of_cj hω ?_
      have hEq : ω - ((m : ℝ) : ℂ) • 1 = ω + ((-m : ℝ) : ℂ) • 1 := by
        push_cast
        module
      rw [hEq, cj_shift hω (-m)]
      refine Matrix.PosSemidef.diagonal fun i => ?_
      show (0 : ℂ) ≤ ((eigV hω i + -m : ℝ) : ℂ)
      have hle : m ≤ eigV hω i := Finset.inf'_le _ (Finset.mem_univ i)
      have hnn : (0 : ℝ) ≤ eigV hω i + -m := by linarith
      exact_mod_cast hnn

/-- A uniform bound on the quadratic resolvent traces. -/
theorem abs_trace_res_quad_le (hω : ω.PosDef) {m t : ℝ} (hm : ∀ i, m ≤ eigV hω i) (ht : 0 ≤ t)
    (hmt : 0 < m + t) (A B : Mat n) :
    |(A * res ω t * B * res ω t).trace.re|
      ≤ (frobSq A + frobSq B) / 2 * ((m + t)⁻¹ * (m + t)⁻¹) := by
  have hrle : ∀ i, (eigV hω i + t)⁻¹ ≤ (m + t)⁻¹ := by
    intro i
    have h1 : 0 < m + t := hmt
    have h2 : m + t ≤ eigV hω i + t := by linarith [hm i]
    exact inv_anti₀ h1 h2
  have hrnn : ∀ i, 0 ≤ (eigV hω i + t)⁻¹ := by
    intro i
    have : 0 < eigV hω i + t := by linarith [eigV_pos hω i]
    positivity
  rw [trace_res_quad hω ht A B]
  set a : Fin n → Fin n → ℂ := fun i j => cj hω A i j with ha
  set b : Fin n → Fin n → ℂ := fun i j => cj hω B i j with hb
  calc |(∑ i, ∑ j, a i j * (((eigV hω j + t)⁻¹ : ℝ) : ℂ) * b j i
            * (((eigV hω i + t)⁻¹ : ℝ) : ℂ)).re|
      ≤ ‖∑ i, ∑ j, a i j * (((eigV hω j + t)⁻¹ : ℝ) : ℂ) * b j i
            * (((eigV hω i + t)⁻¹ : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖a i j‖ * ‖b j i‖ * ((eigV hω j + t)⁻¹ * (eigV hω i + t)⁻¹) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine le_of_eq ?_
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hrnn i), abs_of_nonneg (hrnn j)]
        ring
    _ ≤ ∑ i, ∑ j, ‖a i j‖ * ‖b j i‖ * ((m + t)⁻¹ * (m + t)⁻¹) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have hnn : 0 ≤ ‖a i j‖ * ‖b j i‖ := by positivity
        have hstep : (eigV hω j + t)⁻¹ * (eigV hω i + t)⁻¹ ≤ (m + t)⁻¹ * (m + t)⁻¹ :=
          mul_le_mul (hrle j) (hrle i) (hrnn i) (le_of_lt (inv_pos.mpr hmt))
        exact mul_le_mul_of_nonneg_left hstep hnn
    _ = (∑ i, ∑ j, ‖a i j‖ * ‖b j i‖) * ((m + t)⁻¹ * (m + t)⁻¹) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    _ ≤ (frobSq A + frobSq B) / 2 * ((m + t)⁻¹ * (m + t)⁻¹) := by
        have hsum : ∑ i, ∑ j, ‖a i j‖ * ‖b j i‖ ≤ (frobSq A + frobSq B) / 2 := by
          have hstep : ∀ i, ∑ j, ‖a i j‖ * ‖b j i‖
              ≤ ∑ j, (‖a i j‖ ^ 2 / 2 + ‖b j i‖ ^ 2 / 2) := by
            intro i
            refine Finset.sum_le_sum fun j _ => ?_
            nlinarith [sq_nonneg (‖a i j‖ - ‖b j i‖)]
          have h1 : ∑ i, ∑ j, ‖a i j‖ * ‖b j i‖
              ≤ ∑ i, ∑ j, (‖a i j‖ ^ 2 / 2 + ‖b j i‖ ^ 2 / 2) :=
            Finset.sum_le_sum fun i _ => hstep i
          have hA2 : ∑ i, ∑ j, ‖a i j‖ ^ 2 / 2 = frobSq (cj hω A) / 2 := by
            rw [frobSq, Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_div _ _ _).symm
          have hB2 : ∑ i, ∑ j, ‖b j i‖ ^ 2 / 2 = frobSq (cj hω B) / 2 := by
            rw [Finset.sum_comm, frobSq, Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_div _ _ _).symm
          have h2 : ∑ i, ∑ j, (‖a i j‖ ^ 2 / 2 + ‖b j i‖ ^ 2 / 2)
              = frobSq (cj hω A) / 2 + frobSq (cj hω B) / 2 := by
            rw [← hA2, ← hB2, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
          rw [h2, frobSq_cj, frobSq_cj] at h1
          linarith
        have hpos : 0 ≤ (m + t)⁻¹ * (m + t)⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_right hsum hpos

end QI

import RequestProject.QI.Defs

/-!
# Spectral tools

Elementary facts about unitary conjugation and the functional calculus of Hermitian matrices,
used to compute traces in an eigenbasis.
-/

open Matrix
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ}

/-- Conjugation of a matrix by a unitary preserves the trace. -/
theorem trace_conj (U A : Mat n) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (star U * A * U).trace = A.trace := by
  rw [Matrix.trace_mul_cycle]
  rw [show U * star U = 1 from Matrix.mem_unitaryGroup_iff.mp hU]
  simp

theorem conj_mul (U A B : Mat n) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    star U * (A * B) * U = (star U * A * U) * (star U * B * U) := by
  calc star U * (A * B) * U = star U * A * (U * star U) * B * U := by
        rw [show U * star U = 1 from Matrix.mem_unitaryGroup_iff.mp hU]; noncomm_ring
    _ = (star U * A * U) * (star U * B * U) := by noncomm_ring

theorem conj_inv (U A : Mat n) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hA : IsUnit A) :
    star U * A⁻¹ * U = (star U * A * U)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← conj_mul _ _ _ hU, Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hA)]
  simpa using Matrix.mem_unitaryGroup_iff'.mp hU

theorem trace_mul_diagonal (A : Mat n) (d : Fin n → ℂ) :
    (A * Matrix.diagonal d).trace = ∑ i, A i i * d i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

/-- Trace of a product `A D B E` with `D, E` diagonal. -/
theorem trace_diag_mul_diag (A B : Mat n) (d e : Fin n → ℂ) :
    (A * Matrix.diagonal d * B * Matrix.diagonal e).trace = ∑ i, ∑ j, A i j * d j * B j i * e i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_mul, mul_ite,
    Finset.sum_ite_eq']

end QI

import RequestProject.QI.DPI

/-!
# The Holevo bound

The accessible information of an ensemble of quantum states is at most its Holevo `χ` quantity.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
  {p : X → ℝ} {ρ : X → Mat n} {E : Y → Mat n}

theorem ensembleAvg_posDef (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hρ : ∀ x, (ρ x).PosDef) : (ensembleAvg p ρ).PosDef := by
  classical
  obtain ⟨x₀, -, hx₀⟩ : ∃ x₀ ∈ Finset.univ, 0 < p x₀ := by
    by_contra h
    push_neg at h
    have hle : ∑ x, p x ≤ 0 := Finset.sum_nonpos fun x hx => h x hx
    rw [hp1] at hle
    norm_num at hle
  rw [ensembleAvg, ← Finset.add_sum_erase _ _ (Finset.mem_univ x₀)]
  refine Matrix.PosDef.add_posSemidef ((hρ x₀).smul ?_) ?_
  · exact_mod_cast hx₀
  · exact posSemidef_sum _ _ fun x _ => (hρ x).posSemidef.smul (by exact_mod_cast hp0 x)

theorem ensembleAvg_trace (hp1 : ∑ x, p x = 1) (hρ : ∀ x, (ρ x).trace = 1) :
    (ensembleAvg p ρ).trace = 1 := by
  rw [ensembleAvg, Matrix.trace_sum]
  simp only [Matrix.trace_smul, hρ, smul_eq_mul, mul_one]
  rw [← Complex.ofReal_sum, hp1, Complex.ofReal_one]

/-- The Holevo quantity is the average relative entropy of the members of the ensemble to its
average state. -/
theorem holevoChi_eq_sum :
    holevoChi p ρ = ∑ x, p x * relEntropy (ρ x) (ensembleAvg p ρ) := by
  have hlin : (ensembleAvg p ρ * logM (ensembleAvg p ρ)).trace.re
      = ∑ x, p x * (ρ x * logM (ensembleAvg p ρ)).trace.re :=
    trace_sum_smul_mul _ _ _
  have hrhs : ∑ x, p x * relEntropy (ρ x) (ensembleAvg p ρ)
      = (∑ x, p x * (ρ x * logM (ρ x)).trace.re)
        - ∑ x, p x * (ρ x * logM (ensembleAvg p ρ)).trace.re := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [relEntropy]; ring
  rw [hrhs, holevoChi, vnEntropy, hlin]
  simp only [vnEntropy, mul_neg, Finset.sum_neg_distrib]
  ring

/-- The mutual information of the measurement statistics is the average Kullback-Leibler
divergence of the conditional outcome distributions from the average one. -/
theorem mutualInformation_eq_sum (hp0 : ∀ x, 0 ≤ p x) (hρpd : ∀ x, (ρ x).PosDef)
    (hρ : ∀ x, (ρ x).trace = 1) (hE : IsPOVM E) :
    mutualInformation (measureDist p ρ E)
      = ∑ x, p x * ∑ y, ((ρ x * E y).trace.re * Real.log ((ρ x * E y).trace.re)
          - (ρ x * E y).trace.re * Real.log ((ensembleAvg p ρ * E y).trace.re)) := by
  classical
  have hq0 : ∀ x y, 0 ≤ (ρ x * E y).trace.re := fun x y =>
    trace_mul_nonneg (hρpd x) (hE.posSemidef y)
  have hrow : ∀ x, ∑ y, measureDist p ρ E x y = p x := by
    intro x
    simp only [measureDist]
    rw [← Finset.mul_sum]
    have : ∑ y, (ρ x * E y).trace.re = 1 := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hE.sum_eq_one, mul_one, hρ x]
      simp
    rw [this, mul_one]
  have hcol : ∀ y, ∑ x, measureDist p ρ E x y = (ensembleAvg p ρ * E y).trace.re := by
    intro y
    simp only [measureDist, ensembleAvg]
    rw [trace_sum_smul_mul]
  simp only [mutualInformation, hrow, hcol]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  set q : ℝ := (ρ x * E y).trace.re with hqdef
  set r : ℝ := (ensembleAvg p ρ * E y).trace.re with hrdef
  have hmd : measureDist p ρ E x y = p x * q := rfl
  rw [hmd]
  rcases eq_or_lt_of_le (hp0 x) with hpx | hpx
  · simp [← hpx]
  · rw [mul_div_mul_left _ _ (ne_of_gt hpx)]
    have hlog : q * Real.log (q / r) = q * Real.log q - q * Real.log r := by
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ q from hq0 x y) with hq | hq
      · simp [← hq]
      · have hr : 0 < r := by
          rw [hrdef, ← hcol y]
          refine lt_of_lt_of_le ?_ (Finset.single_le_sum
            (f := fun x' => measureDist p ρ E x' y)
            (fun x' _ => mul_nonneg (hp0 x') (hq0 x' y)) (Finset.mem_univ x))
          exact mul_pos hpx hq
        rw [Real.log_div (ne_of_gt hq) (ne_of_gt hr)]
        ring
    rw [mul_assoc, hlog]

/-- **The Holevo bound.**  For any ensemble `(pₓ, ρₓ)` of faithful quantum states and any POVM
measurement `E`, the mutual information between the label `x` and the measurement outcome is at
most the Holevo quantity `χ = S(∑ pₓ ρₓ) - ∑ pₓ S(ρₓ)` of the ensemble. -/
theorem holevo_bound (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hρ : ∀ x, (ρ x).PosDef) (hρ1 : ∀ x, (ρ x).trace = 1) (hE : IsPOVM E) :
    mutualInformation (measureDist p ρ E) ≤ holevoChi p ρ := by
  have hbar : (ensembleAvg p ρ).PosDef := ensembleAvg_posDef hp0 hp1 hρ
  have hbartr : (ensembleAvg p ρ).trace = 1 := ensembleAvg_trace hp1 (fun x => hρ1 x)
  rw [mutualInformation_eq_sum hp0 hρ hρ1 hE, holevoChi_eq_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (hp0 x)
  exact relEntropy_measurement (hρ x) hbar (by rw [hρ1 x, hbartr]) hE

/-- **The Holevo bound for the accessible information.**  The accessible information of an
ensemble of faithful quantum states, measured with POVMs having outcomes in a fixed finite set,
is at most the Holevo quantity of the ensemble. -/
theorem accessibleInfo_le_holevoChi [Nonempty Y] [DecidableEq Y]
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hρ : ∀ x, (ρ x).PosDef) (hρ1 : ∀ x, (ρ x).trace = 1) :
    accessibleInfo Y p ρ ≤ holevoChi p ρ := by
  have hne : Nonempty {E : Y → Mat n // IsPOVM E} := by
    classical
    refine ⟨⟨fun y => if y = Classical.arbitrary Y then 1 else 0, ?_, ?_⟩⟩
    · intro y
      by_cases h : y = Classical.arbitrary Y <;>
        simp [h, Matrix.PosSemidef.one, Matrix.PosSemidef.zero]
    · simp
  exact ciSup_le fun E => holevo_bound hp0 hp1 hρ hρ1 E.2

end QI

import Mathlib

/-!
# Basic definitions for quantum information

We work with finite dimensional quantum systems, whose states are density matrices in
`Matrix (Fin n) (Fin n) ℂ`.
-/

open Matrix
open scoped ComplexOrder BigOperators

namespace QI

/-- Square complex matrices of size `n`, the operators on an `n`-dimensional quantum system. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

variable {n : ℕ}

/-- The matrix logarithm, defined through the continuous functional calculus.  For a positive
definite matrix `A` with spectral decomposition `A = U * diagonal μ * Uᴴ` we have
`logM A = U * diagonal (Real.log ∘ μ) * Uᴴ`. -/
noncomputable def logM (A : Mat n) : Mat n := cfc Real.log A

/-- The von Neumann entropy `S(ρ) = -Tr (ρ log ρ)` of a density matrix. -/
noncomputable def vnEntropy (A : Mat n) : ℝ := -(A * logM A).trace.re

/-- The Umegaki relative entropy `D(ρ‖σ) = Tr ρ log ρ - Tr ρ log σ`. -/
noncomputable def relEntropy (ρ σ : Mat n) : ℝ :=
  (ρ * logM ρ).trace.re - (ρ * logM σ).trace.re

/-- A matrix is a density matrix (a *faithful* quantum state) when it is positive definite of
unit trace. -/
structure IsState (ρ : Mat n) : Prop where
  posDef : ρ.PosDef
  trace_eq_one : ρ.trace = 1

/-- A family `E : Y → Mat n` is a POVM (positive operator valued measure) when all its elements
are positive semidefinite and they sum to the identity. -/
structure IsPOVM {Y : Type*} [Fintype Y] (E : Y → Mat n) : Prop where
  posSemidef : ∀ y, (E y).PosSemidef
  sum_eq_one : ∑ y, E y = 1

/-- The Shannon mutual information of a joint probability distribution `P` on `X × Y`. -/
noncomputable def mutualInformation {X Y : Type*} [Fintype X] [Fintype Y] (P : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, P x y * Real.log (P x y / ((∑ y', P x y') * (∑ x', P x' y)))

/-- The joint distribution of the label `x` and the measurement outcome `y`, for the ensemble
`(p, ρ)` measured with the POVM `E`. -/
noncomputable def measureDist {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (ρ : X → Mat n) (E : Y → Mat n) : X → Y → ℝ :=
  fun x y => p x * ((ρ x * E y).trace.re)

/-- The average state of the ensemble `(p, ρ)`. -/
noncomputable def ensembleAvg {X : Type*} [Fintype X] (p : X → ℝ) (ρ : X → Mat n) : Mat n :=
  ∑ x, (p x : ℂ) • ρ x

/-- The Holevo quantity `χ = S(∑ pₓ ρₓ) - ∑ pₓ S(ρₓ)` of an ensemble. -/
noncomputable def holevoChi {X : Type*} [Fintype X] (p : X → ℝ) (ρ : X → Mat n) : ℝ :=
  vnEntropy (ensembleAvg p ρ) - ∑ x, p x * vnEntropy (ρ x)

/-- The accessible information of an ensemble, when measurements with outcomes in the finite set
`Y` are allowed: the supremum of the mutual information over all POVMs indexed by `Y`. -/
noncomputable def accessibleInfo {X : Type*} (Y : Type*) [Fintype X] [Fintype Y]
    (p : X → ℝ) (ρ : X → Mat n) : ℝ :=
  ⨆ E : {E : Y → Mat n // IsPOVM E}, mutualInformation (measureDist p ρ E.1)

end QI

import RequestProject.QI.Resolvent
import RequestProject.QI.ScalarIntegrals

/-!
# The BKM quadratic form

For a positive definite `ω` and a Hermitian `Δ` we set
`bkm ω Δ = ∫₀^∞ Tr (Δ (ω+t)⁻¹ Δ (ω+t)⁻¹) dt`,
the Bogoliubov–Kubo–Mori quadratic form.  In the eigenbasis of `ω` it is
`∑ᵢⱼ |Δᵢⱼ|² / L(μᵢ, μⱼ)` where `L` is the logarithmic mean of the eigenvalues.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ω Δ : Mat n}

/-- The BKM (Bogoliubov–Kubo–Mori) quadratic form of `Δ` at the positive definite matrix `ω`. -/
noncomputable def bkm (ω Δ : Mat n) : ℝ :=
  ∫ t in Ioi (0:ℝ), (Δ * res ω t * Δ * res ω t).trace.re

theorem mul_conj_norm (z : ℂ) : z * (starRingEnd ℂ) z = ((‖z‖ : ℂ)) ^ 2 := by
  rw [Complex.mul_conj]; norm_cast; exact (Complex.normSq_eq_norm_sq z) ▸ rfl

theorem trace_res_quad_ofReal (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) (hΔ : Δ.IsHermitian) :
    (Δ * res ω t * Δ * res ω t).trace
      = ((∑ i, ∑ j, ‖cj hω Δ i j‖ ^ 2 * ((eigV hω i + t)⁻¹ * (eigV hω j + t)⁻¹) : ℝ) : ℂ) := by
  rw [trace_res_quad hω ht Δ Δ]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : cj hω Δ j i = (starRingEnd ℂ) (cj hω Δ i j) :=
    ((cj_isHermitian hω hΔ).apply j i).symm
  rw [h1]
  linear_combination ((((eigV hω j : ℂ) + t)⁻¹ * (((eigV hω i : ℂ)) + t)⁻¹)) *
    mul_conj_norm (cj hω Δ i j)

/-- The integrand of the BKM form, in the eigenbasis of `ω`. -/
theorem trace_res_quad_re (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) (hΔ : Δ.IsHermitian) :
    (Δ * res ω t * Δ * res ω t).trace.re
      = ∑ i, ∑ j, ‖cj hω Δ i j‖ ^ 2 * ((eigV hω i + t)⁻¹ * (eigV hω j + t)⁻¹) := by
  rw [trace_res_quad_ofReal hω ht hΔ, Complex.ofReal_re]

/-- The BKM form in the eigenbasis of `ω`. -/
theorem bkm_eq_sum (hω : ω.PosDef) (hΔ : Δ.IsHermitian) :
    bkm ω Δ = ∑ i, ∑ j, ‖cj hω Δ i j‖ ^ 2 *
      (∫ t in Ioi (0:ℝ), (eigV hω i + t)⁻¹ * (eigV hω j + t)⁻¹) := by
  unfold bkm
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => trace_res_quad_re hω (le_of_lt ht) hΔ)]
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => ?_)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_finset_sum _ (fun j _ => ?_)]
    · exact Finset.sum_congr rfl fun j _ => MeasureTheory.integral_const_mul _ _
    · exact ((integrableOn_resProd (eigV_pos hω i) (eigV_pos hω j)).const_mul _)
  · exact MeasureTheory.integrable_finset_sum _
      (fun j _ => ((integrableOn_resProd (eigV_pos hω i) (eigV_pos hω j)).const_mul _))

/-- Integrability in `t` of the BKM integrand. -/
theorem integrableOn_res_quad (hω : ω.PosDef) (hΔ : Δ.IsHermitian) :
    IntegrableOn (fun t : ℝ => (Δ * res ω t * Δ * res ω t).trace.re) (Ioi 0) := by
  refine MeasureTheory.IntegrableOn.congr_fun ?_
    (fun t ht => (trace_res_quad_re hω (le_of_lt ht) hΔ).symm) measurableSet_Ioi
  exact MeasureTheory.integrable_finset_sum _ (fun i _ =>
    MeasureTheory.integrable_finset_sum _ (fun j _ =>
      ((integrableOn_resProd (eigV_pos hω i) (eigV_pos hω j)).const_mul _)))

/-- The integrand `Tr (ω R Δ R)` in the eigenbasis of `ω`. -/
theorem trace_omega_res_quad_re (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) (Δ : Mat n) :
    (ω * res ω t * Δ * res ω t).trace.re
      = ∑ i, ((cj hω Δ) i i).re * (eigV hω i * ((eigV hω i + t)⁻¹ * (eigV hω i + t)⁻¹)) := by
  rw [trace_res_quad hω ht ω Δ, cj_self hω]
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hre : ((eigV hω i : ℝ) : ℂ) * (((eigV hω i + t)⁻¹ : ℝ) : ℂ) * (cj hω Δ) i i
        * (((eigV hω i + t)⁻¹ : ℝ) : ℂ)
      = ((eigV hω i * ((eigV hω i + t)⁻¹ * (eigV hω i + t)⁻¹) : ℝ) : ℂ) * (cj hω Δ) i i := by
    push_cast
    ring
  rw [hre]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem integrableOn_omega_res_quad (hω : ω.PosDef) (Δ : Mat n) :
    IntegrableOn (fun t : ℝ => (ω * res ω t * Δ * res ω t).trace.re) (Ioi 0) := by
  refine MeasureTheory.IntegrableOn.congr_fun ?_
    (fun t ht => (trace_omega_res_quad_re hω (le_of_lt ht) Δ).symm) measurableSet_Ioi
  refine MeasureTheory.integrable_finset_sum _ (fun i _ => ?_)
  exact (((integrableOn_resSq (eigV_pos hω i)).const_mul (eigV hω i)).const_mul _)

/-- `∫₀^∞ Tr (ω R Δ R) dt = Tr Δ`. -/
theorem integral_omega_res_quad (hω : ω.PosDef) (Δ : Mat n) :
    (∫ t in Ioi (0:ℝ), (ω * res ω t * Δ * res ω t).trace.re) = Δ.trace.re := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => trace_omega_res_quad_re hω (le_of_lt ht) Δ)]
  rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
    (((integrableOn_resSq (eigV_pos hω i)).const_mul (eigV hω i)).const_mul _))]
  have hsum : ∀ i : Fin n,
      (∫ t in Ioi (0:ℝ), ((cj hω Δ) i i).re * (eigV hω i * ((eigV hω i + t)⁻¹ * (eigV hω i + t)⁻¹)))
        = ((cj hω Δ) i i).re := by
    intro i
    rw [MeasureTheory.integral_const_mul, integral_resSq (eigV_pos hω i), mul_one]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hsum i)]
  rw [← trace_cj hω Δ, Matrix.trace, Complex.re_sum]
  rfl

theorem bkm_nonneg (hω : ω.PosDef) (hΔ : Δ.IsHermitian) : 0 ≤ bkm ω Δ := by
  rw [bkm_eq_sum hω hΔ]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  refine mul_nonneg (by positivity) ?_
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  simp only [mem_Ioi] at ht
  have h1 : 0 < eigV hω i + t := by linarith [eigV_pos hω i]
  have h2 : 0 < eigV hω j + t := by linarith [eigV_pos hω j]
  positivity

/-- Trace of `Δ * A` in the eigenbasis of `ω`. -/
theorem trace_mul_eq_sum_cj (hω : ω.PosDef) (A B : Mat n) :
    (A * B).trace = ∑ i, ∑ j, (cj hω A) i j * (cj hω B) j i := by
  rw [← trace_cj hω (A * B), cj_mul, trace_mul_eq_sum]

/-- Trace of `ω A A` in the eigenbasis of `ω`. -/
theorem trace_omega_sq (hω : ω.PosDef) {A : Mat n} (hA : A.IsHermitian) :
    (ω * A * A).trace = ((∑ i, ∑ j, eigV hω i * ‖cj hω A i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [← trace_cj hω (ω * A * A), cj_mul, cj_mul, cj_self hω, trace_mul_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : cj hω A j i = (starRingEnd ℂ) (cj hω A i j) :=
    ((cj_isHermitian hω hA).apply j i).symm
  simp only [Matrix.diagonal_mul]
  rw [h1]
  linear_combination (eigV hω i : ℂ) * mul_conj_norm (cj hω A i j)

/-- **Key inequality**: the BKM quadratic form dominates `2 Tr(Δ A) - Tr(ω A²)` for every
Hermitian `A`.  This is the operator form of the fact that the logarithmic mean is at most the
arithmetic mean. -/
theorem two_trace_sub_le_bkm (hω : ω.PosDef) (hΔ : Δ.IsHermitian) {A : Mat n}
    (hA : A.IsHermitian) : 2 * (Δ * A).trace.re - (ω * A * A).trace.re ≤ bkm ω Δ := by
  classical
  set d : Fin n → Fin n → ℂ := fun i j => cj hω Δ i j with hd
  set a : Fin n → Fin n → ℂ := fun i j => cj hω A i j with ha
  set μ : Fin n → ℝ := eigV hω with hμ
  have hμpos : ∀ i, 0 < μ i := eigV_pos hω
  have haH : ∀ i j, a j i = (starRingEnd ℂ) (a i j) := fun i j =>
    ((cj_isHermitian hω hA).apply j i).symm
  -- the two traces, in the eigenbasis
  have h1 : (Δ * A).trace.re = ∑ i, ∑ j, (d i j * (starRingEnd ℂ) (a i j)).re := by
    rw [trace_mul_eq_sum_cj hω]
    simp only [← hd, ← ha]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [haH i j]
  have h2 : (ω * A * A).trace.re = ∑ i, ∑ j, μ i * ‖a i j‖ ^ 2 := by
    rw [trace_omega_sq hω hA, Complex.ofReal_re]
  -- symmetrization of the quadratic term
  have hcsym : ∀ i j, ‖a i j‖ = ‖a j i‖ := by
    intro i j
    rw [haH i j, RCLike.norm_conj]
  have hsym : ∑ i, ∑ j, μ i * ‖a i j‖ ^ 2 = ∑ i, ∑ j, ((μ i + μ j) / 2) * ‖a i j‖ ^ 2 := by
    have hswap : ∑ i, ∑ j, μ i * ‖a i j‖ ^ 2 = ∑ i, ∑ j, μ j * ‖a i j‖ ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hcsym j i]
    have expand : ∀ i, ∑ j, ((μ i + μ j) / 2) * ‖a i j‖ ^ 2
        = (∑ j, μ i * ‖a i j‖ ^ 2) / 2 + (∑ j, μ j * ‖a i j‖ ^ 2) / 2 := by
      intro i
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => expand i), Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.sum_div, ← hswap]
    ring
  rw [h1, h2, hsym, bkm_eq_sum hω hΔ]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  -- the scalar inequality
  have hm : 0 < (μ i + μ j) / 2 := by linarith [hμpos i, hμpos j]
  have hk : 2 / (μ i + μ j) ≤ ∫ t in Ioi (0:ℝ), (μ i + t)⁻¹ * (μ j + t)⁻¹ :=
    two_div_add_le_integral_resProd (hμpos i) (hμpos j)
  have hre : (d i j * (starRingEnd ℂ) (a i j)).re ≤ ‖d i j‖ * ‖a i j‖ := by
    calc (d i j * (starRingEnd ℂ) (a i j)).re ≤ ‖d i j * (starRingEnd ℂ) (a i j)‖ :=
          Complex.re_le_norm _
      _ = ‖d i j‖ * ‖a i j‖ := by rw [norm_mul, RCLike.norm_conj]
  have hamgm : 2 * (‖d i j‖ * ‖a i j‖) - ((μ i + μ j) / 2) * ‖a i j‖ ^ 2
      ≤ ‖d i j‖ ^ 2 * (2 / (μ i + μ j)) := by
    have h2m : 2 / (μ i + μ j) = 1 / ((μ i + μ j) / 2) := by
      rw [one_div_div]
    rw [h2m, mul_one_div, le_div_iff₀ hm]
    nlinarith [sq_nonneg (‖d i j‖ - ((μ i + μ j) / 2) * ‖a i j‖)]
  have hfinal : ‖d i j‖ ^ 2 * (2 / (μ i + μ j))
      ≤ ‖d i j‖ ^ 2 * (∫ t in Ioi (0:ℝ), (μ i + t)⁻¹ * (μ j + t)⁻¹) := by
    exact mul_le_mul_of_nonneg_left hk (by positivity)
  calc 2 * (d i j * (starRingEnd ℂ) (a i j)).re - ((μ i + μ j) / 2) * ‖a i j‖ ^ 2
      ≤ 2 * (‖d i j‖ * ‖a i j‖) - ((μ i + μ j) / 2) * ‖a i j‖ ^ 2 := by linarith
    _ ≤ ‖d i j‖ ^ 2 * (2 / (μ i + μ j)) := hamgm
    _ ≤ _ := hfinal

end QI

import RequestProject.QI.Bkm

/-!
# Measurement: the classical Fisher-type quantity is dominated by the BKM form
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ω Δ : Mat n} {Y : Type*} [Fintype Y] {E : Y → Mat n}

/-- The trace of `ω F` in the eigenbasis of `ω`. -/
theorem trace_mul_eq_sum_eig (hω : ω.PosDef) (F : Mat n) :
    (ω * F).trace = ∑ i, ((eigV hω i : ℝ) : ℂ) * (cj hω F) i i := by
  rw [← trace_cj hω (ω * F), cj_mul, cj_self hω, Matrix.trace_mul_comm, trace_mul_diagonal]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem trace_mul_re_eq_sum_eig (hω : ω.PosDef) (F : Mat n) :
    (ω * F).trace.re = ∑ i, eigV hω i * ((cj hω F) i i).re := by
  rw [trace_mul_eq_sum_eig hω F, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by simp

theorem diag_re_nonneg {F : Mat n} (hF : F.PosSemidef) (i : Fin n) : 0 ≤ (F i i).re := by
  have h : (0 : ℂ) ≤ F i i := hF.diag_nonneg
  simpa using (Complex.le_def.mp h).1

theorem trace_mul_nonneg (hω : ω.PosDef) {F : Mat n} (hF : F.PosSemidef) :
    0 ≤ (ω * F).trace.re := by
  rw [trace_mul_re_eq_sum_eig hω]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (eigV_pos hω i).le (diag_re_nonneg (cj_posSemidef hω hF) i)

/-- If `ω` is positive definite, `F` is positive semidefinite and `Tr (ω F) = 0`, then `F = 0`. -/
theorem eq_zero_of_trace_mul_eq_zero (hω : ω.PosDef) {F : Mat n} (hF : F.PosSemidef)
    (h : (ω * F).trace.re = 0) : F = 0 := by
  have hcj : (cj hω F).PosSemidef := cj_posSemidef hω hF
  rw [trace_mul_re_eq_sum_eig hω] at h
  have hterm : ∀ i ∈ Finset.univ, eigV hω i * ((cj hω F) i i).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (eigV_pos hω i).le (diag_re_nonneg hcj i))).mp h
  have hzero : ∀ i, (cj hω F) i i = 0 := by
    intro i
    have hre : ((cj hω F) i i).re = 0 := by
      have := hterm i (Finset.mem_univ i)
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 (ne_of_gt (eigV_pos hω i))
      · exact h1
    have him : ((cj hω F) i i).im = 0 := by
      have h0 : (0 : ℂ) ≤ (cj hω F) i i := hcj.diag_nonneg
      simpa using (Complex.le_def.mp h0).2.symm
    exact Complex.ext hre him
  refine hF.trace_eq_zero_iff.mp ?_
  rw [← trace_cj hω F]
  simp [Matrix.trace, Matrix.diag, hzero]

/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
theorem posSemidef_sum {ι : Type*} (s : Finset ι) (f : ι → Mat n)
    (hf : ∀ i ∈ s, (f i).PosSemidef) : (∑ i ∈ s, f i).PosSemidef := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (by simp)).add (ih fun j hj => hf j (by simp [hj]))

/-- Operator Cauchy-Schwarz for a POVM: `(∑ c y • E y)² ≤ ∑ c y ^ 2 • E y`. -/
theorem povm_sq_le (hE : IsPOVM E) (c : Y → ℝ) :
    ((∑ y, ((c y ^ 2 : ℝ) : ℂ) • E y) -
      (∑ y, ((c y : ℝ) : ℂ) • E y) * (∑ y, ((c y : ℝ) : ℂ) • E y)).PosSemidef := by
  classical
  set A : Mat n := ∑ y, ((c y : ℝ) : ℂ) • E y with hAdef
  have hherm : ∀ y, (E y)ᴴ = E y := fun y => (hE.posSemidef y).isHermitian
  have hAherm : Aᴴ = A := by
    rw [hAdef]
    simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hherm]
  have expand : ∀ y : Y, (((c y : ℝ) : ℂ) • (1 : Mat n) - A) * E y * (((c y : ℝ) : ℂ) • 1 - A)
      = ((c y ^ 2 : ℝ) : ℂ) • E y - ((c y : ℝ) : ℂ) • (E y * A) - ((c y : ℝ) : ℂ) • (A * E y)
        + A * E y * A := by
    intro y
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
    push_cast [pow_two]
    abel
  have h1 : ∑ y, ((c y : ℝ) : ℂ) • (E y * A) = A * A := by
    conv_rhs => rw [hAdef]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => (smul_mul_assoc _ _ _).symm
  have h2 : ∑ y, ((c y : ℝ) : ℂ) • (A * E y) = A * A := by
    conv_rhs => rw [hAdef]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => (mul_smul_comm _ _ _).symm
  have h3 : ∑ y, A * E y * A = A * A := by
    rw [show (∑ y, A * E y * A) = (∑ y, A * E y) * A by rw [Finset.sum_mul],
      ← Finset.mul_sum, hE.sum_eq_one, mul_one]
  have key : (∑ y, ((c y ^ 2 : ℝ) : ℂ) • E y) - A * A
      = ∑ y, (((c y : ℝ) : ℂ) • (1 : Mat n) - A)ᴴ * E y * (((c y : ℝ) : ℂ) • 1 - A) := by
    have hstar : ∀ y : Y, (((c y : ℝ) : ℂ) • (1 : Mat n) - A)ᴴ = ((c y : ℝ) : ℂ) • 1 - A := by
      intro y
      simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hAherm]
    simp only [hstar, expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, h2, h3]
    abel
  rw [key]
  refine posSemidef_sum _ _ fun y _ => ?_
  exact (hE.posSemidef y).conjTranspose_mul_mul_same _

/-- Trace against a real linear combination of the POVM elements. -/
theorem trace_mul_sum_smul (B : Mat n) (c : Y → ℝ) (F : Y → Mat n) :
    (B * ∑ y, ((c y : ℝ) : ℂ) • F y).trace.re = ∑ y, c y * (B * F y).trace.re := by
  rw [Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_smul_comm, Matrix.trace_smul]
  simp

/-- Trace of a real linear combination against a fixed matrix. -/
theorem trace_sum_smul_mul (B : Mat n) (c : Y → ℝ) (F : Y → Mat n) :
    ((∑ y, ((c y : ℝ) : ℂ) • F y) * B).trace.re = ∑ y, c y * (F y * B).trace.re := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_assoc, Matrix.trace_smul]
  simp

/-- **Measurement bound**: for any POVM, the measured `χ²`-type quantity is dominated by the
BKM quadratic form. -/
theorem meas_le_bkm (hω : ω.PosDef) (hΔ : Δ.IsHermitian) (hE : IsPOVM E) :
    ∑ y, ((Δ * E y).trace.re) ^ 2 / ((ω * E y).trace.re) ≤ bkm ω Δ := by
  classical
  set w : Y → ℝ := fun y => (ω * E y).trace.re with hw
  set d : Y → ℝ := fun y => (Δ * E y).trace.re with hd
  set c : Y → ℝ := fun y => d y / w y with hc
  set A : Mat n := ∑ y, ((c y : ℝ) : ℂ) • E y with hAdef
  have hEzero : ∀ y, w y = 0 → E y = 0 := fun y h =>
    eq_zero_of_trace_mul_eq_zero hω (hE.posSemidef y) h
  have hdzero : ∀ y, w y = 0 → d y = 0 := by
    intro y h
    simp [hd, hEzero y h]
  have hAherm : A.IsHermitian := by
    have hherm : ∀ y, (E y)ᴴ = E y := fun y => (hE.posSemidef y).isHermitian
    show Aᴴ = A
    rw [hAdef]
    simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hherm]
  -- the linear term
  have e1 : ∀ y, c y * d y = d y ^ 2 / w y := by
    intro y
    by_cases h : w y = 0
    · simp [hc, h, hdzero y h]
    · simp only [hc]
      field_simp
  have hlin : (Δ * A).trace.re = ∑ y, d y ^ 2 / w y := by
    rw [hAdef, trace_mul_sum_smul]
    exact Finset.sum_congr rfl fun y _ => e1 y
  -- the quadratic term
  have e2 : ∀ y, c y ^ 2 * w y = d y ^ 2 / w y := by
    intro y
    by_cases h : w y = 0
    · simp [hc, h, hdzero y h]
    · simp only [hc]
      field_simp
  have hquad : (ω * A * A).trace.re ≤ ∑ y, d y ^ 2 / w y := by
    have hpsd := trace_mul_nonneg hω (povm_sq_le hE c)
    have hsplit : (ω * ((∑ y, ((c y ^ 2 : ℝ) : ℂ) • E y) - A * A)).trace.re
        = (ω * ∑ y, ((c y ^ 2 : ℝ) : ℂ) • E y).trace.re - (ω * (A * A)).trace.re := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [hsplit, trace_mul_sum_smul] at hpsd
    have : (ω * (A * A)).trace.re ≤ ∑ y, c y ^ 2 * w y := by linarith
    rw [← Matrix.mul_assoc] at this
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun y _ => e2 y))
  have key := two_trace_sub_le_bkm hω hΔ hAherm
  rw [hlin] at key
  linarith

end QI

import RequestProject.QI.Estimates

/-!
# The integral representation of the relative entropy

The Umegaki relative entropy of two faithful states of equal trace is
`D(ρ‖σ) = ∫₀¹ (1-s) · bkm (σ + s(ρ-σ)) (ρ-σ) ds`.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ω ρ σ : Mat n}

/-- The interpolating path `ω s = σ + s (ρ - σ) = (1-s) σ + s ρ`. -/
noncomputable def pathState (ρ σ : Mat n) (s : ℝ) : Mat n := σ + (s : ℂ) • (ρ - σ)

theorem pathState_eq (ρ σ : Mat n) (s : ℝ) :
    pathState ρ σ s = ((1 - s : ℝ) : ℂ) • σ + ((s : ℝ) : ℂ) • ρ := by
  rw [pathState]
  push_cast
  module

theorem pathState_posDef (hρ : ρ.PosDef) (hσ : σ.PosDef) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (pathState ρ σ s).PosDef := by
  rw [pathState_eq]
  rcases eq_or_lt_of_le h1 with h | h
  · subst h
    simpa using hρ
  · refine Matrix.PosDef.add_posSemidef (hσ.smul ?_) (hρ.posSemidef.smul ?_)
    · have : (0:ℝ) < 1 - s := by linarith
      exact_mod_cast this
    · exact_mod_cast h0

theorem trace_pathState (ρ σ : Mat n) (s : ℝ) (A : Mat n) :
    (pathState ρ σ s * A).trace = (σ * A).trace + (s : ℂ) * ((ρ * A).trace - (σ * A).trace) := by
  rw [pathState, Matrix.add_mul, Matrix.trace_add, smul_mul_assoc, Matrix.trace_smul,
    Matrix.sub_mul, Matrix.trace_sub]
  simp

/-- Integrability of the integrand of the integral representation of `Tr (A log ω)`. -/
theorem integrableOn_logKernel_trace (hω : ω.PosDef) (A : Mat n) :
    IntegrableOn (fun t : ℝ => A.trace.re * (1 + t)⁻¹ - (A * res ω t).trace.re) (Ioi 0) := by
  have heq : ∀ t ∈ Ioi (0:ℝ), A.trace.re * (1 + t)⁻¹ - (A * res ω t).trace.re
      = ∑ i, ((cj hω A) i i).re * ((1 + t)⁻¹ - (eigV hω i + t)⁻¹) := by
    intro t ht
    have h1 : A.trace.re = ∑ i, ((cj hω A) i i).re := by
      rw [← trace_cj hω A, Matrix.trace, Complex.re_sum]
      rfl
    have h2 : (A * res ω t).trace.re = ∑ i, ((cj hω A) i i).re * (eigV hω i + t)⁻¹ := by
      rw [trace_mul_res hω (le_of_lt ht), Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [h1, h2, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine MeasureTheory.IntegrableOn.congr_fun ?_ (fun t ht => (heq t ht).symm) measurableSet_Ioi
  exact MeasureTheory.integrable_finset_sum _
    (fun i _ => (integrableOn_logKernel (eigV_pos hω i)).const_mul _)

/-- Integral representation of `Tr (A log ω)`. -/
theorem trace_mul_logM_integral (hω : ω.PosDef) (A : Mat n) :
    (A * logM ω).trace.re
      = ∫ t in Ioi (0:ℝ), (A.trace.re * (1 + t)⁻¹ - (A * res ω t).trace.re) := by
  have heq : ∀ t ∈ Ioi (0:ℝ), A.trace.re * (1 + t)⁻¹ - (A * res ω t).trace.re
      = ∑ i, ((cj hω A) i i).re * ((1 + t)⁻¹ - (eigV hω i + t)⁻¹) := by
    intro t ht
    have h1 : A.trace.re = ∑ i, ((cj hω A) i i).re := by
      rw [← trace_cj hω A, Matrix.trace, Complex.re_sum]
      rfl
    have h2 : (A * res ω t).trace.re = ∑ i, ((cj hω A) i i).re * (eigV hω i + t)⁻¹ := by
      rw [trace_mul_res hω (le_of_lt ht), Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [h1, h2, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq,
    MeasureTheory.integral_finset_sum _
      (fun i _ => (integrableOn_logKernel (eigV_pos hω i)).const_mul _)]
  rw [trace_mul_logM hω, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_logKernel (eigV_pos hω i)]
  simp

theorem pathState_zero (ρ σ : Mat n) : pathState ρ σ 0 = σ := by
  simp [pathState]

theorem pathState_one (ρ σ : Mat n) : pathState ρ σ 1 = ρ := by
  simp [pathState]

theorem res_pathState_eq (ρ σ : Mat n) (s t : ℝ) :
    res (pathState ρ σ s) t = ((σ + (t : ℂ) • 1) + (s : ℂ) • (ρ - σ))⁻¹ := by
  rw [res, pathState]
  congr 1
  abel

/-- Joint continuity of the resolvent traces along the path. -/
theorem continuousAt_path_trace (hρ : ρ.PosDef) (hσ : σ.PosDef) (A B : Mat n) {p : ℝ × ℝ}
    (ht : 0 ≤ p.1) (h0 : 0 ≤ p.2) (h1 : p.2 ≤ 1) :
    ContinuousAt (fun q : ℝ × ℝ =>
      (A * res (pathState ρ σ q.2) q.1 * B * res (pathState ρ σ q.2) q.1).trace.re) p := by
  have hY : Continuous (fun q : ℝ × ℝ => pathState ρ σ q.2 + (q.1 : ℂ) • (1 : Mat n)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [pathState, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
      Matrix.one_apply]
    fun_prop
  have hpd : (pathState ρ σ p.2 + (p.1 : ℂ) • 1).PosDef :=
    posDef_shift (pathState_posDef hρ hσ h0 h1) ht
  have hdet : (pathState ρ σ p.2 + (p.1 : ℂ) • 1).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
    exact this.ne_zero
  have hinvAt : ContinuousAt Inv.inv (pathState ρ σ p.2 + (p.1 : ℂ) • 1) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hR : ContinuousAt (fun q : ℝ × ℝ => res (pathState ρ σ q.2) q.1) p := by
    have h := ContinuousAt.comp (g := fun X : Mat n => X⁻¹) (x := p) hinvAt hY.continuousAt
    simpa [Function.comp_def, res] using h
  have hM : ContinuousAt
      (fun q : ℝ × ℝ => A * res (pathState ρ σ q.2) q.1 * B * res (pathState ρ σ q.2) q.1) p :=
    ((continuousAt_const.mul hR).mul continuousAt_const).mul hR
  exact Complex.continuous_re.continuousAt.comp
    ((Continuous.matrix_trace continuous_id).continuousAt.comp hM)

theorem shift_pathState_eq (ρ σ : Mat n) (s t : ℝ) :
    (σ + (t : ℂ) • 1) + (s : ℂ) • (ρ - σ) = pathState ρ σ s + (t : ℂ) • 1 := by
  rw [pathState]
  abel

section Derivative

open scoped Matrix.Norms.Operator

/-- The trace, as a continuous linear functional on matrices. -/
noncomputable def traceCLM (n : ℕ) : Mat n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin n) ℂ ℂ)

theorem traceCLM_apply (A : Mat n) : traceCLM n A = A.trace := rfl

/-- The derivative of the inverse along an affine line of matrices. -/
theorem hasDerivAt_inv_affine (M D : Mat n) {s : ℝ} (h : IsUnit (M + (s : ℂ) • D)) :
    HasDerivAt (fun u : ℝ => (M + (u : ℂ) • D)⁻¹)
      (-((M + (s : ℂ) • D)⁻¹ * D * (M + (s : ℂ) • D)⁻¹)) s := by
  obtain ⟨u, hu⟩ := h
  have hfd : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℂ (Mat n) (↑u⁻¹ : Mat n) (↑u⁻¹ : Mat n)))
      (M + (s : ℂ) • D) := by
    rw [← hu]
    exact hasFDerivAt_ringInverse u
  have haff : HasDerivAt (fun v : ℝ => M + (v : ℂ) • D) D s := by
    have h1 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
    simpa using ((h1.smul_const D).const_add M)
  have hcomp := (hfd.restrictScalars ℝ).comp_hasDerivAt s haff
  have hinv : ∀ X : Mat n, Ring.inverse X = X⁻¹ := fun X =>
    (Matrix.nonsing_inv_eq_ringInverse X).symm
  simp only [Function.comp_def, hinv] at hcomp
  convert hcomp using 1
  have huinv : (↑u⁻¹ : Mat n) = (M + (s : ℂ) • D)⁻¹ := by
    rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, huinv]

/-- The derivative of the resolvent along the path. -/
theorem hasDerivAt_res_path (hρ : ρ.PosDef) (hσ : σ.PosDef) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u : ℝ => res (pathState ρ σ u) t)
      (-(res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t)) s := by
  have hunit : IsUnit ((σ + (t : ℂ) • 1) + (s : ℂ) • (ρ - σ)) := by
    rw [shift_pathState_eq]
    exact (posDef_shift (pathState_posDef hρ hσ h0 h1) ht).isUnit
  have := hasDerivAt_inv_affine (σ + (t : ℂ) • 1) (ρ - σ) hunit
  simpa only [← res_pathState_eq] using this

/-- The derivative of `s ↦ -Tr (A (ω s + t)⁻¹)` along the path. -/
theorem hasDerivAt_trace_res_path (hρ : ρ.PosDef) (hσ : σ.PosDef) {s : ℝ} (h0 : 0 ≤ s)
    (h1 : s ≤ 1) {t : ℝ} (ht : 0 ≤ t) (A : Mat n) :
    HasDerivAt (fun u : ℝ => -(A * res (pathState ρ σ u) t).trace.re)
      ((A * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re) s := by
  have hR := hasDerivAt_res_path hρ hσ h0 h1 ht
  have hAR := hR.const_mul A
  have h2 := (((traceCLM n).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt s hAR
  have h3 := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt s h2
  have h4 := h3.neg
  convert h4 using 1
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', traceCLM_apply,
    Complex.reCLM_apply, mul_neg, Matrix.trace_neg, Complex.neg_re, neg_neg, mul_assoc]

/-- The fundamental theorem of calculus along the path. -/
theorem integral_path_deriv (hρ : ρ.PosDef) (hσ : σ.PosDef) {t : ℝ} (ht : 0 ≤ t) (A : Mat n) :
    (∫ s in Ioo (0:ℝ) 1,
        (A * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re)
      = (A * res σ t).trace.re - (A * res ρ t).trace.re := by
  have hle : (0:ℝ) ≤ 1 := by norm_num
  have hderiv : ∀ s ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => -(A * res (pathState ρ σ u) t).trace.re)
        ((A * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re) s := by
    intro s hs
    rw [Set.uIcc_of_le hle] at hs
    exact hasDerivAt_trace_res_path hρ hσ hs.1 hs.2 ht A
  have hcont : ContinuousOn (fun s : ℝ =>
      (A * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re) (uIcc 0 1) := by
    rw [Set.uIcc_of_le hle]
    intro s hs
    have hAt := continuousAt_path_trace hρ hσ A (ρ - σ) (p := (t, s)) ht hs.1 hs.2
    exact (hAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo] at key
  rw [key, pathState_zero, pathState_one]
  ring

end Derivative

/-- The relative entropy as an integral of resolvent traces. -/
theorem relEntropy_eq_res_integral (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEntropy ρ σ = ∫ t in Ioi (0:ℝ), ((ρ * res σ t).trace.re - (ρ * res ρ t).trace.re) := by
  rw [relEntropy, trace_mul_logM_integral hρ ρ, trace_mul_logM_integral hσ ρ,
    ← MeasureTheory.integral_sub (integrableOn_logKernel_trace hρ ρ)
      (integrableOn_logKernel_trace hσ ρ)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  ring

/-- The inner integral over `t`, at a fixed point of the path. -/
theorem integral_res_quad_path (hρ : ρ.PosDef) (hσ : σ.PosDef) (htr : ρ.trace = σ.trace)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (∫ t in Ioi (0:ℝ),
        (ρ * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re)
      = (1 - s) * bkm (pathState ρ σ s) (ρ - σ) := by
  have hω : (pathState ρ σ s).PosDef := pathState_posDef hρ hσ h0 h1
  have hΔ : (ρ - σ).IsHermitian := hρ.isHermitian.sub hσ.isHermitian
  have hρeq : ρ = pathState ρ σ s + ((1 - s : ℝ) : ℂ) • (ρ - σ) := by
    rw [pathState]
    push_cast
    module
  have hsplit : ∀ t ∈ Ioi (0:ℝ),
      (ρ * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re
        = (pathState ρ σ s * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re
          + (1 - s) * ((ρ - σ) * res (pathState ρ σ s) t * (ρ - σ)
              * res (pathState ρ σ s) t).trace.re := by
    intro t _
    have hmat : ρ * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t
        = (pathState ρ σ s * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t)
          + ((1 - s : ℝ) : ℂ) • ((ρ - σ) * res (pathState ρ σ s) t * (ρ - σ)
              * res (pathState ρ σ s) t) := by
      conv_lhs => rw [hρeq]
      simp [Matrix.add_mul, Matrix.smul_mul]
    rw [hmat, Matrix.trace_add, Matrix.trace_smul, Complex.add_re, smul_eq_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hsplit,
    MeasureTheory.integral_add (integrableOn_omega_res_quad hω (ρ - σ))
      ((integrableOn_res_quad hω hΔ).const_mul _),
    integral_omega_res_quad hω, MeasureTheory.integral_const_mul]
  have htr0 : ((ρ - σ).trace).re = 0 := by
    rw [Matrix.trace_sub, htr]
    simp
  rw [htr0, zero_add, bkm]

/-- Joint integrability of the two-parameter family of resolvent traces. -/
theorem integrable_uncurry_path (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    Integrable (Function.uncurry fun (t s : ℝ) =>
        (ρ * res (pathState ρ σ s) t * (ρ - σ) * res (pathState ρ σ s) t).trace.re)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  classical
  obtain ⟨mr, hmr0, hmr⟩ := exists_pos_sub_posSemidef hρ
  obtain ⟨ms, hms0, hms⟩ := exists_pos_sub_posSemidef hσ
  set m : ℝ := min mr ms with hm
  have hm0 : 0 < m := lt_min hmr0 hms0
  have hmono : ∀ {A : Mat n} {m₀ : ℝ}, (A - ((m₀ : ℝ) : ℂ) • 1).PosSemidef → m ≤ m₀ →
      (A - ((m : ℝ) : ℂ) • 1).PosSemidef := by
    intro A m₀ hA hle
    have hid : A - ((m : ℝ) : ℂ) • 1
        = (A - ((m₀ : ℝ) : ℂ) • 1) + ((m₀ - m : ℝ) : ℂ) • (1 : Mat n) := by
      push_cast
      module
    rw [hid]
    refine hA.add (Matrix.PosSemidef.smul Matrix.PosSemidef.one ?_)
    have : (0:ℝ) ≤ m₀ - m := by linarith
    exact_mod_cast this
  have hρm : (ρ - ((m : ℝ) : ℂ) • 1).PosSemidef := hmono hmr (min_le_left _ _)
  have hσm : (σ - ((m : ℝ) : ℂ) • 1).PosSemidef := hmono hms (min_le_right _ _)
  have hpathm : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (pathState ρ σ s - ((m : ℝ) : ℂ) • 1).PosSemidef := by
    intro s h0 h1
    have hid : pathState ρ σ s - ((m : ℝ) : ℂ) • 1
        = ((1 - s : ℝ) : ℂ) • (σ - ((m : ℝ) : ℂ) • 1)
          + ((s : ℝ) : ℂ) • (ρ - ((m : ℝ) : ℂ) • 1) := by
      rw [pathState_eq]
      push_cast
      module
    rw [hid]
    refine (Matrix.PosSemidef.smul hσm ?_).add (Matrix.PosSemidef.smul hρm ?_)
    · have : (0:ℝ) ≤ 1 - s := by linarith
      exact_mod_cast this
    · exact_mod_cast h0
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1)) := ⟨by simp⟩
  set K : ℝ := (frobSq ρ + frobSq (ρ - σ)) / 2 with hK
  rw [MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.Integrable.mono'
    (g := fun p : ℝ × ℝ => K * ((m + p.1)⁻¹ * (m + p.1)⁻¹)) ?_ ?_ ?_
  · rw [← MeasureTheory.Measure.prod_restrict]
    exact ((integrableOn_resSq hm0).const_mul K).comp_fst _
  · refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    exact (continuousAt_path_trace hρ hσ ρ (ρ - σ) (le_of_lt hp.1) (le_of_lt hp.2.1)
      (le_of_lt hp.2.2)).continuousWithinAt
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have ht : (0:ℝ) ≤ p.1 := le_of_lt hp1
    have hs0 : (0:ℝ) ≤ p.2 := le_of_lt hp2.1
    have hs1 : p.2 ≤ 1 := le_of_lt hp2.2
    have hωp : (pathState ρ σ p.2).PosDef := pathState_posDef hρ hσ hs0 hs1
    have hmt : 0 < m + p.1 := by linarith
    have hbound := abs_trace_res_quad_le hωp
      (fun i => eigV_ge_of_sub_posSemidef hωp (hpathm p.2 hs0 hs1) i) ht hmt ρ (ρ - σ)
    simpa [Function.uncurry, Real.norm_eq_abs, hK] using hbound

/-- **The integral representation of the relative entropy.** -/
theorem relEntropy_eq_path (hρ : ρ.PosDef) (hσ : σ.PosDef) (htr : ρ.trace = σ.trace) :
    relEntropy ρ σ = ∫ s in Ioo (0:ℝ) 1, (1 - s) * bkm (pathState ρ σ s) (ρ - σ) := by
  rw [relEntropy_eq_res_integral hρ hσ,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => (integral_path_deriv hρ hσ (le_of_lt ht) ρ).symm),
    MeasureTheory.integral_integral_swap (integrable_uncurry_path hρ hσ)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  exact integral_res_quad_path hρ hσ htr (le_of_lt hs.1) (le_of_lt hs.2)

/-- Integrability along the path. -/
theorem integrableOn_path (hρ : ρ.PosDef) (hσ : σ.PosDef) (htr : ρ.trace = σ.trace) :
    IntegrableOn (fun s : ℝ => (1 - s) * bkm (pathState ρ σ s) (ρ - σ)) (Ioo 0 1) := by
  have h := (integrable_uncurry_path hρ hσ).integral_prod_right
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact integral_res_quad_path hρ hσ htr (le_of_lt hs.1) (le_of_lt hs.2)

end QI

import RequestProject.QI.Spectral

/-!
# Resolvents and traces in an eigenbasis
-/

open Matrix
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ω : Mat n}

/-- The resolvent `(ω + t)⁻¹` of a matrix. -/
noncomputable def res (ω : Mat n) (t : ℝ) : Mat n := (ω + (t : ℂ) • 1)⁻¹

/-- The unitary diagonalizing a positive definite matrix. -/
noncomputable def eigU (hω : ω.PosDef) : Mat n := hω.isHermitian.eigenvectorUnitary

/-- The eigenvalues of a positive definite matrix. -/
noncomputable def eigV (hω : ω.PosDef) : Fin n → ℝ := hω.isHermitian.eigenvalues

/-- Conjugation into the eigenbasis of `ω`. -/
noncomputable def cj (hω : ω.PosDef) (A : Mat n) : Mat n := star (eigU hω) * A * eigU hω

theorem eigU_mem (hω : ω.PosDef) : eigU hω ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  hω.isHermitian.eigenvectorUnitary.2

theorem eigV_pos (hω : ω.PosDef) (i : Fin n) : 0 < eigV hω i := hω.eigenvalues_pos i

theorem conj_eq_of_spectral (U A D : Mat n) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (h : A = U * D * star U) : star U * A * U = D := by
  subst h
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc star U * (U * D * star U) * U = (star U * U) * D * (star U * U) := by noncomm_ring
    _ = D := by rw [h1]; simp

theorem trace_cj (hω : ω.PosDef) (A : Mat n) : (cj hω A).trace = A.trace :=
  trace_conj _ _ (eigU_mem hω)

theorem cj_mul (hω : ω.PosDef) (A B : Mat n) : cj hω (A * B) = cj hω A * cj hω B :=
  conj_mul _ _ _ (eigU_mem hω)

theorem cj_isHermitian (hω : ω.PosDef) {A : Mat n} (hA : A.IsHermitian) :
    (cj hω A).IsHermitian := by
  have hA' : star A = A := hA
  have h : star (cj hω A) = cj hω A := by
    simp only [cj, Matrix.star_mul, star_star, hA', mul_assoc]
  exact h

theorem cj_conjTranspose (hω : ω.PosDef) (A : Mat n) : cj hω (Aᴴ) = (cj hω A)ᴴ := by
  simp [cj, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, mul_assoc]

/-- Conjugating a positive semidefinite matrix into the eigenbasis of `ω`. -/
theorem cj_posSemidef (hω : ω.PosDef) {F : Mat n} (hF : F.PosSemidef) :
    (cj hω F).PosSemidef := by
  simpa [cj, Matrix.star_eq_conjTranspose] using hF.conjTranspose_mul_mul_same (eigU hω)

/-- Conversely, a matrix whose conjugate into the eigenbasis of `ω` is positive semidefinite is
itself positive semidefinite. -/
theorem posSemidef_of_cj (hω : ω.PosDef) {F : Mat n} (hF : (cj hω F).PosSemidef) :
    F.PosSemidef := by
  have h1 : eigU hω * (cj hω F) * star (eigU hω) = F := by
    have hu : eigU hω * star (eigU hω) = 1 := Matrix.mem_unitaryGroup_iff.mp (eigU_mem hω)
    calc eigU hω * (star (eigU hω) * F * eigU hω) * star (eigU hω)
        = (eigU hω * star (eigU hω)) * F * (eigU hω * star (eigU hω)) := by noncomm_ring
      _ = F := by rw [hu]; simp
  rw [← h1]
  simpa [Matrix.star_eq_conjTranspose] using hF.mul_mul_conjTranspose_same (eigU hω)

theorem cj_self (hω : ω.PosDef) :
    cj hω ω = Matrix.diagonal (fun i => ((eigV hω i : ℝ) : ℂ)) := by
  refine conj_eq_of_spectral _ _ _ (eigU_mem hω) ?_
  conv_lhs => rw [hω.isHermitian.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Function.comp_def, eigU, eigV]

theorem cj_cfc (hω : ω.PosDef) (f : ℝ → ℝ) :
    cj hω (cfc f ω) = Matrix.diagonal (fun i => ((f (eigV hω i) : ℝ) : ℂ)) := by
  refine conj_eq_of_spectral _ _ _ (eigU_mem hω) ?_
  rw [hω.isHermitian.cfc_eq f]
  simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def, eigU, eigV]

theorem cj_logM (hω : ω.PosDef) :
    cj hω (logM ω) = Matrix.diagonal (fun i => ((Real.log (eigV hω i) : ℝ) : ℂ)) :=
  cj_cfc hω Real.log

/-- Shifting a positive definite matrix by a nonnegative multiple of the identity. -/
theorem posDef_shift (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) : (ω + (t : ℂ) • 1).PosDef := by
  rcases eq_or_lt_of_le ht with h | h
  · simpa [← h] using hω
  · exact hω.add (Matrix.PosDef.smul Matrix.PosDef.one (by exact_mod_cast h))

theorem cj_shift (hω : ω.PosDef) (t : ℝ) :
    cj hω (ω + (t : ℂ) • 1) = Matrix.diagonal (fun i => ((eigV hω i + t : ℝ) : ℂ)) := by
  have h1 : star (eigU hω) * (eigU hω) = 1 := Matrix.mem_unitaryGroup_iff'.mp (eigU_mem hω)
  have h2 : cj hω (ω + (t : ℂ) • 1)
      = cj hω ω + (t : ℂ) • (star (eigU hω) * eigU hω) := by
    simp [cj, Matrix.mul_add, Matrix.add_mul]
  rw [h2, h1, cj_self hω]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]

theorem cj_res (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    cj hω (res ω t) = Matrix.diagonal (fun i => (((eigV hω i + t)⁻¹ : ℝ) : ℂ)) := by
  have hpos : (ω + (t : ℂ) • 1).PosDef := posDef_shift hω ht
  rw [cj, res, conj_inv _ _ (eigU_mem hω) hpos.isUnit]
  rw [show star (eigU hω) * (ω + (t : ℂ) • 1) * eigU hω = cj hω (ω + (t:ℂ) • 1) from rfl,
    cj_shift hω t]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff.2 fun i => ?_).trans Matrix.diagonal_one
  have h0 : (eigV hω i + t) ≠ 0 := ne_of_gt (by linarith [eigV_pos hω i])
  have h1 : ((eigV hω i + t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
  push_cast at h1 ⊢
  field_simp

/-- The trace of a product, entrywise. -/
theorem trace_mul_eq_sum (A B : Mat n) : (A * B).trace = ∑ i, ∑ j, A i j * B j i := by
  simp [Matrix.trace, Matrix.mul_apply]

/-- Trace of `A * f(ω)` in the eigenbasis of `ω`. -/
theorem trace_mul_cfc (hω : ω.PosDef) (f : ℝ → ℝ) (A : Mat n) :
    (A * cfc f ω).trace = ∑ i, (cj hω A) i i * ((f (eigV hω i) : ℝ) : ℂ) := by
  rw [← trace_cj hω (A * cfc f ω), cj_mul, cj_cfc hω f, trace_mul_diagonal]

theorem trace_mul_res (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) (A : Mat n) :
    (A * res ω t).trace = ∑ i, (cj hω A) i i * (((eigV hω i + t)⁻¹ : ℝ) : ℂ) := by
  rw [← trace_cj hω (A * res ω t), cj_mul, cj_res hω ht, trace_mul_diagonal]

theorem trace_mul_logM (hω : ω.PosDef) (A : Mat n) :
    (A * logM ω).trace = ∑ i, (cj hω A) i i * ((Real.log (eigV hω i) : ℝ) : ℂ) :=
  trace_mul_cfc hω Real.log A

/-- Trace of `Δ R Δ R` in the eigenbasis of `ω`, where `R` is the resolvent. -/
theorem trace_res_quad (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) (Δ B : Mat n) :
    (Δ * res ω t * B * res ω t).trace
      = ∑ i, ∑ j, (cj hω Δ) i j * (((eigV hω j + t)⁻¹ : ℝ) : ℂ) *
          (cj hω B) j i * (((eigV hω i + t)⁻¹ : ℝ) : ℂ) := by
  rw [← trace_cj hω _, cj_mul, cj_mul, cj_mul, cj_res hω ht, trace_diag_mul_diag]

end QI

