import RequestProject.CLT

/-!
# Convergence of the rescaled walk against smooth test functions

`Math2.walkLaw μ n t` is the law of `S_{⌊n t⌋} / √n`, where `S` is a random walk with step
distribution `μ`.  Here we prove that, for a centered step distribution with unit variance and
finite third absolute moment, the integrals of smooth test functions against `walkLaw μ n t`
converge to the corresponding integrals against the centered Gaussian law of variance `t`, which
is the law of Brownian motion at time `t`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The law of `S_p / √n`, the sum of `p` i.i.d. steps with law `μ`, rescaled by `1/√n`. -/
noncomputable def scaledLaw (μ : Measure ℝ) (p n : ℕ) : Measure ℝ :=
  (convPow μ p).map (fun x => (Real.sqrt n)⁻¹ * x)

instance isProbabilityMeasure_scaledLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (p n : ℕ) :
    IsProbabilityMeasure (scaledLaw μ p n) := by
  rw [scaledLaw]; infer_instance

/-- The law of the rescaled random walk `S_{⌊n t⌋} / √n` with step distribution `μ`. -/
noncomputable def walkLaw (μ : Measure ℝ) (n : ℕ) (t : ℝ) : Measure ℝ :=
  scaledLaw μ ⌊(n : ℝ) * t⌋₊ n

instance isProbabilityMeasure_walkLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) :
    IsProbabilityMeasure (walkLaw μ n t) := by
  rw [walkLaw]; infer_instance

theorem walkLaw_eq_scaledLaw (μ : Measure ℝ) (n : ℕ) (t : ℝ) :
    walkLaw μ n t = scaledLaw μ ⌊(n : ℝ) * t⌋₊ n := rfl

/-- Weak continuity of the centered Gaussian family in its variance, tested against bounded
continuous functions. -/
theorem tendsto_integral_gaussianReal_of_tendsto {g : ℝ → ℝ} {M : ℝ} (hg : Continuous g)
    (hgb : ∀ x, |g x| ≤ M) {v : ℕ → ℝ≥0} {w : ℝ≥0} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => ∫ x, g x ∂(gaussianReal 0 (v n))) atTop
      (𝓝 (∫ x, g x ∂(gaussianReal 0 w))) := by
  have key : ∀ u : ℝ≥0, ∫ x, g x ∂(gaussianReal 0 u)
      = ∫ x, g (Real.sqrt u * x) ∂(gaussianReal 0 1) := by
    intro u
    have hsq : (⟨(Real.sqrt u) ^ 2, sq_nonneg _⟩ : ℝ≥0) = u := by
      ext
      simp [Real.sq_sqrt u.coe_nonneg]
    calc ∫ x, g x ∂(gaussianReal 0 u)
        = ∫ x, g x ∂(gaussianReal 0 (⟨(Real.sqrt u) ^ 2, sq_nonneg _⟩ : ℝ≥0)) := by rw [hsq]
      _ = ∫ x, g (Real.sqrt u * x) ∂(gaussianReal 0 1) := by
          rw [gaussianReal_eq_map (Real.sqrt u), integral_map_const_mul _ _ hg]
  simp only [key]
  have hvr : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (w : ℝ)) := by
    exact (NNReal.tendsto_coe.2 hv)
  refine tendsto_integral_of_dominated_convergence (fun _ => M) ?_ (integrable_const M) ?_ ?_
  · intro n
    exact (hg.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · intro n
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hgb _
  · filter_upwards with x
    have : Tendsto (fun n => Real.sqrt (v n) * x) atTop (𝓝 (Real.sqrt w * x)) :=
      ((Real.continuous_sqrt.tendsto _).comp hvr).mul tendsto_const_nhds
    exact (hg.tendsto _).comp this

theorem tendsto_floor_div (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) * t⌋₊ : ℝ) / n) atTop (𝓝 t) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hl : Tendsto (fun n : ℕ => t - 1 / n) atTop (𝓝 t) := by
    have := (tendsto_const_nhds (x := t) (f := atTop (α := ℕ))).sub h0
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h2 : (n : ℝ) * t - 1 < (⌊(n : ℝ) * t⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one ((n : ℝ) * t); linarith
    rw [le_div_iff₀ hn0]
    have hinv : (1 / (n : ℝ)) * n = 1 := by field_simp
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (⌊(n : ℝ) * t⌋₊ : ℝ) ≤ (n : ℝ) * t := Nat.floor_le (by positivity)
    rw [div_le_iff₀ hn0]
    linarith

/-- The main convergence statement for smooth test functions: if the number of steps `m n`
satisfies `m n / n → v`, then the law of `S_{m n} / √n` converges to the centered Gaussian of
variance `v`. -/
theorem tendsto_integral_scaledLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    {f f1 f2 f3 : ℝ → ℝ} {M : ℝ} (h : IsC3Test f f1 f2 f3 M) {m : ℕ → ℕ} {v : ℝ}
    (hm : Tendsto (fun n : ℕ => (m n : ℝ) / n) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ => ∫ x, f x ∂(scaledLaw μ (m n) n)) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 v.toNNReal))) := by
  have hvnn : 0 ≤ v := by
    refine ge_of_tendsto hm ?_
    filter_upwards with n using by positivity
  set K : ℝ := M * ((∫ x, |x| ^ 3 ∂μ) + gaussThirdMoment) with hK
  have hKnn : 0 ≤ K := by
    have h1 : 0 ≤ ∫ x, |x| ^ 3 ∂μ := integral_nonneg fun x => by positivity
    have h2 : 0 ≤ gaussThirdMoment := integral_nonneg fun x => by positivity
    have := h.nonneg
    rw [hK]; positivity
  set w : ℕ → ℝ≥0 := fun n =>
    (m n : ℕ) • (⟨((Real.sqrt n)⁻¹) ^ 2, sq_nonneg _⟩ : ℝ≥0) with hw
  -- Step 1 : the Lindeberg estimate tends to zero
  have hdiff : Tendsto
      (fun n : ℕ => (∫ x, f x ∂(scaledLaw μ (m n) n)) - ∫ x, f x ∂(gaussianReal 0 (w n)))
      atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hzero : Tendsto (fun n : ℕ => (m n : ℝ) / n * K / Real.sqrt n) atTop (𝓝 0) :=
      Tendsto.div_atTop (hm.mul_const K) hsqrt
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    have hbound := walk_gaussian_bound hmean hvar h3 h (Real.sqrt n)⁻¹ (m n)
    rw [← scaledLaw] at hbound
    have habs : |((Real.sqrt n)⁻¹)| ^ 3 = 1 / ((n : ℝ) * Real.sqrt n) := by
      rw [abs_of_pos (inv_pos.2 hsn), inv_pow, one_div]
      congr 1
      have h3' : Real.sqrt n ^ 3 = Real.sqrt n ^ 2 * Real.sqrt n := by ring
      rw [h3', Real.sq_sqrt hn0.le]
    have heq : (m n : ℝ) * (K * (1 / ((n : ℝ) * Real.sqrt n)))
        = (m n : ℝ) / n * K / Real.sqrt n := by
      field_simp
    calc ‖(∫ x, f x ∂(scaledLaw μ (m n) n)) - ∫ x, f x ∂(gaussianReal 0 (w n))‖
        = |(∫ x, f x ∂(scaledLaw μ (m n) n)) - ∫ x, f x ∂(gaussianReal 0 (w n))| := by
          rw [Real.norm_eq_abs]
      _ ≤ (m n : ℝ) * (M * (|((Real.sqrt n)⁻¹)| ^ 3
            * ((∫ x, |x| ^ 3 ∂μ) + gaussThirdMoment))) := hbound
      _ = (m n : ℝ) * (K * (1 / ((n : ℝ) * Real.sqrt n))) := by
          rw [habs, hK]; ring
      _ = (m n : ℝ) / n * K / Real.sqrt n := heq
  -- Step 2 : the Gaussian laws converge
  have hwlim : Tendsto w atTop (𝓝 v.toNNReal) := by
    rw [← NNReal.tendsto_coe]
    have hcoe : ∀ n : ℕ, 0 < n → ((w n : ℝ≥0) : ℝ) = (m n : ℝ) / n := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : ((w n : ℝ≥0) : ℝ) = (m n : ℝ) * ((Real.sqrt n)⁻¹) ^ 2 := by
        rw [hw]
        push_cast [nsmul_eq_mul]
        rfl
      rw [h1, inv_pow, Real.sq_sqrt hn0.le]
      field_simp
    rw [Real.coe_toNNReal v hvnn]
    refine hm.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hcoe n hn]
  have hgauss : Tendsto (fun n : ℕ => ∫ x, f x ∂(gaussianReal 0 (w n))) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 v.toNNReal))) :=
    tendsto_integral_gaussianReal_of_tendsto h.continuous h.bound0 hwlim
  have := hdiff.add hgauss
  simpa using this

/-- The convergence statement for smooth test functions at a fixed time `t ≥ 0`: the rescaled
walk at time `t` converges to the centered Gaussian of variance `t`. -/
theorem tendsto_integral_walkLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    {f f1 f2 f3 : ℝ → ℝ} {M : ℝ} (h : IsC3Test f f1 f2 f3 M) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => ∫ x, f x ∂(walkLaw μ n t)) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 t.toNNReal))) :=
  tendsto_integral_scaledLaw hmean hvar h3 h (m := fun n => ⌊(n : ℝ) * t⌋₊)
    (tendsto_floor_div t ht)

end Math2

import RequestProject.Lindeberg

/-!
# A quantitative central limit theorem

Combining the Lindeberg swapping estimate with the scaling properties of convolution powers we
obtain: if `μ` is centered with unit variance and finite third absolute moment, then the law of
the rescaled sum of `m` independent `μ`-distributed steps is close, when tested against smooth
functions, to a centered Gaussian with variance `m * c ^ 2` (here `c` is the scaling factor,
which will be `1 / √n`).
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

section Scaling

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ}

theorem integral_map_const_mul (μ : Measure ℝ) (c : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ x, g x ∂(μ.map (fun x => c * x)) = ∫ x, g (c * x) ∂μ :=
  integral_map (measurable_const_mul c).aemeasurable hg.aestronglyMeasurable

theorem integral_id_map_const_mul (μ : Measure ℝ) (c : ℝ) :
    ∫ x, x ∂(μ.map (fun x => c * x)) = c * ∫ x, x ∂μ := by
  rw [integral_map_const_mul μ c (g := fun x => x) continuous_id, integral_const_mul]

theorem integral_sq_map_const_mul (μ : Measure ℝ) (c : ℝ) :
    ∫ x, x ^ 2 ∂(μ.map (fun x => c * x)) = c ^ 2 * ∫ x, x ^ 2 ∂μ := by
  rw [integral_map_const_mul μ c (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]

theorem integral_abs_cube_map_const_mul (μ : Measure ℝ) (c : ℝ) :
    ∫ x, |x| ^ 3 ∂(μ.map (fun x => c * x)) = |c| ^ 3 * ∫ x, |x| ^ 3 ∂μ := by
  rw [integral_map_const_mul μ c (by fun_prop)]
  simp_rw [abs_mul, mul_pow]
  rw [integral_const_mul]

theorem integrable_abs_cube_map_const_mul (μ : Measure ℝ) (c : ℝ)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable (fun x : ℝ => |x| ^ 3) (μ.map (fun x => c * x)) := by
  rw [integrable_map_measure (by fun_prop) (measurable_const_mul c).aemeasurable]
  simp only [Function.comp_def, abs_mul, mul_pow]
  exact h3.const_mul _

instance isProbabilityMeasure_map_const_mul (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    IsProbabilityMeasure (μ.map (fun x => c * x)) :=
  Measure.isProbabilityMeasure_map (measurable_const_mul c).aemeasurable

end Scaling

section Gaussian

/-- The third absolute moment of a standard Gaussian. -/
noncomputable def gaussThirdMoment : ℝ := ∫ x, |x| ^ 3 ∂(gaussianReal 0 1)

theorem integral_sq_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_sub (X := fun x : ℝ => x) (μ := gaussianReal 0 v)
    (by simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 2))] at h
  simpa [integral_id_gaussianReal] using h

theorem integrable_abs_cube_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => |x| ^ 3) (gaussianReal 0 v) := by
  have h2 : MemLp (fun x : ℝ => x) 3 (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 3)
  have h3 := h2.integrable_norm_rpow (by norm_num) (by norm_num)
  simp only [Real.norm_eq_abs] at h3
  have heq : (fun x : ℝ => |x| ^ (3 : ℝ≥0∞).toReal) = fun x : ℝ => |x| ^ (3 : ℕ) := by
    funext x
    rw [show ((3 : ℝ≥0∞).toReal) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [heq] at h3
  exact h3

theorem gaussianReal_eq_map (c : ℝ) :
    gaussianReal 0 (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) = (gaussianReal 0 1).map (fun x => c * x) := by
  rw [gaussianReal_map_const_mul c]
  simp

theorem integral_abs_cube_gaussianReal_sq (c : ℝ) :
    ∫ x, |x| ^ 3 ∂(gaussianReal 0 (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0)) = |c| ^ 3 * gaussThirdMoment := by
  rw [gaussianReal_eq_map c, integral_abs_cube_map_const_mul, gaussThirdMoment]

end Gaussian

/-- **Quantitative CLT.** If `μ` is a centered probability measure on `ℝ` with unit variance and
finite third absolute moment, then the law of `c * (X₁ + ⋯ + X_m)` (`Xᵢ` iid with law `μ`) is
close to the centered Gaussian of variance `m * c ^ 2` when tested against a smooth test
function. -/
theorem walk_gaussian_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    {f f1 f2 f3 : ℝ → ℝ} {M : ℝ} (h : IsC3Test f f1 f2 f3 M) (c : ℝ) (m : ℕ) :
    |(∫ x, f x ∂((convPow μ m).map (fun x => c * x)))
        - ∫ x, f x ∂(gaussianReal 0 (m • (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0)))|
      ≤ m * (M * (|c| ^ 3 * ((∫ x, |x| ^ 3 ∂μ) + gaussThirdMoment))) := by
  set P : Measure ℝ := μ.map (fun x => c * x) with hP
  set Q : Measure ℝ := gaussianReal 0 (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) with hQ
  have hP1 : ∫ x, x ∂P = 0 := by rw [hP, integral_id_map_const_mul, hmean, mul_zero]
  have hQ1 : ∫ x, x ∂Q = 0 := integral_id_gaussianReal
  have hPQ2 : ∫ x, x ^ 2 ∂P = ∫ x, x ^ 2 ∂Q := by
    rw [hP, hQ, integral_sq_map_const_mul, hvar, integral_sq_gaussianReal]
    simp
  have hP3 : Integrable (fun x : ℝ => |x| ^ 3) P := integrable_abs_cube_map_const_mul μ c h3
  have hQ3 : Integrable (fun x : ℝ => |x| ^ 3) Q := integrable_abs_cube_gaussianReal _
  have hPpow : convPow P m = (convPow μ m).map (fun x => c * x) := by
    have := map_convPow (AddMonoidHom.mulLeft c) (measurable_const_mul c) μ m
    simpa [hP] using this.symm
  have hQpow : convPow Q m = gaussianReal 0 (m • (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0)) := by
    rw [hQ, convPow_gaussianReal]
  have key := h.convPow_swap_bound hP1 hQ1 hPQ2 hP3 hQ3 m (Measure.dirac 0)
  rw [Measure.dirac_zero_conv, Measure.dirac_zero_conv, hPpow, hQpow] at key
  refine key.trans ?_
  have hm3P : ∫ x, |x| ^ 3 ∂P = |c| ^ 3 * ∫ x, |x| ^ 3 ∂μ := integral_abs_cube_map_const_mul μ c
  have hm3Q : ∫ x, |x| ^ 3 ∂Q = |c| ^ 3 * gaussThirdMoment := integral_abs_cube_gaussianReal_sq c
  rw [hm3P, hm3Q]
  apply le_of_eq
  ring

end Math2

import RequestProject.Limit
import RequestProject.SmoothStep

/-!
# From smooth test functions to convergence in distribution

Using the smooth step functions of `SmoothStep.lean` we upgrade the convergence of integrals of
smooth test functions to the convergence of the distribution functions, and then to convergence
in distribution (weak convergence of the laws).
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction

section CDF

/-- A finite measure without atoms puts small mass on small windows. -/
theorem exists_small_window (γ : Measure ℝ) [IsProbabilityMeasure γ] [NoAtoms γ] (x : ℝ)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, γ.real (Ioc (x - δ) (x + δ)) ≤ ε := by
  have hanti : Antitone (fun k : ℕ => Ioc (x - 1 / ((k : ℝ) + 1)) (x + 1 / ((k : ℝ) + 1))) := by
    intro a b hab
    have hle : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (a : ℝ) ≤ b := by exact_mod_cast hab
        linarith
    exact Ioc_subset_Ioc (by linarith) (by linarith)
  have hinter : (⋂ k : ℕ, Ioc (x - 1 / ((k : ℝ) + 1)) (x + 1 / ((k : ℝ) + 1))) = {x} := by
    ext y
    simp only [mem_iInter, mem_Ioc, mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < x - y by linarith)
        have := (h k).1
        linarith
      · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < y - x by linarith)
        have := (h k).2
        linarith
    · rintro rfl
      intro k
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      constructor <;> linarith
  have h := tendsto_measure_iInter_atTop (μ := γ)
    (s := fun k : ℕ => Ioc (x - 1 / ((k : ℝ) + 1)) (x + 1 / ((k : ℝ) + 1)))
    (fun k => measurableSet_Ioc.nullMeasurableSet) hanti ⟨0, by simp⟩
  rw [hinter] at h
  simp only [measure_singleton] at h
  have hev : ∀ᶠ k : ℕ in atTop, γ (Ioc (x - 1 / ((k : ℝ) + 1)) (x + 1 / ((k : ℝ) + 1)))
      < ENNReal.ofReal ε := by
    have : (0 : ℝ≥0∞) < ENNReal.ofReal ε := by simpa using hε
    exact h.eventually (eventually_lt_nhds this)
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal hε.le hk.le

/-- Continuity of the distribution function of an atomless probability measure, in the form
needed below. -/
theorem exists_delta_cdf (γ : Measure ℝ) [IsProbabilityMeasure γ] [NoAtoms γ] (x : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, γ.real (Iic (x + δ)) ≤ γ.real (Iic x) + ε ∧
      γ.real (Iic x) - ε ≤ γ.real (Iic (x - δ)) := by
  obtain ⟨δ, hδ, hwin⟩ := exists_small_window γ x hε
  have hd1 : γ.real (Iic (x + δ)) = γ.real (Iic x) + γ.real (Ioc x (x + δ)) := by
    rw [← measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic (by linarith)]
  have hd2 : γ.real (Iic x) = γ.real (Iic (x - δ)) + γ.real (Ioc (x - δ) x) := by
    rw [← measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic (by linarith)]
  have hsub1 : γ.real (Ioc x (x + δ)) ≤ γ.real (Ioc (x - δ) (x + δ)) :=
    measureReal_mono (Ioc_subset_Ioc (by linarith) le_rfl)
  have hsub2 : γ.real (Ioc (x - δ) x) ≤ γ.real (Ioc (x - δ) (x + δ)) :=
    measureReal_mono (Ioc_subset_Ioc le_rfl (by linarith))
  exact ⟨δ, hδ, by linarith, by linarith⟩

end CDF

section Sandwich

variable {f f1 f2 f3 : ℝ → ℝ} {M x : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- The measure of `Iic x` is at most the integral of a nonnegative test function which is `1`
on `Iic x`. -/
theorem measureReal_Iic_le_integral (h : IsC3Test f f1 f2 f3 M) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y ≤ x, f y = 1) : ν.real (Iic x) ≤ ∫ y, f y ∂ν := by
  have hind : Integrable ((Iic x).indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_indicator_iff measurableSet_Iic).2 (by simp)
  have hle : ∀ y, (Iic x).indicator (fun _ => (1 : ℝ)) y ≤ f y := by
    intro y
    by_cases hy : y ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy), hf1 y hy]
    · rw [Set.indicator_of_notMem (by simpa using hy)]
      exact hf0 y
  have := integral_mono hind (h.integrable ν) hle
  rwa [show ((Iic x).indicator (fun _ => (1 : ℝ))) = (Iic x).indicator 1 from rfl,
    integral_indicator_one measurableSet_Iic] at this

/-- The integral of a test function bounded by `1` and vanishing on `Ici x` is at most the
measure of `Iic x`. -/
theorem integral_le_measureReal_Iic (h : IsC3Test f f1 f2 f3 M) (hf1 : ∀ y, f y ≤ 1)
    (hf0 : ∀ y, x ≤ y → f y = 0) : (∫ y, f y ∂ν) ≤ ν.real (Iic x) := by
  have hind : Integrable ((Iic x).indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_indicator_iff measurableSet_Iic).2 (by simp)
  have hle : ∀ y, f y ≤ (Iic x).indicator (fun _ => (1 : ℝ)) y := by
    intro y
    by_cases hy : y ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy)]
      exact hf1 y
    · rw [Set.indicator_of_notMem (by simpa using hy), hf0 y (le_of_lt (by simpa using hy))]
  have := integral_mono (h.integrable ν) hind hle
  rwa [show ((Iic x).indicator (fun _ => (1 : ℝ))) = (Iic x).indicator 1 from rfl,
    integral_indicator_one measurableSet_Iic] at this

end Sandwich

/-- The distribution function of a centered Gaussian is continuous at `x`, provided the variance
is positive or `x` is not the atom `0` of the degenerate Gaussian. -/
theorem exists_delta_cdf_gaussianReal (v : ℝ≥0) (x : ℝ) (hx : v ≠ 0 ∨ x ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, (gaussianReal 0 v).real (Iic (x + δ)) ≤ (gaussianReal 0 v).real (Iic x) + ε ∧
      (gaussianReal 0 v).real (Iic x) - ε ≤ (gaussianReal 0 v).real (Iic (x - δ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · have hx0 : x ≠ 0 := hx.resolve_left (by simp)
    have hdir : ∀ y : ℝ,
        (Measure.dirac (0 : ℝ)).real (Iic y) = if (0 : ℝ) ≤ y then 1 else 0 := by
      intro y
      rw [Measure.real, Measure.dirac_apply' _ measurableSet_Iic]
      by_cases hy : (0 : ℝ) ≤ y
      · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy)]; simp [hy]
      · rw [Set.indicator_of_notMem (by simpa using hy)]; simp [hy]
    simp only [gaussianReal_zero_var, hdir]
    refine ⟨|x| / 2, by positivity, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · rw [abs_of_neg hneg]; split_ifs <;> linarith
      · rw [abs_of_pos hpos]; split_ifs <;> linarith
    · rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · rw [abs_of_neg hneg]; split_ifs <;> linarith
      · rw [abs_of_pos hpos]; split_ifs <;> linarith
  · have : NoAtoms (gaussianReal 0 v) := noAtoms_gaussianReal hv
    exact exists_delta_cdf _ x hε

/-- **Convergence of the distribution functions.**  If the number of steps satisfies
`m n / n → v`, the distribution function of `S_{m n} / √n` converges to that of the centered
Gaussian of variance `v` at every point `x` of continuity of the latter. -/
theorem tendsto_scaledLaw_measureReal_Iic {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {m : ℕ → ℕ} {v : ℝ}
    (hm : Tendsto (fun n : ℕ => (m n : ℝ) / n) atTop (𝓝 v)) (x : ℝ)
    (hx : v.toNNReal ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun n : ℕ => (scaledLaw μ (m n) n).real (Iic x)) atTop
      (𝓝 ((gaussianReal 0 v.toNNReal).real (Iic x))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hup, hlow⟩ :=
    exists_delta_cdf_gaussianReal v.toNNReal x hx (ε := ε / 3) (by linarith)
  obtain ⟨f, f1, f2, f3, M, hf, hf0, hf1, hfone, hfzero⟩ := exists_smooth_step x δ hδ
  obtain ⟨g, g1, g2, g3, N, hg, hg0, hg1, hgone, hgzero⟩ := exists_smooth_step (x - δ) δ hδ
  have hfconv := tendsto_integral_scaledLaw hmean hvar h3 hf hm
  have hgconv := tendsto_integral_scaledLaw hmean hvar h3 hg hm
  rw [Metric.tendsto_atTop] at hfconv hgconv
  obtain ⟨N₁, hN₁⟩ := hfconv (ε / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hgconv (ε / 3) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hfn := hN₁ n hn₁
  have hgn := hN₂ n hn₂
  rw [Real.dist_eq] at hfn hgn ⊢
  have hupper : (scaledLaw μ (m n) n).real (Iic x) ≤
      (gaussianReal 0 v.toNNReal).real (Iic x) + 2 * (ε / 3) := by
    have h1 : (scaledLaw μ (m n) n).real (Iic x) ≤ ∫ y, f y ∂(scaledLaw μ (m n) n) :=
      measureReal_Iic_le_integral hf hf0 (fun y hy => hfone y hy)
    have h2 : (∫ y, f y ∂(gaussianReal 0 v.toNNReal))
        ≤ (gaussianReal 0 v.toNNReal).real (Iic (x + δ)) :=
      integral_le_measureReal_Iic hf hf1 (fun y hy => hfzero y hy)
    have h3' : (∫ y, f y ∂(scaledLaw μ (m n) n))
        ≤ (∫ y, f y ∂(gaussianReal 0 v.toNNReal)) + ε / 3 := by
      have := abs_lt.1 hfn
      linarith [this.2]
    linarith
  have hlower : (gaussianReal 0 v.toNNReal).real (Iic x) - 2 * (ε / 3) ≤
      (scaledLaw μ (m n) n).real (Iic x) := by
    have h1 : (∫ y, g y ∂(scaledLaw μ (m n) n)) ≤ (scaledLaw μ (m n) n).real (Iic x) := by
      refine integral_le_measureReal_Iic hg hg1 (fun y hy => hgzero y ?_)
      linarith
    have h2 : (gaussianReal 0 v.toNNReal).real (Iic (x - δ))
        ≤ ∫ y, g y ∂(gaussianReal 0 v.toNNReal) :=
      measureReal_Iic_le_integral hg hg0 (fun y hy => hgone y hy)
    have h3' : (∫ y, g y ∂(gaussianReal 0 v.toNNReal)) - ε / 3
        ≤ ∫ y, g y ∂(scaledLaw μ (m n) n) := by
      have := abs_lt.1 hgn
      linarith [this.1]
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- **Convergence of the distribution functions of the rescaled walk**, for every time `t ≥ 0`. -/
theorem tendsto_walkLaw_measureReal_Iic' {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    Tendsto (fun n : ℕ => (walkLaw μ n t).real (Iic x)) atTop
      (𝓝 ((gaussianReal 0 t.toNNReal).real (Iic x))) := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · have hzero : ∀ n : ℕ, walkLaw μ n 0 = gaussianReal 0 (0 : ℝ).toNNReal := by
      intro n
      have hc : ((n : ℝ) * 0) = 0 := by ring
      rw [walkLaw, hc]
      simp [scaledLaw, Measure.map_dirac (measurable_const_mul ((Real.sqrt n)⁻¹))]
    simp only [hzero]
    exact tendsto_const_nhds
  · have hne : t.toNNReal ≠ 0 := by simpa using ht'
    exact tendsto_scaledLaw_measureReal_Iic hmean hvar h3
      (m := fun n => ⌊(n : ℝ) * t⌋₊) (tendsto_floor_div t ht) x (Or.inl hne)

private theorem measureReal_Ioc_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] {a b : ℝ}
    (hab : a ≤ b) : ν.real (Ioc a b) = ν.real (Iic b) - ν.real (Iic a) := by
  have : ν.real (Iic b) = ν.real (Iic a) + ν.real (Ioc a b) := by
    rw [← measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hab]
  linarith

/-- The law of `S_p / √n`, as a probability measure. -/
noncomputable def scaledProb (μ : Measure ℝ) [IsProbabilityMeasure μ] (p n : ℕ) :
    ProbabilityMeasure ℝ := ⟨scaledLaw μ p n, isProbabilityMeasure_scaledLaw μ p n⟩

/-- The law of the rescaled random walk `S_{⌊n t⌋} / √n`, as a probability measure. -/
noncomputable def walkProb (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) :
    ProbabilityMeasure ℝ := ⟨walkLaw μ n t, isProbabilityMeasure_walkLaw μ n t⟩

/-- The law of Brownian motion at time `t`: the centered Gaussian with variance `t`. -/
noncomputable def brownianProb (t : ℝ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 t.toNNReal, inferInstance⟩

@[simp] theorem scaledProb_toMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] (p n : ℕ) :
    (scaledProb μ p n : Measure ℝ) = scaledLaw μ p n := rfl

@[simp] theorem walkProb_toMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) :
    (walkProb μ n t : Measure ℝ) = walkLaw μ n t := rfl

@[simp] theorem brownianProb_toMeasure (t : ℝ) :
    (brownianProb t : Measure ℝ) = gaussianReal 0 t.toNNReal := rfl

/-- **Convergence in distribution of the rescaled sums.**  If `m n / n → v` then the law of
`S_{m n} / √n` converges weakly to the centered Gaussian of variance `v`. -/
theorem tendsto_scaledProb {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {m : ℕ → ℕ} {v : ℝ}
    (hm : Tendsto (fun n : ℕ => (m n : ℝ) / n) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ => scaledProb μ (m n) n) atTop (𝓝 (brownianProb v)) := by
  set S : Set (Set ℝ) := {s | ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ s = Ioc a b} with hS
  have hpi : IsPiSystem S := by
    rintro s ⟨a, b, ha, hb, rfl⟩ u ⟨c, d, hc, hd, rfl⟩ -
    refine ⟨max a c, min b d, ?_, ?_, by rw [Set.Ioc_inter_Ioc]⟩
    · rcases max_choice a c with h | h <;> rw [h] <;> assumption
    · rcases min_choice b d with h | h <;> rw [h] <;> assumption
  have hmeas : ∀ s ∈ S, MeasurableSet s := by
    rintro s ⟨a, b, -, -, rfl⟩
    exact measurableSet_Ioc
  have hnhds : ∀ (u : Set ℝ), IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u := by
    intro u hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu x hx
    set r : ℝ := if x = 0 then ε / 2 else min (ε / 2) (|x| / 2) with hr
    have hr0 : 0 < r := by
      rw [hr]
      split_ifs with hx0
      · linarith
      · have : (0 : ℝ) < |x| := abs_pos.2 hx0
        positivity
    have hrε : r ≤ ε / 2 := by
      rw [hr]; split_ifs
      · exact le_rfl
      · exact min_le_left _ _
    have hne : x - r ≠ 0 ∧ x + r ≠ 0 := by
      rcases eq_or_ne x 0 with rfl | hx0
      · constructor
        · simp only [zero_sub, ne_eq, neg_eq_zero]; exact hr0.ne'
        · simpa using hr0.ne'
      · have hrx : r ≤ |x| / 2 := by
          rw [hr, if_neg hx0]; exact min_le_right _ _
        have hxa : 0 < |x| := abs_pos.2 hx0
        rcases lt_or_gt_of_ne hx0 with hneg | hpos
        · rw [abs_of_neg hneg] at hrx
          constructor <;> intro hc <;> linarith
        · rw [abs_of_pos hpos] at hrx
          constructor <;> intro hc <;> linarith
    refine ⟨Ioc (x - r) (x + r), ⟨_, _, hne.1, hne.2, rfl⟩, ?_, ?_⟩
    · exact Ioc_mem_nhds (by linarith) (by linarith)
    · intro y hy
      refine hball ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have := hy.1; linarith
      · have := hy.2; linarith
  refine hpi.tendsto_probabilityMeasure_of_tendsto_of_mem hmeas hnhds ?_
  rintro s ⟨a, b, ha, hb, rfl⟩
  rw [← NNReal.tendsto_coe]
  have hcoe : ∀ ν : ProbabilityMeasure ℝ, ((ν (Ioc a b) : ℝ≥0) : ℝ)
      = (ν : Measure ℝ).real (Ioc a b) := fun ν =>
    (ProbabilityMeasure.measureReal_eq_coe_coeFn ν (Ioc a b)).symm
  simp only [hcoe, scaledProb_toMeasure, brownianProb_toMeasure]
  rcases le_or_gt a b with hab | hab
  · simp only [measureReal_Ioc_eq _ hab]
    exact (tendsto_scaledLaw_measureReal_Iic hmean hvar h3 hm b (Or.inr hb)).sub
      (tendsto_scaledLaw_measureReal_Iic hmean hvar h3 hm a (Or.inr ha))
  · have hempty : Ioc a b = (∅ : Set ℝ) := Ioc_eq_empty (by simp [not_lt.2 hab.le])
    simp [hempty]

/-- **Convergence in distribution of the rescaled random walk.** -/
theorem tendsto_walkLaw_probabilityMeasure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => walkProb μ n t) atTop (𝓝 (brownianProb t)) :=
  tendsto_scaledProb hmean hvar h3 (m := fun n => ⌊(n : ℝ) * t⌋₊) (tendsto_floor_div t ht)

/-- **Donsker-type convergence tested against bounded continuous functions.** -/
theorem tendsto_integral_walkLaw_boundedContinuous {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℝ} (ht : 0 ≤ t) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ x, f x ∂(walkLaw μ n t)) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 t.toNNReal))) := by
  have h := tendsto_walkLaw_probabilityMeasure hmean hvar h3 ht
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
  exact h f

end Math2

import RequestProject.Blocks
import RequestProject.Weak

/-!
# Finite dimensional distributions of the rescaled random walk

We prove that the finite dimensional distributions of the rescaled random walk converge to those
of Brownian motion: for times `0 = t 0 ≤ t 1 ≤ ⋯ ≤ t k` the random vector

`(S_{⌊n t 1⌋}/√n, …, S_{⌊n t k⌋}/√n)`

converges in distribution to the vector of partial sums of independent centered Gaussians with
variances `t (j+1) - t j`, that is, to `(B_{t 1}, …, B_{t k})` for a Brownian motion `B`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction

section Fdd

/-- Partial sums of a vector: `partialSumMap z j = z 0 + ⋯ + z j`. -/
def partialSumMap (k : ℕ) (z : Fin k → ℝ) (j : Fin k) : ℝ := ∑ l ∈ Finset.Iic j, z l

theorem continuous_partialSumMap (k : ℕ) : Continuous (partialSumMap k) := by
  refine continuous_pi fun j => ?_
  exact continuous_finset_sum _ fun l _ => continuous_apply l

theorem measurable_partialSumMap (k : ℕ) : Measurable (partialSumMap k) :=
  (continuous_partialSumMap k).measurable

/-- The law of the increments of Brownian motion along the times `t`: independent centered
Gaussians with variances `t (j+1) - t j`. -/
noncomputable def brownianIncrements (t : ℕ → ℝ) (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun j : Fin k => gaussianReal 0 (t (j + 1) - t j).toNNReal)

instance isProbabilityMeasure_brownianIncrements (t : ℕ → ℝ) (k : ℕ) :
    IsProbabilityMeasure (brownianIncrements t k) := by
  rw [brownianIncrements]; infer_instance

/-- The law of `(B_{t 1}, …, B_{t k})` for a Brownian motion `B`: the partial sums of independent
centered Gaussian increments of variances `t (j+1) - t j`. -/
noncomputable def brownianFdd (t : ℕ → ℝ) (k : ℕ) : Measure (Fin k → ℝ) :=
  (brownianIncrements t k).map (partialSumMap k)

instance isProbabilityMeasure_brownianFdd (t : ℕ → ℝ) (k : ℕ) :
    IsProbabilityMeasure (brownianFdd t k) := by
  rw [brownianFdd]
  exact (brownianIncrements t k).isProbabilityMeasure_map
    (measurable_partialSumMap k).aemeasurable

/-- Summing consecutive blocks recovers the partial sum over the whole range. -/
theorem sum_blocks_eq_sum_range {a : ℕ → ℕ} (ha : Monotone a) (ha0 : a 0 = 0) (g : ℕ → ℝ)
    (m : ℕ) : ∑ l ∈ Finset.range m, ∑ i ∈ Finset.Ico (a l) (a (l + 1)), g i
      = ∑ i ∈ Finset.range (a m), g i := by
  induction m with
  | zero => simp [ha0]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.range_eq_Ico]
      exact Finset.sum_Ico_consecutive g (Nat.zero_le _) (ha (Nat.le_succ m))

/-- Rewriting a sum over `Finset.Iic j` in `Fin k` as a sum over a range of naturals. -/
theorem sum_Iic_fin (k : ℕ) (j : Fin k) (g : ℕ → ℝ) :
    ∑ l ∈ Finset.Iic j, g (l : ℕ) = ∑ l ∈ Finset.range ((j : ℕ) + 1), g l := by
  refine Finset.sum_nbij' (i := fun l : Fin k => (l : ℕ))
    (j := fun l : ℕ => (⟨min l (j : ℕ), lt_of_le_of_lt (min_le_right _ _) j.isLt⟩ : Fin k))
    ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_Iic] at hl
    simp only [Finset.mem_range]
    have : (l : ℕ) ≤ (j : ℕ) := hl
    omega
  · intro l _
    simp only [Finset.mem_Iic]
    show min l (j : ℕ) ≤ (j : ℕ)
    omega
  · intro l hl
    simp only [Finset.mem_Iic] at hl
    have : (l : ℕ) ≤ (j : ℕ) := hl
    ext
    show min (l : ℕ) (j : ℕ) = (l : ℕ)
    omega
  · intro l hl
    simp only [Finset.mem_range] at hl
    show min l (j : ℕ) = l
    omega
  · intro l _
    rfl


/-- If `s ≤ u` are nonnegative times, the number of steps in the block between them, divided by
`n`, converges to `u - s`. -/
theorem tendsto_floor_diff_div {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    Tendsto (fun n : ℕ => ((⌊(n : ℝ) * u⌋₊ - ⌊(n : ℝ) * s⌋₊ : ℕ) : ℝ) / n) atTop (𝓝 (u - s)) := by
  have hu : 0 ≤ u := le_trans hs hsu
  have hlim := (tendsto_floor_div u hu).sub (tendsto_floor_div s hs)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hmono : ⌊(n : ℝ) * s⌋₊ ≤ ⌊(n : ℝ) * u⌋₊ := by
    refine Nat.floor_le_floor ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  rw [Nat.cast_sub hmono]
  ring

section Walk

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The joint law of the rescaled increments of the walk is the product of the scaled convolution
powers. -/
theorem map_scaledIncrements (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) {a : ℕ → ℕ} (ha : Monotone a) (n k : ℕ) :
    P.map (fun ω (j : Fin k) =>
        (∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) / Real.sqrt n)
      = Measure.pi (fun j : Fin k => scaledLaw μ (a (j + 1) - a j) n) := by
  have hblocks := map_blockSums_eq_pi hmeas hindep hident ha k
  have hmeasv : Measurable
      (fun (ω : Ω) (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) :=
    measurable_pi_lambda _ fun j => measurable_blockSum hmeas _ _
  have hscale : Measurable (fun (v : Fin k → ℝ) (j : Fin k) => (Real.sqrt n)⁻¹ * v j) := by
    fun_prop
  have hcomp : (fun (ω : Ω) (j : Fin k) =>
        (∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) / Real.sqrt n)
      = (fun (v : Fin k → ℝ) (j : Fin k) => (Real.sqrt n)⁻¹ * v j)
        ∘ (fun (ω : Ω) (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) := by
    funext ω j
    simp [Function.comp, div_eq_inv_mul]
  rw [hcomp, ← Measure.map_map hscale hmeasv, hblocks,
    Measure.pi_map_pi (fun j => (measurable_const_mul (Real.sqrt n)⁻¹).aemeasurable)]
  rfl

omit [MeasurableSpace Ω] in
/-- The vector of rescaled positions is the vector of partial sums of the rescaled increments. -/
theorem positions_eq_partialSumMap {a : ℕ → ℕ} (ha : Monotone a) (ha0 : a 0 = 0) (n k : ℕ)
    (ω : Ω) :
    (fun j : Fin k => (∑ i ∈ Finset.range (a ((j : ℕ) + 1)), X i ω) / Real.sqrt n)
      = partialSumMap k (fun j : Fin k =>
          (∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) / Real.sqrt n) := by
  funext j
  rw [partialSumMap]
  have := sum_Iic_fin k j
    (fun l => (∑ i ∈ Finset.Ico (a l) (a (l + 1)), X i ω) / Real.sqrt n)
  rw [this, ← Finset.sum_div,
    sum_blocks_eq_sum_range ha ha0 (fun i => X i ω) ((j : ℕ) + 1)]


/-- Weak convergence of the joint law of the rescaled increments to the product of the Gaussian
increment laws. -/
theorem tendsto_incrementsProb (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℕ → ℝ} (hmono : Monotone t) (ht0 : t 0 = 0)
    (k : ℕ) :
    Tendsto (fun n : ℕ => ProbabilityMeasure.pi (fun j : Fin k =>
        scaledProb μ (⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊ - ⌊(n : ℝ) * t (j : ℕ)⌋₊) n)) atTop
      (𝓝 (ProbabilityMeasure.pi
        (fun j : Fin k => brownianProb (t ((j : ℕ) + 1) - t (j : ℕ))))) := by
  refine (ProbabilityMeasure.continuous_pi.tendsto _).comp (tendsto_pi_nhds.2 fun j => ?_)
  have hs : 0 ≤ t (j : ℕ) := by
    rw [← ht0]; exact hmono (Nat.zero_le _)
  have hsu : t (j : ℕ) ≤ t ((j : ℕ) + 1) := hmono (Nat.le_succ _)
  exact tendsto_scaledProb hmean hvar h3 (tendsto_floor_diff_div hs hsu)

/-- **Donsker's invariance principle: convergence of the finite dimensional distributions.**

Let `X 0, X 1, …` be i.i.d. real random variables with common law `μ`, centred, of unit variance
and with a finite third absolute moment, and let `S_m = X 0 + ⋯ + X (m-1)` be the associated
random walk.  Fix times `0 = t 0 ≤ t 1 ≤ ⋯`.  Then the random vector

`(S_{⌊n·t 1⌋}/√n, …, S_{⌊n·t k⌋}/√n)`

converges in distribution, as `n → ∞`, to `(B_{t 1}, …, B_{t k})`, the vector of the values of a
Brownian motion at the times `t 1, …, t k`, described here as the partial sums of independent
centred Gaussian increments of variances `t (j+1) - t j`. -/
theorem donsker_invariance_fdd (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℕ → ℝ} (hmono : Monotone t) (ht0 : t 0 = 0)
    (k : ℕ) (f : (Fin k → ℝ) →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, f (fun j : Fin k =>
        (∑ i ∈ Finset.range ⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n) ∂P) atTop
      (𝓝 (∫ z, f z ∂(brownianFdd t k))) := by
  -- the times, as numbers of steps
  have ha : ∀ n : ℕ, Monotone (fun j : ℕ => ⌊(n : ℝ) * t j⌋₊) := by
    intro n i j hij
    refine Nat.floor_le_floor ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have := hmono hij
    nlinarith
  have ha0 : ∀ n : ℕ, (fun j : ℕ => ⌊(n : ℝ) * t j⌋₊) 0 = 0 := by
    intro n
    simp [ht0]
  -- the law of the vector of rescaled positions
  have hmeasv : ∀ n : ℕ, Measurable (fun (ω : Ω) (j : Fin k) =>
      (∑ i ∈ Finset.Ico (⌊(n : ℝ) * t (j : ℕ)⌋₊) (⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊), X i ω)
        / Real.sqrt n) := by
    intro n
    exact measurable_pi_lambda _ fun j => (measurable_blockSum hmeas _ _).div_const _
  have hlaw : ∀ n : ℕ, P.map (fun (ω : Ω) (j : Fin k) =>
        (∑ i ∈ Finset.range ⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n)
      = (Measure.pi (fun j : Fin k =>
          scaledLaw μ (⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊ - ⌊(n : ℝ) * t (j : ℕ)⌋₊) n)).map
            (partialSumMap k) := by
    intro n
    have hpos : (fun (ω : Ω) (j : Fin k) =>
          (∑ i ∈ Finset.range ⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n)
        = (partialSumMap k) ∘ (fun (ω : Ω) (j : Fin k) =>
            (∑ i ∈ Finset.Ico (⌊(n : ℝ) * t (j : ℕ)⌋₊) (⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊), X i ω)
              / Real.sqrt n) := by
      funext ω
      exact positions_eq_partialSumMap (ha n) (ha0 n) n k ω
    rw [hpos, ← Measure.map_map (measurable_partialSumMap k) (hmeasv n),
      map_scaledIncrements hmeas hindep hident (ha n) n k]
  -- weak convergence of the increments, transported by the partial sum map
  have hconv := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_incrementsProb (μ := μ) hmean hvar h3 hmono ht0 k) (continuous_partialSumMap k)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hconv
  have hint := hconv f
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi,
    scaledProb_toMeasure, brownianProb_toMeasure] at hint
  have hlimit : (Measure.pi (fun j : Fin k =>
      gaussianReal 0 (t ((j : ℕ) + 1) - t (j : ℕ)).toNNReal)).map (partialSumMap k)
      = brownianFdd t k := rfl
  rw [hlimit] at hint
  refine hint.congr fun n => ?_
  have hmeaspos : Measurable (fun (ω : Ω) (j : Fin k) =>
      (∑ i ∈ Finset.range ⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n) :=
    measurable_pi_lambda _ fun j =>
      (Finset.measurable_sum _ fun i _ => hmeas i).div_const _
  rw [← hlaw n, integral_map hmeaspos.aemeasurable f.continuous.aestronglyMeasurable]

end Walk

end Fdd

end Math2

import Mathlib

/-!
# Third order Taylor bounds for test functions

This file introduces the class of test functions used in the Lindeberg swapping argument:
functions `f : ℝ → ℝ` which are bounded, three times differentiable with a bounded third
derivative.  For such a function we prove the crude Taylor estimate

`|f (w + u) - f w - f' w * u - f'' w * u ^ 2 / 2| ≤ M * |u| ^ 3`.
-/

namespace Math2

open Set

/-- `IsC3Test f f1 f2 f3 M` says that `f1, f2, f3` are the first three derivatives of `f`,
that `|f| ≤ M` and that `|f3| ≤ M`. -/
structure IsC3Test (f f1 f2 f3 : ℝ → ℝ) (M : ℝ) : Prop where
  hasDeriv0 : ∀ x, HasDerivAt f (f1 x) x
  hasDeriv1 : ∀ x, HasDerivAt f1 (f2 x) x
  hasDeriv2 : ∀ x, HasDerivAt f2 (f3 x) x
  bound0 : ∀ x, |f x| ≤ M
  bound3 : ∀ x, |f3 x| ≤ M

namespace IsC3Test

variable {f f1 f2 f3 : ℝ → ℝ} {M : ℝ}

theorem differentiable (h : IsC3Test f f1 f2 f3 M) : Differentiable ℝ f :=
  fun x => (h.hasDeriv0 x).differentiableAt

theorem continuous (h : IsC3Test f f1 f2 f3 M) : Continuous f :=
  h.differentiable.continuous

theorem nonneg (h : IsC3Test f f1 f2 f3 M) : 0 ≤ M :=
  le_trans (abs_nonneg _) (h.bound0 0)

private theorem abs_le_abs_of_mem_uIcc {u v : ℝ} (hv : v ∈ Set.uIcc (0 : ℝ) u) : |v| ≤ |u| := by
  have hu1 := le_abs_self u
  have hu2 := neg_abs_le u
  rcases Set.mem_uIcc.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [abs_le] <;> constructor <;> linarith

/-- Mean value bound for the second derivative. -/
theorem lipschitz_f2 (h : IsC3Test f f1 f2 f3 M) (x y : ℝ) :
    |f2 y - f2 x| ≤ M * |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f2) (f' := f3)
    (s := univ) (fun z _ => (h.hasDeriv2 z).hasDerivWithinAt) (fun z _ => by
      simpa [Real.norm_eq_abs] using h.bound3 z) convex_univ (mem_univ x) (mem_univ y)
  simpa [Real.norm_eq_abs] using this

/-- The crude third order Taylor estimate. -/
theorem taylor_bound (h : IsC3Test f f1 f2 f3 M) (w u : ℝ) :
    |f (w + u) - f w - f1 w * u - f2 w * u ^ 2 / 2| ≤ M * |u| ^ 3 := by
  have hM := h.nonneg
  set R : ℝ → ℝ := fun v => f (w + v) - f w - f1 w * v - f2 w * v ^ 2 / 2 with hRdef
  set R1 : ℝ → ℝ := fun v => f1 (w + v) - f1 w - f2 w * v with hR1def
  set R2 : ℝ → ℝ := fun v => f2 (w + v) - f2 w with hR2def
  -- derivatives
  have hdR : ∀ v, HasDerivAt R (R1 v) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => f (w + v)) (f1 (w + v)) v := by
      simpa using (h.hasDeriv0 (w + v)).comp v ((hasDerivAt_id v).const_add w)
    have h2 : HasDerivAt (fun v : ℝ => f1 w * v) (f1 w) v := by
      simpa using (hasDerivAt_id v).const_mul (f1 w)
    have h3 : HasDerivAt (fun v : ℝ => f2 w * v ^ 2 / 2) (f2 w * v) v := by
      have hh := ((hasDerivAt_pow 2 v).const_mul (f2 w)).div_const 2
      convert hh using 1
      ring
    exact ((h1.sub_const (f w)).sub h2).sub h3
  have hdR1 : ∀ v, HasDerivAt R1 (R2 v) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => f1 (w + v)) (f2 (w + v)) v := by
      simpa using (h.hasDeriv1 (w + v)).comp v ((hasDerivAt_id v).const_add w)
    have h2 : HasDerivAt (fun v : ℝ => f2 w * v) (f2 w) v := by
      simpa using (hasDerivAt_id v).const_mul (f2 w)
    exact (h1.sub_const (f1 w)).sub h2
  -- bounds
  have hb2 : ∀ v, |R2 v| ≤ M * |v| := by
    intro v
    have := h.lipschitz_f2 w (w + v)
    simpa [hR2def] using this
  have hb1 : ∀ v, |R1 v| ≤ M * |v| ^ 2 := by
    intro v
    have hzero : R1 0 = 0 := by simp [hR1def]
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := R1) (f' := R2)
      (s := Set.uIcc (0 : ℝ) v) (C := M * |v|)
      (fun z _ => (hdR1 z).hasDerivWithinAt)
      (fun z hz => by
        refine le_trans (by simpa [Real.norm_eq_abs] using hb2 z) ?_
        exact mul_le_mul_of_nonneg_left (abs_le_abs_of_mem_uIcc hz) hM)
      (convex_uIcc _ _) (left_mem_uIcc) (right_mem_uIcc)
    rw [hzero] at this
    simpa [Real.norm_eq_abs, sq, mul_assoc] using this
  have hzero : R 0 = 0 := by simp [hRdef]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := R) (f' := R1)
    (s := Set.uIcc (0 : ℝ) u) (C := M * |u| ^ 2)
    (fun z _ => (hdR z).hasDerivWithinAt)
    (fun z hz => by
      refine le_trans (by simpa [Real.norm_eq_abs] using hb1 z) ?_
      have : z ^ 2 ≤ |u| ^ 2 := by
        have h0 : (0:ℝ) ≤ |z| := abs_nonneg _
        have hz2 : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
        nlinarith [abs_le_abs_of_mem_uIcc hz, abs_nonneg u]
      exact mul_le_mul_of_nonneg_left this hM)
    (convex_uIcc _ _) (left_mem_uIcc) (right_mem_uIcc)
  rw [hzero] at this
  have huR : |R u| ≤ M * |u| ^ 2 * |u| := by
    simpa [Real.norm_eq_abs] using this
  calc |f (w + u) - f w - f1 w * u - f2 w * u ^ 2 / 2| = |R u| := by rw [hRdef]
    _ ≤ M * |u| ^ 2 * |u| := huR
    _ = M * |u| ^ 3 := by ring

end IsC3Test

end Math2

import RequestProject.Taylor
import RequestProject.ConvPow

/-!
# The Lindeberg swapping argument

We compare the integral of a smooth test function against convolution powers of two probability
measures which have the same first two moments.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

section Moments

variable {P : Measure ℝ} [IsProbabilityMeasure P]

theorem integrable_id_of_integrable_abs_cube (h3 : Integrable (fun x : ℝ => |x| ^ 3) P) :
    Integrable (fun x : ℝ => x) P := by
  refine Integrable.mono' (h3.add (integrable_const 1)) (by fun_prop) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [abs_nonneg x, sq_nonneg (|x| - 1), sq_nonneg (|x| + 1)]

theorem integrable_sq_of_integrable_abs_cube (h3 : Integrable (fun x : ℝ => |x| ^ 3) P) :
    Integrable (fun x : ℝ => x ^ 2) P := by
  refine Integrable.mono' (h3.add (integrable_const 1)) (by fun_prop) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, Pi.add_apply, abs_pow, sq_abs]
  nlinarith [abs_nonneg x, sq_nonneg (|x| - 1), sq_nonneg (|x| + 1), sq_abs x]

end Moments

variable {f f1 f2 f3 : ℝ → ℝ} {M : ℝ}

/-- Integrability of a bounded continuous test function against a probability measure. -/
theorem IsC3Test.integrable_shift (h : IsC3Test f f1 f2 f3 M) (P : Measure ℝ)
    [IsProbabilityMeasure P] (w : ℝ) : Integrable (fun x => f (w + x)) P := by
  refine Integrable.mono' (integrable_const M) ?_ ?_
  · exact (h.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  · filter_upwards with x
    simpa [Real.norm_eq_abs] using h.bound0 (w + x)

/-- A bounded continuous test function is integrable against any probability measure. -/
theorem IsC3Test.integrable (h : IsC3Test f f1 f2 f3 M) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] : Integrable f ν := by
  refine Integrable.mono' (integrable_const M) h.continuous.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using h.bound0 x

/-- The key one-step estimate: for a probability measure with vanishing mean, the integral of a
shifted test function is, up to an error controlled by the third absolute moment, given by the
second order Taylor expansion. -/
theorem IsC3Test.integral_shift_bound (h : IsC3Test f f1 f2 f3 M) {P : Measure ℝ}
    [IsProbabilityMeasure P] (h1 : ∫ x, x ∂P = 0) (h3 : Integrable (fun x : ℝ => |x| ^ 3) P)
    (w : ℝ) :
    |(∫ x, f (w + x) ∂P) - f w - f2 w * (∫ x, x ^ 2 ∂P) / 2| ≤ M * ∫ x, |x| ^ 3 ∂P := by
  have hid : Integrable (fun x : ℝ => x) P := integrable_id_of_integrable_abs_cube h3
  have hsq : Integrable (fun x : ℝ => x ^ 2) P := integrable_sq_of_integrable_abs_cube h3
  have hfw : Integrable (fun x => f (w + x)) P := h.integrable_shift P w
  have hA0 : Integrable (fun x : ℝ => f (w + x) - f w) P := hfw.sub (integrable_const (f w))
  have hA1 : Integrable (fun x : ℝ => f1 w * x) P := hid.const_mul (f1 w)
  have hA : Integrable (fun x : ℝ => f (w + x) - f w - f1 w * x) P := hA0.sub hA1
  have hB : Integrable (fun x : ℝ => f2 w * x ^ 2 / 2) P := (hsq.const_mul (f2 w)).div_const 2
  have hcomb : Integrable
      (fun x => f (w + x) - f w - f1 w * x - f2 w * x ^ 2 / 2) P := hA.sub hB
  have hint : (∫ x, (f (w + x) - f w - f1 w * x - f2 w * x ^ 2 / 2) ∂P)
      = (∫ x, f (w + x) ∂P) - f w - f2 w * (∫ x, x ^ 2 ∂P) / 2 := by
    rw [integral_sub hA hB, integral_sub hA0 hA1, integral_sub hfw (integrable_const (f w))]
    rw [integral_const_mul, h1]
    simp only [mul_zero, sub_zero]
    rw [integral_div, integral_const_mul, integral_const]
    simp
  rw [← hint]
  calc |∫ x, (f (w + x) - f w - f1 w * x - f2 w * x ^ 2 / 2) ∂P|
      ≤ ∫ x, |f (w + x) - f w - f1 w * x - f2 w * x ^ 2 / 2| ∂P := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := P) (f := fun x => f (w + x) - f w - f1 w * x - f2 w * x ^ 2 / 2)
    _ ≤ ∫ x, M * |x| ^ 3 ∂P := by
        refine integral_mono hcomb.abs (h3.const_mul M) ?_
        intro x
        exact h.taylor_bound w x
    _ = M * ∫ x, |x| ^ 3 ∂P := integral_const_mul _ _

/-- One swapping step: replacing `P` by `Q` inside a convolution changes the integral of a test
function by at most `M` times the sum of the third absolute moments. -/
theorem IsC3Test.conv_swap_bound (h : IsC3Test f f1 f2 f3 M) {P Q ρ : Measure ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure ρ]
    (hP1 : ∫ x, x ∂P = 0) (hQ1 : ∫ x, x ∂Q = 0)
    (hPQ2 : ∫ x, x ^ 2 ∂P = ∫ x, x ^ 2 ∂Q)
    (hP3 : Integrable (fun x : ℝ => |x| ^ 3) P) (hQ3 : Integrable (fun x : ℝ => |x| ^ 3) Q) :
    |(∫ x, f x ∂(ρ ∗ P)) - ∫ x, f x ∂(ρ ∗ Q)|
      ≤ M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) := by
  rw [integral_conv (h.integrable (ρ ∗ P)), integral_conv (h.integrable (ρ ∗ Q))]
  set F : ℝ → ℝ := fun w => ∫ x, f (w + x) ∂P with hF
  set G : ℝ → ℝ := fun w => ∫ x, f (w + x) ∂Q with hG
  have hFm : StronglyMeasurable F :=
    StronglyMeasurable.integral_prod_right' (ν := P)
      (f := fun p : ℝ × ℝ => f (p.1 + p.2))
      ((h.continuous.comp (continuous_fst.add continuous_snd)).stronglyMeasurable)
  have hGm : StronglyMeasurable G :=
    StronglyMeasurable.integral_prod_right' (ν := Q)
      (f := fun p : ℝ × ℝ => f (p.1 + p.2))
      ((h.continuous.comp (continuous_fst.add continuous_snd)).stronglyMeasurable)
  have hFb : ∀ w, |F w| ≤ M := by
    intro w
    have : |∫ x, f (w + x) ∂P| ≤ ∫ x, |f (w + x)| ∂P := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := P) (f := fun x => f (w + x))
    refine this.trans ?_
    calc ∫ x, |f (w + x)| ∂P ≤ ∫ _x, M ∂P :=
          integral_mono (h.integrable_shift P w).abs (integrable_const M)
            (fun x => h.bound0 (w + x))
      _ = M := by simp
  have hGb : ∀ w, |G w| ≤ M := by
    intro w
    have : |∫ x, f (w + x) ∂Q| ≤ ∫ x, |f (w + x)| ∂Q := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := Q) (f := fun x => f (w + x))
    refine this.trans ?_
    calc ∫ x, |f (w + x)| ∂Q ≤ ∫ _x, M ∂Q :=
          integral_mono (h.integrable_shift Q w).abs (integrable_const M)
            (fun x => h.bound0 (w + x))
      _ = M := by simp
  have hFi : Integrable F ρ :=
    Integrable.mono' (integrable_const M) hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hFb w)
  have hGi : Integrable G ρ :=
    Integrable.mono' (integrable_const M) hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hGb w)
  have hpt : ∀ w, |F w - G w| ≤ M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) := by
    intro w
    have hP := h.integral_shift_bound hP1 hP3 w
    have hQ := h.integral_shift_bound hQ1 hQ3 w
    rw [← hPQ2] at hQ
    calc |F w - G w|
        = |(F w - f w - f2 w * (∫ x, x ^ 2 ∂P) / 2)
            - (G w - f w - f2 w * (∫ x, x ^ 2 ∂P) / 2)| := by ring_nf
      _ ≤ |F w - f w - f2 w * (∫ x, x ^ 2 ∂P) / 2|
            + |G w - f w - f2 w * (∫ x, x ^ 2 ∂P) / 2| := abs_sub _ _
      _ ≤ (M * ∫ x, |x| ^ 3 ∂P) + M * ∫ x, |x| ^ 3 ∂Q := add_le_add hP hQ
      _ = M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) := by ring
  calc |(∫ w, F w ∂ρ) - ∫ w, G w ∂ρ| = |∫ w, (F w - G w) ∂ρ| := by
        rw [integral_sub hFi hGi]
    _ ≤ ∫ w, |F w - G w| ∂ρ := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := ρ) (f := fun w => F w - G w)
    _ ≤ ∫ _w, M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) ∂ρ :=
        integral_mono (hFi.sub hGi).abs (integrable_const _) hpt
    _ = M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) := by simp

private theorem conv_swap_right (a b c : Measure ℝ) [SFinite a] [SFinite b] [SFinite c] :
    (a ∗ b) ∗ c = (a ∗ c) ∗ b := by
  rw [Measure.conv_assoc, Measure.conv_comm b c, ← Measure.conv_assoc]

/-- The Lindeberg telescoping estimate: convolution powers of two probability measures with the
same first two moments have close integrals against a smooth test function. -/
theorem IsC3Test.convPow_swap_bound (h : IsC3Test f f1 f2 f3 M) {P Q : Measure ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP1 : ∫ x, x ∂P = 0) (hQ1 : ∫ x, x ∂Q = 0)
    (hPQ2 : ∫ x, x ^ 2 ∂P = ∫ x, x ^ 2 ∂Q)
    (hP3 : Integrable (fun x : ℝ => |x| ^ 3) P) (hQ3 : Integrable (fun x : ℝ => |x| ^ 3) Q) :
    ∀ (m : ℕ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      |(∫ x, f x ∂(ρ ∗ convPow P m)) - ∫ x, f x ∂(ρ ∗ convPow Q m)|
        ≤ m * (M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q)) := by
  intro m
  induction m with
  | zero => intro ρ _; simp
  | succ m ih =>
      intro ρ _
      have hK : 0 ≤ M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) := by
        have h1 : 0 ≤ ∫ x, |x| ^ 3 ∂P := integral_nonneg fun x => by positivity
        have h2 : 0 ≤ ∫ x, |x| ^ 3 ∂Q := integral_nonneg fun x => by positivity
        have := h.nonneg
        positivity
      have e1 : ρ ∗ convPow P (m + 1) = (ρ ∗ P) ∗ convPow P m := by
        rw [convPow_succ, ← Measure.conv_assoc, conv_swap_right]
      have e2 : (ρ ∗ P) ∗ convPow Q m = (ρ ∗ convPow Q m) ∗ P := conv_swap_right _ _ _
      have e3 : ρ ∗ convPow Q (m + 1) = (ρ ∗ convPow Q m) ∗ Q := by
        rw [convPow_succ, ← Measure.conv_assoc]
      have hstep : |(∫ x, f x ∂((ρ ∗ convPow Q m) ∗ P)) - ∫ x, f x ∂((ρ ∗ convPow Q m) ∗ Q)|
          ≤ M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) :=
        h.conv_swap_bound hP1 hQ1 hPQ2 hP3 hQ3
      have hih := ih (ρ ∗ P)
      rw [e1, e3]
      calc |(∫ x, f x ∂((ρ ∗ P) ∗ convPow P m)) - ∫ x, f x ∂((ρ ∗ convPow Q m) ∗ Q)|
          ≤ |(∫ x, f x ∂((ρ ∗ P) ∗ convPow P m)) - ∫ x, f x ∂((ρ ∗ P) ∗ convPow Q m)|
            + |(∫ x, f x ∂((ρ ∗ P) ∗ convPow Q m)) - ∫ x, f x ∂((ρ ∗ convPow Q m) ∗ Q)| := by
            simpa using abs_sub_le (∫ x, f x ∂((ρ ∗ P) ∗ convPow P m))
              (∫ x, f x ∂((ρ ∗ P) ∗ convPow Q m)) (∫ x, f x ∂((ρ ∗ convPow Q m) ∗ Q))
        _ ≤ m * (M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q))
              + M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) := by
            refine add_le_add hih ?_
            rw [e2]
            exact hstep
        _ = (m + 1 : ℕ) * (M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q)) := by push_cast; ring

end Math2

import RequestProject.ConvPow

/-!
# Random walks with i.i.d. steps

We show that the law of the partial sum `X 0 + ⋯ + X (m-1)` of an i.i.d. sequence with common
law `μ` is the `m`-fold convolution power `convPow μ m`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The law of the sum of the coordinates of a finite product measure is the convolution power. -/
theorem map_sum_pi (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)).map (fun ω => ∑ i, ω i) = convPow μ N := by
  induction N with
  | zero =>
      simp [convPow_zero, Measure.map_const]
  | succ N ih =>
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0 with he
      have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) 0
      have hcomp : (fun ω : Fin (N + 1) → ℝ => ∑ i, ω i)
          = (fun p : ℝ × (Fin N → ℝ) => p.1 + ∑ j, p.2 j) ∘ e := by
        funext ω
        simp [he, MeasurableEquiv.piFinSuccAbove, Fin.sum_univ_succ, Fin.tail]
      have hmeas : Measurable (fun p : ℝ × (Fin N → ℝ) => p.1 + ∑ j, p.2 j) := by fun_prop
      calc (Measure.pi (fun _ : Fin (N + 1) => μ)).map (fun ω => ∑ i, ω i)
          = ((Measure.pi (fun _ : Fin (N + 1) => μ)).map e).map
              (fun p : ℝ × (Fin N → ℝ) => p.1 + ∑ j, p.2 j) := by
            rw [hcomp, ← Measure.map_map hmeas e.measurable]
        _ = (μ.prod (Measure.pi (fun _ : Fin N => μ))).map
              (fun p : ℝ × (Fin N → ℝ) => p.1 + ∑ j, p.2 j) := by rw [hmp.map_eq]
        _ = μ ∗ convPow μ N := by
            have key := Measure.map_prod_map (f := (id : ℝ → ℝ))
              (g := fun ω : Fin N → ℝ => ∑ i, ω i) μ (Measure.pi (fun _ : Fin N => μ))
              measurable_id (by fun_prop)
            rw [Measure.map_id] at key
            rw [Measure.conv, ← ih, key, Measure.map_map (by fun_prop) (by fun_prop)]
            simp [Function.comp_def, Prod.map]
        _ = convPow μ (N + 1) := by rw [convPow_succ, Measure.conv_comm]

/-- **The law of a random walk with i.i.d. steps.**  If `X` is an independent family of random
variables, each with law `μ`, then the partial sum `X 0 + ⋯ + X (m-1)` has law `convPow μ m`. -/
theorem map_partialSum_eq_convPow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hident : ∀ i, P.map (X i) = μ) (m : ℕ) :
    P.map (fun ω => ∑ i ∈ Finset.range m, X i ω) = convPow μ m := by
  have hinj : Function.Injective (fun i : Fin m => (i : ℕ)) := Fin.val_injective
  have hindep' : iIndepFun (fun i : Fin m => X (i : ℕ)) P := hindep.precomp hinj
  have hvec : P.map (fun ω (i : Fin m) => X (i : ℕ) ω)
      = Measure.pi (fun _ : Fin m => μ) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin m => (hmeas (i : ℕ)).aemeasurable)).1 hindep']
    exact congrArg Measure.pi (funext fun i => hident (i : ℕ))
  have hsum : (fun ω => ∑ i ∈ Finset.range m, X i ω)
      = (fun v : Fin m → ℝ => ∑ i, v i) ∘ (fun ω (i : Fin m) => X (i : ℕ) ω) := by
    funext ω
    exact (Fin.sum_univ_eq_sum_range (fun i => X i ω) m).symm
  rw [hsum, ← Measure.map_map (by fun_prop) (by fun_prop), hvec, map_sum_pi]

end Math2

import RequestProject.Taylor

/-!
# Smooth step functions

We construct, for every `x : ℝ` and `δ > 0`, a smooth test function which equals `1` on
`Iic x`, vanishes on `Ici (x + δ)` and takes values in `[0, 1]`.  These functions are used to
sandwich indicators of half lines between smooth test functions, and hence to upgrade
convergence of integrals of smooth test functions to convergence of distribution functions.
-/

namespace Math2

open Set Filter Topology

/-- The smooth transition function of Mathlib. -/
noncomputable def sTrans0 : ℝ → ℝ := Real.smoothTransition
/-- Its first derivative. -/
noncomputable def sTrans1 : ℝ → ℝ := deriv sTrans0
/-- Its second derivative. -/
noncomputable def sTrans2 : ℝ → ℝ := deriv sTrans1
/-- Its third derivative. -/
noncomputable def sTrans3 : ℝ → ℝ := deriv sTrans2

theorem sTrans0_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sTrans0 :=
  Real.smoothTransition.contDiff

theorem sTrans1_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sTrans1 :=
  (contDiff_infty_iff_deriv.1 sTrans0_contDiff).2

theorem sTrans2_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sTrans2 :=
  (contDiff_infty_iff_deriv.1 sTrans1_contDiff).2

theorem sTrans3_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sTrans3 :=
  (contDiff_infty_iff_deriv.1 sTrans2_contDiff).2

theorem hasDerivAt_sTrans0 (y : ℝ) : HasDerivAt sTrans0 (sTrans1 y) y :=
  ((contDiff_infty_iff_deriv.1 sTrans0_contDiff).1 y).hasDerivAt

theorem hasDerivAt_sTrans1 (y : ℝ) : HasDerivAt sTrans1 (sTrans2 y) y :=
  ((contDiff_infty_iff_deriv.1 sTrans1_contDiff).1 y).hasDerivAt

theorem hasDerivAt_sTrans2 (y : ℝ) : HasDerivAt sTrans2 (sTrans3 y) y :=
  ((contDiff_infty_iff_deriv.1 sTrans2_contDiff).1 y).hasDerivAt

private theorem deriv_eq_zero_of_eventually_const_Iio {g : ℝ → ℝ} (hg : ∀ y < (0 : ℝ), g y = 0) :
    ∀ y < (0 : ℝ), deriv g y = 0 := by
  intro y hy
  have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hy] with z hz using hg z hz
  rw [hev.deriv_eq]
  simp

private theorem deriv_eq_zero_of_eventually_const_Ioi {g : ℝ → ℝ} {c : ℝ}
    (hg : ∀ y, (1 : ℝ) < y → g y = c) : ∀ y, (1 : ℝ) < y → deriv g y = 0 := by
  intro y hy
  have hev : g =ᶠ[𝓝 y] fun _ => c := by
    filter_upwards [Ioi_mem_nhds hy] with z hz using hg z hz
  rw [hev.deriv_eq]
  simp

theorem sTrans3_eq_zero_of_lt_zero : ∀ y < (0 : ℝ), sTrans3 y = 0 := by
  have h1 : ∀ y < (0 : ℝ), sTrans1 y = 0 :=
    deriv_eq_zero_of_eventually_const_Iio (fun y hy => Real.smoothTransition.zero_of_nonpos hy.le)
  have h2 : ∀ y < (0 : ℝ), sTrans2 y = 0 := deriv_eq_zero_of_eventually_const_Iio h1
  exact deriv_eq_zero_of_eventually_const_Iio h2

theorem sTrans3_eq_zero_of_one_lt : ∀ y, (1 : ℝ) < y → sTrans3 y = 0 := by
  have h1 : ∀ y, (1 : ℝ) < y → sTrans1 y = 0 :=
    deriv_eq_zero_of_eventually_const_Ioi (c := 1)
      (fun y hy => Real.smoothTransition.one_of_one_le hy.le)
  have h2 : ∀ y, (1 : ℝ) < y → sTrans2 y = 0 :=
    deriv_eq_zero_of_eventually_const_Ioi (c := 0) h1
  exact deriv_eq_zero_of_eventually_const_Ioi (c := 0) h2

/-- The third derivative of the smooth transition function is bounded. -/
theorem exists_bound_sTrans3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |sTrans3 y| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := sTrans3) (s := Icc (0 : ℝ) 1) sTrans3_contDiff.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [sTrans3_eq_zero_of_lt_zero y hy]
    simp
  · have : y ∈ Icc (0 : ℝ) 1 := by simp [hy]
    exact le_trans (by simpa [Real.norm_eq_abs] using hC y this) (le_max_left _ _)
  · rcases le_or_gt y 1 with hy1 | hy1
    · have : y ∈ Icc (0 : ℝ) 1 := ⟨hy.le, hy1⟩
      exact le_trans (by simpa [Real.norm_eq_abs] using hC y this) (le_max_left _ _)
    · rw [sTrans3_eq_zero_of_one_lt y hy1]
      simp

/-- A smooth function which is `1` on `Iic x`, `0` on `Ici (x + δ)` and takes values in
`[0,1]`, together with its first three derivatives and a common bound. -/
theorem exists_smooth_step (x δ : ℝ) (hδ : 0 < δ) :
    ∃ (f f1 f2 f3 : ℝ → ℝ) (M : ℝ), IsC3Test f f1 f2 f3 M ∧
      (∀ y, 0 ≤ f y) ∧ (∀ y, f y ≤ 1) ∧ (∀ y ≤ x, f y = 1) ∧
      (∀ y, x + δ ≤ y → f y = 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_sTrans3
  set r : ℝ := -δ⁻¹ with hr
  set u : ℝ → ℝ := fun y => (x + δ - y) / δ with hu
  have hu' : ∀ y, HasDerivAt u r y := by
    intro y
    have : HasDerivAt (fun y : ℝ => (x + δ - y) / δ) ((0 - 1) / δ) y := by
      exact (((hasDerivAt_id y).const_sub (x + δ)).div_const δ).congr_deriv (by ring)
    simpa [hr, hu, div_eq_mul_inv] using this
  refine ⟨fun y => sTrans0 (u y), fun y => sTrans1 (u y) * r, fun y => sTrans2 (u y) * r ^ 2,
    fun y => sTrans3 (u y) * r ^ 3, max 1 (C * |r| ^ 3), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro y
    exact (hasDerivAt_sTrans0 (u y)).comp y (hu' y)
  · intro y
    have := ((hasDerivAt_sTrans1 (u y)).comp y (hu' y)).mul_const r
    convert this using 1
    ring
  · intro y
    have := ((hasDerivAt_sTrans2 (u y)).comp y (hu' y)).mul_const (r ^ 2)
    convert this using 1
    ring
  · intro y
    have h0 : |sTrans0 (u y)| ≤ 1 := by
      show |Real.smoothTransition (u y)| ≤ 1
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    exact h0.trans (le_max_left _ _)
  · intro y
    have : |sTrans3 (u y) * r ^ 3| ≤ C * |r| ^ 3 := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right (hC _) (by positivity)
    exact this.trans (le_max_right _ _)
  · intro y
    exact Real.smoothTransition.nonneg _
  · intro y
    exact Real.smoothTransition.le_one _
  · intro y hy
    have : 1 ≤ u y := by
      rw [hu]
      rw [le_div_iff₀ hδ]
      linarith
    exact Real.smoothTransition.one_of_one_le this
  · intro y hy
    have : u y ≤ 0 := by
      rw [hu, div_nonpos_iff]
      right
      constructor <;> linarith
    exact Real.smoothTransition.zero_of_nonpos this

end Math2

import RequestProject.Walk

/-!
# Joint law of the increments of a random walk

For an i.i.d. sequence `X` with law `μ` and an increasing sequence of times `a 0 ≤ a 1 ≤ ⋯`, the
block sums `∑_{a j ≤ i < a (j+1)} X i` are independent, the `j`-th one having law
`convPow μ (a (j+1) - a j)`.  We record this as an identity between the joint law of the vector of
block sums and the product of the convolution powers.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set

section Blocks

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The law of a single block sum `X p + ⋯ + X (q-1)` is the convolution power of order `q - p`. -/
theorem map_blockSum_eq_convPow (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) (p q : ℕ) :
    P.map (fun ω => ∑ i ∈ Finset.Ico p q, X i ω) = convPow μ (q - p) := by
  have hshift : Function.Injective (fun i : ℕ => p + i) := fun i j hij =>
    Nat.add_left_cancel hij
  have hindep' : iIndepFun (fun i : ℕ => X (p + i)) P := hindep.precomp hshift
  have hident' : ∀ i, P.map (X (p + i)) = μ := fun i => hident _
  have hsum : (fun ω => ∑ i ∈ Finset.Ico p q, X i ω)
      = fun ω => ∑ i ∈ Finset.range (q - p), X (p + i) ω := by
    funext ω
    exact Finset.sum_Ico_eq_sum_range (fun i => X i ω) p q
  rw [hsum]
  exact map_partialSum_eq_convPow (fun i => hmeas (p + i)) hindep' hident' (q - p)

/-- Measurability of the block sums. -/
theorem measurable_blockSum (hmeas : ∀ i, Measurable (X i)) (p q : ℕ) :
    Measurable (fun ω => ∑ i ∈ Finset.Ico p q, X i ω) :=
  Finset.measurable_sum _ fun i _ => hmeas i

omit [IsProbabilityMeasure P] in
/-- The last block sum is independent of the vector of the earlier block sums. -/
theorem indepFun_blockSum_vector (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    {a : ℕ → ℕ} (ha : Monotone a) (k : ℕ) :
    IndepFun (fun ω => ∑ i ∈ Finset.Ico (a k) (a (k + 1)), X i ω)
      (fun ω (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) P := by
  classical
  set S : Finset ℕ := Finset.Ico (a k) (a (k + 1)) with hS
  set T : Finset ℕ := Finset.range (a k) with hT
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    rw [hS, Finset.mem_Ico] at hiS
    rw [hT, Finset.mem_range] at hiT
    omega
  have hbase := hindep.indepFun_finset S T hST hmeas
  have hφ : Measurable (fun w : S → ℝ => ∑ i : S, w i) := by fun_prop
  have hψ : Measurable (fun (w : T → ℝ) (j : Fin k) =>
      ∑ i : T, if a j ≤ (i : ℕ) ∧ (i : ℕ) < a (j + 1) then w i else 0) := by
    refine measurable_pi_lambda _ fun j => ?_
    exact Finset.measurable_sum _ fun i _ => by split_ifs <;> fun_prop
  have hcomp := hbase.comp hφ hψ
  have h1 : ((fun w : S → ℝ => ∑ i : S, w i) ∘ fun (ω : Ω) (i : S) => X (i : ℕ) ω)
      = fun ω => ∑ i ∈ Finset.Ico (a k) (a (k + 1)), X i ω := by
    funext ω
    simp only [Function.comp_apply]
    exact Finset.sum_coe_sort (Finset.Ico (a k) (a (k + 1))) (fun i => X i ω)
  have h2 : ((fun (w : T → ℝ) (j : Fin k) =>
        ∑ i : T, if a j ≤ (i : ℕ) ∧ (i : ℕ) < a (j + 1) then w i else 0)
      ∘ fun (ω : Ω) (i : T) => X (i : ℕ) ω)
      = fun ω (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω := by
    funext ω j
    simp only [Function.comp_apply]
    have hsub : Finset.Ico (a j) (a (j + 1)) ⊆ T := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hle : a ((j : ℕ) + 1) ≤ a k := ha (by omega)
      rw [hT, Finset.mem_range]
      omega
    have hcoe : (∑ i : T, if a j ≤ (i : ℕ) ∧ (i : ℕ) < a (j + 1) then X (i : ℕ) ω else 0)
        = ∑ i ∈ T, if a j ≤ i ∧ i < a (j + 1) then X i ω else 0 :=
      Finset.sum_coe_sort T (fun i => if a j ≤ i ∧ i < a (j + 1) then X i ω else 0)
    have hfilter : T.filter (fun i => a j ≤ i ∧ i < a (j + 1))
        = Finset.Ico (a j) (a (j + 1)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h
        exact ⟨hsub (Finset.mem_Ico.2 h), h⟩
    rw [hcoe, ← Finset.sum_filter, hfilter]
  rw [h1, h2] at hcomp
  exact hcomp

/-- **The joint law of the block sums of a random walk with i.i.d. steps.**  For an increasing
sequence of times `a`, the vector of increments `(∑_{a j ≤ i < a (j+1)} X i)_{j < k}` has as law
the product of the convolution powers `convPow μ (a (j+1) - a j)`; in particular the increments
are independent. -/
theorem map_blockSums_eq_pi (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) {a : ℕ → ℕ} (ha : Monotone a) (k : ℕ) :
    P.map (fun ω (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω)
      = Measure.pi (fun j : Fin k => convPow μ (a (j + 1) - a j)) := by
  induction k with
  | zero =>
      have hconst : (fun (ω : Ω) (j : Fin 0) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω)
          = fun _ => (fun j : Fin 0 => (0 : ℝ)) := by
        funext ω j
        exact j.elim0
      rw [hconst, Measure.map_const, measure_univ, one_smul]
      exact (Measure.pi_of_empty _ _).symm
  | succ k ih =>
      have hmeas1 : Measurable (fun ω => ∑ i ∈ Finset.Ico (a k) (a (k + 1)), X i ω) :=
        measurable_blockSum hmeas _ _
      have hmeas2 : Measurable
          (fun (ω : Ω) (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) :=
        measurable_pi_lambda _ fun j => measurable_blockSum hmeas _ _
      have hpair := (indepFun_iff_map_prod_eq_prod_map_map hmeas1.aemeasurable
        hmeas2.aemeasurable).1 (indepFun_blockSum_vector hmeas hindep ha k)
      rw [map_blockSum_eq_convPow hmeas hindep hident, ih] at hpair
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k) with he
      have hmp := measurePreserving_piFinSuccAbove
        (fun j : Fin (k + 1) => convPow μ (a (j + 1) - a j)) (Fin.last k)
      have hsymm : ∀ p : ℝ × (Fin k → ℝ),
          (⇑e.symm) p = (Fin.snoc p.2 p.1 : Fin (k + 1) → ℝ) := by
        intro p
        show Fin.insertNth (Fin.last k) p.1 p.2 = (Fin.snoc p.2 p.1 : Fin (k + 1) → ℝ)
        exact Fin.insertNth_last' _ _
      have hcomp : (fun (ω : Ω) (j : Fin (k + 1)) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω)
          = (⇑e.symm) ∘ (fun ω => ((∑ i ∈ Finset.Ico (a k) (a (k + 1)), X i ω),
              fun j : Fin k => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω)) := by
        funext ω
        simp only [Function.comp_apply, hsymm]
        funext j
        refine Fin.lastCases ?_ ?_ j
        · simp
        · intro j'
          simp
      have hpairmeas : Measurable (fun ω => ((∑ i ∈ Finset.Ico (a k) (a (k + 1)), X i ω),
          fun j : Fin k => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω)) := hmeas1.prodMk hmeas2
      rw [hcomp, ← Measure.map_map e.symm.measurable hpairmeas, hpair]
      have := (hmp.symm e).map_eq
      simpa [Fin.succAbove_last] using this

end Blocks

end Math2

import Mathlib

/-!
# Convolution powers

`Math2.convPow μ n` is the `n`-fold convolution power of a measure on `ℝ`; it is the law of the
sum of `n` independent random variables with law `μ`, i.e. of the random walk after `n` steps.
-/

namespace Math2

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The `n`-fold convolution power of a measure on `ℝ`. -/
noncomputable def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | (n + 1) => (convPow μ n) ∗ μ

@[simp] theorem convPow_zero (μ : Measure ℝ) : convPow μ 0 = Measure.dirac 0 := rfl

theorem convPow_succ (μ : Measure ℝ) (n : ℕ) : convPow μ (n + 1) = (convPow μ n) ∗ μ := rfl

instance isProbabilityMeasure_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ n : ℕ, IsProbabilityMeasure (convPow μ n)
  | 0 => by rw [convPow_zero]; infer_instance
  | (n + 1) => by
      have := isProbabilityMeasure_convPow μ n
      rw [convPow_succ]
      infer_instance

instance sfinite_convPow (μ : Measure ℝ) [SFinite μ] :
    ∀ n : ℕ, SFinite (convPow μ n)
  | 0 => by rw [convPow_zero]; infer_instance
  | (n + 1) => by
      have := sfinite_convPow μ n
      rw [convPow_succ]
      infer_instance

theorem convPow_one (μ : Measure ℝ) [SFinite μ] : convPow μ 1 = μ := by
  rw [convPow_succ, convPow_zero, Measure.dirac_zero_conv]

/-- Convolution powers commute with pushforward by an additive monoid homomorphism. -/
theorem map_convPow (L : ℝ →+ ℝ) (hL : Measurable L) (μ : Measure ℝ) [SFinite μ] (n : ℕ) :
    (convPow μ n).map L = convPow (μ.map L) n := by
  induction n with
  | zero => simp [Measure.map_dirac hL]
  | succ n ih =>
      rw [convPow_succ, Measure.map_conv_addMonoidHom L hL, ih, convPow_succ]

/-- Convolution powers of a centered Gaussian. -/
theorem convPow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    convPow (gaussianReal 0 v) n = gaussianReal 0 (n • v) := by
  induction n with
  | zero => simp [gaussianReal_zero_var]
  | succ n ih =>
      rw [convPow_succ, ih, gaussianReal_conv_gaussianReal]
      congr 1
      ring

end Math2

/-
/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib
import RequestProject.Walk
import RequestProject.Weak

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
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

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

section Donsker

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The rescaled random walk `S_{⌊n t⌋} / √n` associated with the step sequence `X`. -/
noncomputable def rescaledWalk (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n

/-- The law of the rescaled walk is exactly the measure `walkLaw μ n t` studied in the previous
files. -/
theorem map_rescaledWalk (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) (n : ℕ) (t : ℝ) :
    P.map (rescaledWalk X n t) = walkLaw μ n t := by
  have hsum : Measurable fun ω => ∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω :=
    Finset.measurable_sum _ fun i _ => hmeas i
  have hcomp : rescaledWalk X n t
      = (fun x : ℝ => (Real.sqrt n)⁻¹ * x) ∘
        (fun ω => ∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) := by
    funext ω
    simp [rescaledWalk, Function.comp, div_eq_inv_mul]
  rw [hcomp, ← Measure.map_map (by fun_prop) hsum,
    map_partialSum_eq_convPow hmeas hindep hident, walkLaw, scaledLaw]

/-- **Donsker's invariance principle (one-dimensional marginals).**

Let `X 0, X 1, …` be an i.i.d. sequence of real random variables with common law `μ`, which is
centred (`∫ y ∂μ = 0`), has unit variance (`∫ y² ∂μ = 1`) and a finite third absolute moment.
Write `S_m = X 0 + ⋯ + X (m-1)` for the random walk.  Then for every time `t ≥ 0` the rescaled
walk `S_{⌊n t⌋} / √n` converges in distribution, as `n → ∞`, to the value at time `t` of a
standard Brownian motion, i.e. to the centred Gaussian law with variance `t`.

Convergence in distribution is stated in two equivalent standard forms: convergence of the
distribution functions at every point, and convergence of the expectations of every bounded
continuous test function. -/
theorem donsker_invariance (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℝ} (ht : 0 ≤ t) :
    (∀ x : ℝ,
        Tendsto
          (fun n : ℕ => P.real {ω | (∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n ≤ x})
          atTop (𝓝 ((gaussianReal 0 t.toNNReal).real (Iic x)))) ∧
      ∀ f : ℝ →ᵇ ℝ,
        Tendsto
          (fun n : ℕ => ∫ ω, f ((∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n) ∂P)
          atTop (𝓝 (∫ x, f x ∂(gaussianReal 0 t.toNNReal))) := by
  have hmap : ∀ n : ℕ, P.map (rescaledWalk X n t) = walkLaw μ n t :=
    fun n => map_rescaledWalk hmeas hindep hident n t
  have hmeasw : ∀ n : ℕ, Measurable (rescaledWalk X n t) := by
    intro n
    have hsum : Measurable fun ω => ∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω :=
      Finset.measurable_sum _ fun i _ => hmeas i
    exact hsum.div_const _
  constructor
  · intro x
    have hset : ∀ n : ℕ,
        P.real {ω | (∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n ≤ x}
          = (walkLaw μ n t).real (Iic x) := by
      intro n
      have h1 : P {ω | (∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n ≤ x}
          = (walkLaw μ n t) (Iic x) := by
        rw [← hmap n, Measure.map_apply (hmeasw n) measurableSet_Iic]
        rfl
      simp [Measure.real, h1]
    simp only [hset]
    exact tendsto_walkLaw_measureReal_Iic' hmean hvar h3 ht x
  · intro f
    have hint : ∀ n : ℕ,
        ∫ ω, f ((∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n) ∂P
          = ∫ y, f y ∂(walkLaw μ n t) := by
      intro n
      rw [← hmap n, integral_map (hmeasw n).aemeasurable f.continuous.aestronglyMeasurable]
      rfl
    simp only [hint]
    exact tendsto_integral_walkLaw_boundedContinuous hmean hvar h3 ht f

end Donsker

end Math2

