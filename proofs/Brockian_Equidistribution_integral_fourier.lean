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
# Weyl's equidistribution criterion on the additive circle

This file develops equidistribution of sequences on `AddCircle T`.

* `Brockian.Equidistribution.Equidistributed x` says that the empirical averages of a sequence
  `x : ℕ → AddCircle T` converge, against every continuous test function, to the integral of the
  test function with respect to the normalised Haar (probability) measure.
* `Brockian.Equidistribution.WeylSumsVanish x` is the Weyl-sum hypothesis: the empirical averages
  of every nontrivial Fourier monomial `fourier k` (`k ≠ 0`) tend to `0`.
* `Brockian.Equidistribution.equidistribution_of_asymptotic` is the conditional statement
  (Weyl's criterion): `WeylSumsVanish x → Equidistributed x`.
* `Brockian.Equidistribution.weylSumsVanish_rotSeq` discharges the hypothesis for the
  irrational rotation sequence `n ↦ n * a` on `AddCircle 1`, and
  `Brockian.Equidistribution.equidistributed_irrational_rotation` is the resulting unconditional
  equidistribution theorem.
-/

open Filter Topology MeasureTheory AddCircle Complex Submodule Set

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The empirical average of `f` over the first `N` terms of the sequence `x`. -/
noncomputable def avg (x : ℕ → AddCircle T) (f : AddCircle T → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (x n)

/-- A sequence in `AddCircle T` is equidistributed if its empirical averages converge to the
integral against the normalised Haar probability measure, for every continuous test function. -/
def Equidistributed (x : ℕ → AddCircle T) : Prop :=
  ∀ f : C(AddCircle T, ℂ), Tendsto (avg x f) atTop (𝓝 (∫ t, f t ∂haarAddCircle))

/-- The Weyl-sum hypothesis: all nontrivial exponential sums have vanishing averages. -/
def WeylSumsVanish (x : ℕ → AddCircle T) : Prop :=
  ∀ k : ℤ, k ≠ 0 → Tendsto (avg x (fourier k)) atTop (𝓝 0)

/-- The integral of a Fourier monomial against the Haar probability measure. -/
lemma integral_fourier (k : ℤ) :
    ∫ t : AddCircle T, fourier k t ∂haarAddCircle = if k = 0 then 1 else 0 := by
  have h0 := congrFun (fourierCoeff_fourier (T := T) k) 0
  rw [fourierCoeff] at h0
  simp only [Pi.single_apply, neg_zero, fourier_zero, smul_eq_mul, one_mul, eq_comm] at h0
  rw [← h0]

/-- Continuous functions on the circle are integrable for the Haar probability measure. -/
lemma integrable_of_continuousMap (f : C(AddCircle T, ℂ)) :
    Integrable (fun t => f t) (haarAddCircle (T := T)) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit hT in
lemma avg_add (x : ℕ → AddCircle T) (f g : AddCircle T → ℂ) (N : ℕ) :
    avg x (f + g) N = avg x f N + avg x g N := by
  simp [avg, Finset.sum_add_distrib, mul_add]

omit hT in
lemma avg_sub (x : ℕ → AddCircle T) (f g : AddCircle T → ℂ) (N : ℕ) :
    avg x (f - g) N = avg x f N - avg x g N := by
  simp [avg, Finset.sum_sub_distrib, mul_sub]

omit hT in
lemma avg_smul (x : ℕ → AddCircle T) (c : ℂ) (f : AddCircle T → ℂ) (N : ℕ) :
    avg x (c • f) N = c * avg x f N := by
  simp only [avg, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma norm_avg_le (x : ℕ → AddCircle T) (f : C(AddCircle T, ℂ)) (N : ℕ) :
    ‖avg x f N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [avg, norm_nonneg f]
  · rw [avg, norm_mul, norm_inv]
    have h1 : ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ N * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ ∑ n ∈ Finset.range N, ‖f (x n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := Finset.sum_le_sum (fun n _ => f.norm_coe_le_norm _)
        _ = N * ‖f‖ := by simp
    have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [Complex.norm_natCast, inv_mul_le_iff₀ hNpos]
    simpa [mul_comm] using h1

lemma norm_integral_le (f : C(AddCircle T, ℂ)) :
    ‖∫ t : AddCircle T, f t ∂haarAddCircle‖ ≤ ‖f‖ := by
  have := norm_integral_le_of_norm_le_const (μ := (haarAddCircle : Measure (AddCircle T)))
    (C := ‖f‖) (f := fun t => f t) (Filter.Eventually.of_forall (fun t => f.norm_coe_le_norm t))
  simpa using this

/-- The conclusion of Weyl's criterion holds for every element of the span of the Fourier
monomials. -/
lemma tendsto_avg_of_mem_span (x : ℕ → AddCircle T) (hx : WeylSumsVanish x)
    (f : C(AddCircle T, ℂ)) (hf : f ∈ span ℂ (range (fourier (T := T)))) :
    Tendsto (avg x f) atTop (𝓝 (∫ t, f t ∂haarAddCircle)) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      rcases eq_or_ne k 0 with rfl | hk
      · rw [integral_fourier, if_pos rfl]
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_gt_atTop 0] with N hN
        have hNe : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
        simp [avg, hNe]
      · rw [integral_fourier, if_neg hk]
        exact hx k hk
  | zero =>
      have h : ∀ N : ℕ, avg x (⇑(0 : C(AddCircle T, ℂ))) N = 0 := by intro N; simp [avg]
      simp only [ContinuousMap.zero_apply, integral_zero]
      exact tendsto_const_nhds.congr (fun N => (h N).symm)
  | add g h hg hh ihg ihh =>
      have hadd : ∀ N, avg x (⇑(g + h)) N = avg x ⇑g N + avg x ⇑h N := by
        intro N; simpa using avg_add x ⇑g ⇑h N
      rw [show (∫ t, (g + h) t ∂haarAddCircle) = (∫ t, g t ∂haarAddCircle) + ∫ t, h t ∂haarAddCircle
        from by
          simpa using integral_add (integrable_of_continuousMap g) (integrable_of_continuousMap h)]
      exact (ihg.add ihh).congr (fun N => (hadd N).symm)
  | smul c g hg ih =>
      have hs : ∀ N, avg x (⇑(c • g)) N = c * avg x ⇑g N := by
        intro N; simpa using avg_smul x c ⇑g N
      rw [show (∫ t, (c • g) t ∂haarAddCircle) = c * ∫ t, g t ∂haarAddCircle from by
        simp [integral_const_mul]]
      exact (ih.const_mul c).congr (fun N => (hs N).symm)

/-- Trigonometric polynomials are dense in the continuous functions on the circle. -/
lemma exists_mem_span_norm_sub_lt (f : C(AddCircle T, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ span ℂ (range (fourier (T := T))), ‖f - g‖ < ε := by
  have hcl : f ∈ closure ((span ℂ (range (fourier (T := T)))) : Set C(AddCircle T, ℂ)) := by
    show f ∈ (span ℂ (range (fourier (T := T)))).topologicalClosure
    rw [span_fourier_closure_eq_top]; trivial
  rw [Metric.mem_closure_iff] at hcl
  obtain ⟨g, hg, hdist⟩ := hcl ε hε
  exact ⟨g, hg, by rwa [← dist_eq_norm]⟩

/-- **Weyl's criterion**: if all nontrivial Weyl sums of `x` have vanishing averages, then `x`
is equidistributed. -/
theorem equidistribution_of_asymptotic (x : ℕ → AddCircle T) (hx : WeylSumsVanish x) :
    Equidistributed x := by
  intro f
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgspan, hg⟩ := exists_mem_span_norm_sub_lt f (ε := ε / 3) (by positivity)
  have hgt := tendsto_avg_of_mem_span x hx g hgspan
  rw [Metric.tendsto_atTop] at hgt
  obtain ⟨N₀, hN₀⟩ := hgt (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ‖avg x ⇑f N - avg x ⇑g N‖ ≤ ε / 3 := by
    have he : avg x ⇑f N - avg x ⇑g N = avg x (⇑(f - g)) N := by
      simpa using (avg_sub x ⇑f ⇑g N).symm
    rw [he]
    exact (norm_avg_le x (f - g) N).trans hg.le
  have h2 : ‖avg x ⇑g N - ∫ t, g t ∂haarAddCircle‖ < ε / 3 := by
    have := hN₀ N hN
    rwa [dist_eq_norm] at this
  have h3 : ‖(∫ t, g t ∂haarAddCircle) - ∫ t, f t ∂haarAddCircle‖ ≤ ε / 3 := by
    have he : (∫ t, g t ∂haarAddCircle) - ∫ t, f t ∂haarAddCircle
        = ∫ t, (g - f) t ∂haarAddCircle := by
      simpa using
        (integral_sub (integrable_of_continuousMap g) (integrable_of_continuousMap f)).symm
    rw [he]
    refine (norm_integral_le (g - f)).trans ?_
    rw [← norm_neg, neg_sub]
    exact hg.le
  have hsplit : dist (avg x ⇑f N) (∫ t, f t ∂haarAddCircle)
      ≤ ‖avg x ⇑f N - avg x ⇑g N‖ + ‖avg x ⇑g N - ∫ t, g t ∂haarAddCircle‖
        + ‖(∫ t, g t ∂haarAddCircle) - ∫ t, f t ∂haarAddCircle‖ := by
    rw [dist_eq_norm]
    have : avg x ⇑f N - ∫ t, f t ∂haarAddCircle
        = (avg x ⇑f N - avg x ⇑g N) + (avg x ⇑g N - ∫ t, g t ∂haarAddCircle)
          + ((∫ t, g t ∂haarAddCircle) - ∫ t, f t ∂haarAddCircle) := by ring
    rw [this]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  linarith

section Rotation

/-- The rotation sequence `n ↦ n * a` on `AddCircle 1`. -/
noncomputable def rotSeq (a : ℝ) (n : ℕ) : AddCircle (1 : ℝ) := ((n * a : ℝ) : AddCircle (1 : ℝ))

/-- The Fourier monomials evaluated along an irrational rotation form a geometric sequence. -/
lemma fourier_rotSeq (a : ℝ) (k : ℤ) (n : ℕ) :
    fourier k (rotSeq a n) = (Complex.exp (((2 * Real.pi * k * a : ℝ) : ℂ) * Complex.I)) ^ n := by
  rw [rotSeq, fourier_coe_apply, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- For irrational `a` and `k ≠ 0`, the base of that geometric sequence is not `1`. -/
lemma exp_ne_one_of_irrational {a : ℝ} (ha : Irrational a) {k : ℤ} (hk : k ≠ 0) :
    Complex.exp (((2 * Real.pi * k * a : ℝ) : ℂ) * Complex.I) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hka : ((k : ℝ) * a : ℝ) = (m : ℝ) := by
    have : (((k : ℝ) * a : ℝ) : ℂ) = ((m : ℝ) : ℂ) := by
      push_cast at hm ⊢
      field_simp at hm
      exact hm
    exact_mod_cast this
  exact (ha.intCast_mul hk).ne_int m hka

/-- Discharging the hypothesis of Weyl's criterion for an irrational rotation. -/
theorem weylSumsVanish_rotSeq {a : ℝ} (ha : Irrational a) : WeylSumsVanish (rotSeq a) := by
  intro k hk
  set z : ℂ := Complex.exp (((2 * Real.pi * k * a : ℝ) : ℂ) * Complex.I) with hzdef
  have hz1 : z ≠ 1 := exp_ne_one_of_irrational ha hk
  have hznorm : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hd : 0 < ‖z - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hz1
  have havg : ∀ N : ℕ, avg (rotSeq a) (fourier k) N = (N : ℂ)⁻¹ * ((z ^ N - 1) / (z - 1)) := by
    intro N
    simp only [avg, fourier_rotSeq a k, ← hzdef]
    rw [geom_sum_eq hz1]
  refine squeeze_zero_norm (a := fun N : ℕ => (2 / ‖z - 1‖) / N) (fun N => ?_) ?_
  · show ‖avg (rotSeq a) (⇑(fourier k)) N‖ ≤ 2 / ‖z - 1‖ / (N : ℝ)
    rw [havg N, norm_mul, norm_inv, Complex.norm_natCast, norm_div, div_eq_inv_mul (2 / ‖z - 1‖)]
    have h2 : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm]; norm_num
    gcongr
  · exact tendsto_const_div_atTop_nhds_zero_nat _

/-- **Unconditional equidistribution** of the irrational rotation sequence. -/
theorem equidistributed_irrational_rotation {a : ℝ} (ha : Irrational a) :
    Equidistributed (rotSeq a) :=
  equidistribution_of_asymptotic _ (weylSumsVanish_rotSeq ha)

end Rotation

end Brockian.Equidistribution

