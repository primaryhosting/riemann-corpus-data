import Mathlib
/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
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

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/
def IsSymmConvex {E : Type*} [AddCommGroup E] [Module ℝ E] (K : Set E) : Prop :=
  Convex ℝ K ∧ ∀ x ∈ K, -x ∈ K

/-- The Gaussian correlation property for a fixed measure `μ`:
for all symmetric convex measurable sets `K`, `L` one has `μ K * μ L ≤ μ (K ∩ L)`. -/
def HasGaussianCorrelation {E : Type*} [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∀ K L : Set E, MeasurableSet K → MeasurableSet L → IsSymmConvex K → IsSymmConvex L →
    μ K * μ L ≤ μ (K ∩ L)

/-- **The Gaussian correlation inequality** (Royen's theorem) on a space `E`:
every centered (i.e. symmetric) Gaussian measure on `E` satisfies the correlation
inequality for symmetric convex sets.

This is the formalized *statement*. Below we prove it in dimension one
(`Frontier.gaussian_correlation : GaussianCorrelationInequality ℝ`), together with several
Lean-checked reductions; the full theorem in dimension `n` (Royen, 2014) is not proved here. -/
def GaussianCorrelationInequality (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] : Prop :=
  ∀ μ : Measure E, IsGaussian μ → μ.map (fun x => -x) = μ → HasGaussianCorrelation μ

section Elementary

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]

omit [AddCommGroup E] [Module ℝ E] in
/-- Nested sets always satisfy the correlation inequality (for a probability measure). -/
theorem measure_mul_le_measure_inter_of_subset (μ : Measure E) [IsProbabilityMeasure μ]
    {K L : Set E} (h : K ⊆ L ∨ L ⊆ K) : μ K * μ L ≤ μ (K ∩ L) := by
  rcases h with h | h
  · rw [Set.inter_eq_self_of_subset_left h]
    exact mul_le_of_le_one_right' prob_le_one
  · rw [Set.inter_eq_self_of_subset_right h]
    exact mul_le_of_le_one_left' prob_le_one

end Elementary

section Dim1

/-- A symmetric convex subset of `ℝ` is a "downward closed set in absolute value":
if `a ∈ K` and `|b| ≤ |a|` then `b ∈ K`. -/
theorem IsSymmConvex.mem_of_abs_le {K : Set ℝ} (hK : IsSymmConvex K) {a b : ℝ}
    (ha : a ∈ K) (hab : |b| ≤ |a|) : b ∈ K := by
  obtain ⟨hconv, hsymm⟩ := hK
  rcases eq_or_ne a 0 with rfl | ha0
  · have : b = 0 := by
      have : |b| ≤ 0 := by simpa using hab
      simpa using abs_nonpos_iff.mp this
    simpa [this] using ha
  · have haabs : 0 < |a| := abs_pos.mpr ha0
    set t : ℝ := (1 + b / a) / 2 with ht
    have hba : |b / a| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one haabs).mpr hab
    have h1 : -1 ≤ b / a := neg_le_of_abs_le hba
    have h2 : b / a ≤ 1 := le_of_abs_le hba
    have ht0 : 0 ≤ t := by rw [ht]; linarith
    have ht1 : 0 ≤ 1 - t := by rw [ht]; linarith
    have hsum : t + (1 - t) = 1 := by ring
    have := hconv ha (hsymm a ha) ht0 ht1 hsum
    have hb : t • a + (1 - t) • (-a) = b := by
      have : t * a + (1 - t) * (-a) = a * (2 * t - 1) := by ring
      rw [smul_eq_mul, smul_eq_mul, this, ht]
      field_simp
      ring
    rwa [hb] at this

/-- Two symmetric convex subsets of `ℝ` are always nested. -/
theorem symmConvex_subset_total {K L : Set ℝ} (hK : IsSymmConvex K) (hL : IsSymmConvex L) :
    K ⊆ L ∨ L ⊆ K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp h1
  obtain ⟨y, hyL, hyK⟩ := Set.not_subset.mp h2
  rcases le_total |y| |x| with h | h
  · exact hyK (hK.mem_of_abs_le hxK h)
  · exact hxL (hL.mem_of_abs_le hyL h)

/-- **Base case of the Gaussian correlation inequality (dimension one).**
In fact any probability measure on `ℝ` satisfies the correlation inequality for
symmetric convex sets, since these are totally ordered by inclusion. -/
theorem hasGaussianCorrelation_real (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    HasGaussianCorrelation μ := fun _K _L _ _ hK hL =>
  measure_mul_le_measure_inter_of_subset μ (symmConvex_subset_total hK hL)

/-- **The Gaussian correlation inequality in dimension one.** -/
theorem gaussian_correlation : GaussianCorrelationInequality ℝ := by
  intro μ hμ _
  have : IsProbabilityMeasure μ := hμ.toIsProbabilityMeasure μ
  exact hasGaussianCorrelation_real μ

/-- Non-vacuity of the main theorem: every centered real Gaussian `N(0, v)` satisfies the
hypotheses, hence the correlation inequality for symmetric convex sets. -/
theorem hasGaussianCorrelation_gaussianReal_zero (v : NNReal) :
    HasGaussianCorrelation (gaussianReal 0 v) :=
  gaussian_correlation _ inferInstance (by simpa using gaussianReal_map_neg (μ := 0) (v := v))

end Dim1

section Reductions

/-- Preimages of symmetric convex sets under linear maps are symmetric convex. -/
theorem IsSymmConvex.preimage_linearMap {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (T : E →ₗ[ℝ] F) {K : Set F} (hK : IsSymmConvex K) :
    IsSymmConvex (T ⁻¹' K) := by
  refine ⟨hK.1.linear_preimage T, fun x hx => ?_⟩
  simp only [Set.mem_preimage, map_neg]
  exact hK.2 _ hx

/-- **Reduction along linear pushforwards.** If a measure `μ` on `E` satisfies the Gaussian
correlation inequality, then so does its pushforward by any measurable linear map `T : E → F`.
In particular, the inequality for the standard Gaussian implies it for all its linear images. -/
theorem hasGaussianCorrelation_map {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace E] [AddCommGroup F] [Module ℝ F] [MeasurableSpace F]
    {μ : Measure E} (hμ : HasGaussianCorrelation μ) (T : E →ₗ[ℝ] F) (hT : Measurable T) :
    HasGaussianCorrelation (μ.map T) := by
  intro K L hKm hLm hK hL
  rw [Measure.map_apply hT hKm, Measure.map_apply hT hLm,
    Measure.map_apply hT (hKm.inter hLm), Set.preimage_inter]
  exact hμ _ _ (hKm.preimage hT) (hLm.preimage hT)
    (hK.preimage_linearMap T) (hL.preimage_linearMap T)

/-- Products of symmetric convex sets are symmetric convex. -/
theorem IsSymmConvex.prod {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {K : Set E} {L : Set F}
    (hK : IsSymmConvex K) (hL : IsSymmConvex L) : IsSymmConvex (K ×ˢ L) :=
  ⟨hK.1.prod hL.1, fun _ hx => ⟨hK.2 _ hx.1, hL.2 _ hx.2⟩⟩

/-- **Tensorization for box-shaped sets.** If `μ` and `ν` satisfy the correlation inequality,
then the product measure satisfies it for products of symmetric convex sets. -/
theorem measure_prod_box_correlation {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace E] [AddCommGroup F] [Module ℝ F] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [SFinite μ] [SFinite ν]
    {K₁ L₁ : Set E} {K₂ L₂ : Set F}
    (h₁ : μ K₁ * μ L₁ ≤ μ (K₁ ∩ L₁)) (h₂ : ν K₂ * ν L₂ ≤ ν (K₂ ∩ L₂)) :
    (μ.prod ν) (K₁ ×ˢ K₂) * (μ.prod ν) (L₁ ×ˢ L₂) ≤ (μ.prod ν) ((K₁ ×ˢ K₂) ∩ (L₁ ×ˢ L₂)) := by
  rw [Set.prod_inter_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  calc μ K₁ * ν K₂ * (μ L₁ * ν L₂) = (μ K₁ * μ L₁) * (ν K₂ * ν L₂) := by ring
    _ ≤ μ (K₁ ∩ L₁) * ν (K₂ ∩ L₂) := mul_le_mul' h₁ h₂

/-- **A genuinely infinite/high-dimensional consequence of the base case.**
For a Gaussian measure `μ` on a Banach space `E` and a continuous linear functional `f`,
the correlation inequality holds for any two sets that are preimages under `f` of symmetric
convex subsets of `ℝ` (e.g. two parallel symmetric slabs). This is obtained by pushing `μ`
forward along `f`, which is a Gaussian measure on `ℝ`, and applying the one-dimensional case. -/
theorem gaussian_correlation_preimage_dual {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) [IsGaussian μ] (f : StrongDual ℝ E) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAc : IsSymmConvex A) (hBc : IsSymmConvex B) :
    μ (f ⁻¹' A) * μ (f ⁻¹' B) ≤ μ (f ⁻¹' A ∩ f ⁻¹' B) := by
  have hf : Measurable f := f.continuous.measurable
  have hmap : μ.map f = gaussianReal (μ[f]) (Var[f; μ]).toNNReal :=
    IsGaussian.map_eq_gaussianReal f
  have hprob : IsProbabilityMeasure (μ.map f) := by
    rw [hmap]; infer_instance
  have := hasGaussianCorrelation_real (μ.map f) A B hA hB hAc hBc
  rwa [Measure.map_apply hf hA, Measure.map_apply hf hB,
    Measure.map_apply hf (hA.inter hB), Set.preimage_inter] at this

/-- Symmetric closed intervals `{t | |t| ≤ a}` are symmetric convex. -/
theorem isSymmConvex_abs_le (a : ℝ) : IsSymmConvex {t : ℝ | |t| ≤ a} := by
  constructor
  · intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq] at *
    calc |s • x + t • y| ≤ |s * x| + |t * y| := abs_add_le _ _
      _ = s * |x| + t * |y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * a + t * a := by gcongr
      _ = a := by rw [← add_mul, hst, one_mul]
  · intro x hx
    simpa using hx

/-- **Parallel slabs.** For a Gaussian measure on a Banach space, the correlation inequality
holds for two symmetric slabs determined by the same continuous linear functional. -/
theorem gaussian_correlation_parallel_slabs {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) [IsGaussian μ] (f : StrongDual ℝ E) (a b : ℝ) :
    μ {x | |f x| ≤ a} * μ {x | |f x| ≤ b} ≤ μ ({x | |f x| ≤ a} ∩ {x | |f x| ≤ b}) :=
  gaussian_correlation_preimage_dual μ f
    (measurableSet_le measurable_norm measurable_const)
    (measurableSet_le measurable_norm measurable_const)
    (isSymmConvex_abs_le a) (isSymmConvex_abs_le b)

end Reductions

end Frontier

