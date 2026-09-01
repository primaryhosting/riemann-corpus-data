/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace BigOperators

namespace Frontier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A *density operator* on a complex Hilbert space: a self-adjoint, positive semidefinite
operator of unit trace. -/
structure IsDensityOperator (ρ : H →ₗ[ℂ] H) : Prop where
  isSymmetric : ρ.IsSymmetric
  nonneg : ∀ v : H, 0 ≤ (⟪v, ρ v⟫_ℂ).re
  trace_one : ρ.trace ℂ H = 1

/-- A *quantum measure* (a state on the lattice of closed subspaces): a nonnegative, normalized,
orthogonally additive function on subspaces. -/
structure QuantumMeasure (μ : Submodule ℂ H → ℝ) : Prop where
  nonneg : ∀ S, 0 ≤ μ S
  top : μ ⊤ = 1
  additive : ∀ S T : Submodule ℂ H, S ≤ Tᗮ → μ (S ⊔ T) = μ S + μ T

/-- The quantum measure induced by a density operator `ρ`: `S ↦ tr (ρ ∘ P_S)`, where `P_S` is
the orthogonal projection onto `S`. -/
noncomputable def traceMeasure (ρ : H →ₗ[ℂ] H) (S : Submodule ℂ H) : ℝ :=
  ((ρ ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap).trace ℂ H).re

/-- The analytic core of Gleason's theorem (valid in dimension `≥ 3`): the *frame function*
`v ↦ μ (ℂ ∙ v)` on unit vectors is the quadratic form of a self-adjoint operator. -/
def GleasonFrameProperty (μ : Submodule ℂ H → ℝ) : Prop :=
  ∃ ρ : H →ₗ[ℂ] H, ρ.IsSymmetric ∧ ∀ v : H, ‖v‖ = 1 → μ (Submodule.span ℂ {v}) = (⟪v, ρ v⟫_ℂ).re

section Auxiliary

omit [FiniteDimensional ℂ H] in
/-- The quadratic form of a symmetric operator takes real values. -/
lemma inner_self_apply_eq_ofReal {ρ : H →ₗ[ℂ] H} (h : ρ.IsSymmetric) (v : H) :
    ⟪v, ρ v⟫_ℂ = ((⟪v, ρ v⟫_ℂ).re : ℂ) := by
  have hc : (starRingEnd ℂ) ⟪v, ρ v⟫_ℂ = ⟪v, ρ v⟫_ℂ := by
    rw [inner_conj_symm]; exact h v v
  exact (Complex.conj_eq_iff_re.mp hc).symm

omit [FiniteDimensional ℂ H] in
/-- Nonnegativity of the quadratic form on unit vectors implies nonnegativity everywhere. -/
lemma nonneg_of_nonneg_on_unit {ρ : H →ₗ[ℂ] H}
    (hpos : ∀ v : H, ‖v‖ = 1 → 0 ≤ (⟪v, ρ v⟫_ℂ).re) (w : H) : 0 ≤ (⟪w, ρ w⟫_ℂ).re := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    have hv : ‖(‖w‖⁻¹ : ℂ) • w‖ = 1 := by simp [norm_smul, inv_mul_cancel₀ hn]
    have h2 := hpos _ hv
    have he : ⟪(‖w‖⁻¹ : ℂ) • w, ρ ((‖w‖⁻¹ : ℂ) • w)⟫_ℂ = ((‖w‖⁻¹ : ℝ) ^ 2 : ℝ) • ⟪w, ρ w⟫_ℂ := by
      simp [map_smul, Complex.conj_ofReal]
      ring
    rw [he] at h2
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at h2
    have hp : 0 < ‖w‖⁻¹ ^ 2 := by positivity
    nlinarith

omit [FiniteDimensional ℂ H] in
/-- Distinct members of an orthonormal family span mutually orthogonal lines. -/
lemma span_singleton_le_orthogonal_iSup {ι : Type*} [DecidableEq ι] {v : ι → H}
    (hv : Orthonormal ℂ v) (s : Finset ι) {a : ι} (ha : a ∉ s) :
    Submodule.span ℂ {v a} ≤ (⨆ i ∈ s, Submodule.span ℂ {v i})ᗮ := by
  rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_iSup_right]
  intro i
  rw [Submodule.isOrtho_iSup_right]
  intro hi
  rw [Submodule.isOrtho_span]
  rintro u hu w hw
  simp only [Set.mem_singleton_iff] at hu hw
  subst hu; subst hw
  exact hv.2 (fun h => ha (h ▸ hi))

omit [FiniteDimensional ℂ H] in
/-- An orthonormal basis of a subspace `S` spans `S`. -/
lemma iSup_span_singleton_orthonormalBasis {S : Submodule ℂ H} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ S) :
    (⨆ i ∈ (Finset.univ : Finset ι), Submodule.span ℂ {(b i : H)}) = S := by
  have h0 : (⨆ i ∈ (Finset.univ : Finset ι), Submodule.span ℂ {(b i : H)})
      = Submodule.span ℂ (Set.range fun i => (b i : H)) := by
    simp [Submodule.span_range_eq_iSup]
  rw [h0]
  have h1 : Submodule.span ℂ (Set.range fun i => (b i : S)) = ⊤ := b.toBasis.span_eq
  have h2 := congrArg (Submodule.map S.subtype) h1
  rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h2

omit [FiniteDimensional ℂ H] in
/-- The image in `H` of an orthonormal basis of a subspace is an orthonormal family. -/
lemma orthonormal_coe_orthonormalBasis {S : Submodule ℂ H} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ S) : Orthonormal ℂ fun i => (b i : H) :=
  b.orthonormal.comp_linearIsometry S.subtypeₗᵢ

/-- The orthonormal basis of the line spanned by a unit vector. -/
noncomputable def lineBasis {v : H} (hv : ‖v‖ = 1) :
    OrthonormalBasis Unit ℂ (Submodule.span ℂ {v}) :=
  OrthonormalBasis.mk (v := fun _ => (⟨v, Submodule.mem_span_singleton_self v⟩ :
      Submodule.span ℂ {v}))
    (by
      rw [orthonormal_iff_ite]
      rintro ⟨⟩ ⟨⟩
      simp [inner_self_eq_norm_sq_to_K, hv])
    (by
      rintro ⟨w, hw⟩ -
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have h : (⟨c • v, hw⟩ : Submodule.span ℂ {v})
          = c • (⟨v, Submodule.mem_span_singleton_self v⟩ : Submodule.span ℂ {v}) := rfl
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩))

omit [FiniteDimensional ℂ H] in
@[simp]
lemma lineBasis_apply {v : H} (hv : ‖v‖ = 1) (u : Unit) :
    ((lineBasis hv u : Submodule.span ℂ {v}) : H) = v := by
  simp [lineBasis]

omit [FiniteDimensional ℂ H] in
/-- A symmetric operator whose quadratic form vanishes on unit vectors is zero. -/
lemma eq_zero_of_re_inner_self_unit_eq_zero {τ : H →ₗ[ℂ] H} (hs : τ.IsSymmetric)
    (h : ∀ v : H, ‖v‖ = 1 → (⟪v, τ v⟫_ℂ).re = 0) : τ = 0 := by
  have h1 : ∀ w : H, 0 ≤ (⟪w, τ w⟫_ℂ).re :=
    nonneg_of_nonneg_on_unit fun v hv => (h v hv).ge
  have h2 : ∀ w : H, 0 ≤ (⟪w, (-τ) w⟫_ℂ).re := by
    refine nonneg_of_nonneg_on_unit fun v hv => ?_
    simp [h v hv]
  have h3 : ∀ w : H, ⟪w, τ w⟫_ℂ = 0 := by
    intro w
    have hw2 := h2 w
    simp only [LinearMap.neg_apply, inner_neg_right, Complex.neg_re, neg_nonneg] at hw2
    have : (⟪w, τ w⟫_ℂ).re = 0 := le_antisymm hw2 (h1 w)
    rw [inner_self_apply_eq_ofReal hs w, this]
    simp
  refine (hs.inner_map_self_eq_zero).mp fun x => ?_
  rw [← inner_conj_symm, h3 x, map_zero]

end Auxiliary

section QuantumMeasureLemmas

variable {μ : Submodule ℂ H → ℝ}

omit [FiniteDimensional ℂ H] in
lemma QuantumMeasure.bot (hμ : QuantumMeasure μ) : μ ⊥ = 0 := by
  have h := hμ.additive ⊥ ⊥ (by simp)
  simp only [bot_sup_eq] at h
  linarith

omit [FiniteDimensional ℂ H] in
/-- Orthogonal additivity extends to finite orthogonal families of lines. -/
lemma QuantumMeasure.sum_span_singleton (hμ : QuantumMeasure μ) {ι : Type*} [DecidableEq ι]
    {v : ι → H} (hv : Orthonormal ℂ v) (s : Finset ι) :
    μ (⨆ i ∈ s, Submodule.span ℂ {v i}) = ∑ i ∈ s, μ (Submodule.span ℂ {v i}) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hμ.bot
  | insert a s ha ih =>
      rw [Finset.iSup_insert, hμ.additive _ _ (span_singleton_le_orthogonal_iSup hv s ha),
        Finset.sum_insert ha, ih]

end QuantumMeasureLemmas

section TraceMeasureLemmas

/-- The trace of `ρ ∘ P_S`, computed in an orthonormal basis of `S`. -/
lemma trace_comp_starProjection_eq_sum {ρ : H →ₗ[ℂ] H} {S : Submodule ℂ H} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ S) :
    (ρ ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap).trace ℂ H
      = ∑ i, ⟪(b i : H), ρ (b i : H)⟫_ℂ := by
  have h1 : (ρ ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap)
      = ∑ i, (InnerProductSpace.rankOne ℂ (ρ (b i : H)) (b i : H) : H →L[ℂ] H).toLinearMap := by
    rw [b.starProjection_eq_sum_rankOne]
    ext z
    simp [Finset.sum_apply, map_sum]
  rw [h1, map_sum]
  exact Finset.sum_congr rfl fun i _ => InnerProductSpace.trace_rankOne _ _

/-- `traceMeasure ρ S` is the sum of the diagonal values of the quadratic form of `ρ` over an
orthonormal basis of `S`. -/
lemma traceMeasure_eq_sum {ρ : H →ₗ[ℂ] H} {S : Submodule ℂ H} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ S) :
    traceMeasure ρ S = ∑ i, (⟪(b i : H), ρ (b i : H)⟫_ℂ).re := by
  rw [traceMeasure, trace_comp_starProjection_eq_sum b, Complex.re_sum]

/-- The value of `traceMeasure ρ` on the line spanned by a unit vector is the quadratic form. -/
lemma traceMeasure_span_singleton (ρ : H →ₗ[ℂ] H) {v : H} (hv : ‖v‖ = 1) :
    traceMeasure ρ (Submodule.span ℂ {v}) = (⟪v, ρ v⟫_ℂ).re := by
  rw [traceMeasure_eq_sum (lineBasis hv)]
  simp

/-- Uniqueness in Gleason's theorem: a quantum measure determines its density operator. -/
theorem density_operator_unique {ρ σ : H →ₗ[ℂ] H} (hρ : ρ.IsSymmetric) (hσ : σ.IsSymmetric)
    (h : ∀ S : Submodule ℂ H, traceMeasure ρ S = traceMeasure σ S) : ρ = σ := by
  have hzero : ρ - σ = 0 := by
    refine eq_zero_of_re_inner_self_unit_eq_zero (hρ.sub hσ) fun v hv => ?_
    have hv2 := h (Submodule.span ℂ {v})
    rw [traceMeasure_span_singleton ρ hv, traceMeasure_span_singleton σ hv] at hv2
    simp only [LinearMap.sub_apply, inner_sub_right, Complex.sub_re, hv2, sub_self]
  exact sub_eq_zero.mp hzero

/-- Orthogonal projections onto orthogonal subspaces add up to the projection onto their join. -/
lemma starProjection_sup_of_le_orthogonal {S T : Submodule ℂ H} (h : S ≤ Tᗮ) :
    ((S ⊔ T).starProjection : H →L[ℂ] H) = S.starProjection + T.starProjection := by
  ext x
  simp only [ContinuousLinearMap.add_apply]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact add_mem (Submodule.mem_sup_left (Submodule.starProjection_apply_mem S x))
      (Submodule.mem_sup_right (Submodule.starProjection_apply_mem T x))
  · intro w hw
    rcases Submodule.mem_sup.mp hw with ⟨a, ha, c, hc, rfl⟩
    have hSa : ⟪x - S.starProjection x, a⟫_ℂ = 0 :=
      inner_eq_zero_symm.mp ((Submodule.sub_starProjection_mem_orthogonal x) a ha)
    have hTc : ⟪x - T.starProjection x, c⟫_ℂ = 0 :=
      inner_eq_zero_symm.mp ((Submodule.sub_starProjection_mem_orthogonal x) c hc)
    have hTa : ⟪T.starProjection x, a⟫_ℂ = 0 :=
      (Submodule.isOrtho_iff_le.mpr h).symm.inner_eq (Submodule.starProjection_apply_mem T x) ha
    have hSc : ⟪S.starProjection x, c⟫_ℂ = 0 :=
      (Submodule.isOrtho_iff_le.mpr h).inner_eq (Submodule.starProjection_apply_mem S x) hc
    simp only [inner_sub_left, inner_add_left, inner_add_right] at *
    linear_combination hSa + hTc - hTa - hSc

/-- A density operator induces a quantum measure. -/
theorem traceMeasure_isQuantumMeasure {ρ : H →ₗ[ℂ] H} (hρ : IsDensityOperator ρ) :
    QuantumMeasure (traceMeasure ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    rw [traceMeasure_eq_sum (stdOrthonormalBasis ℂ S)]
    exact Finset.sum_nonneg fun i _ => hρ.nonneg _
  · rw [traceMeasure, Submodule.starProjection_top]
    simp only [ContinuousLinearMap.coe_id]
    rw [LinearMap.comp_id, hρ.trace_one]
    simp
  · intro S T hST
    rw [traceMeasure, traceMeasure, traceMeasure, starProjection_sup_of_le_orthogonal hST]
    have : (ρ ∘ₗ ((S.starProjection + T.starProjection : H →L[ℂ] H)).toLinearMap)
        = (ρ ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap)
          + (ρ ∘ₗ (T.starProjection : H →L[ℂ] H).toLinearMap) := by
      ext z; simp
    rw [this, map_add, Complex.add_re]

@[simp]
lemma traceMeasure_bot (ρ : H →ₗ[ℂ] H) : traceMeasure ρ (⊥ : Submodule ℂ H) = 0 := by
  rw [traceMeasure]
  have h : (ρ ∘ₗ ((⊥ : Submodule ℂ H).starProjection : H →L[ℂ] H).toLinearMap) = 0 := by
    ext z; simp
  rw [h]
  simp

/-- The *maximally mixed state* `ρ = (dim H)⁻¹ • id` is a density operator; in particular
density operators, and hence quantum measures, exist on every nonzero space. -/
noncomputable def maximallyMixed (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] : H →ₗ[ℂ] H :=
  (((Module.finrank ℂ H : ℝ)⁻¹ : ℝ) : ℂ) • (LinearMap.id : H →ₗ[ℂ] H)

theorem isDensityOperator_maximallyMixed (hne : 0 < Module.finrank ℂ H) :
    IsDensityOperator (maximallyMixed H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simp [maximallyMixed, inner_smul_left, inner_smul_right]
  · intro v
    have h0 : (0 : ℝ) ≤ (⟪v, v⟫_ℂ).re := inner_self_nonneg (𝕜 := ℂ) (x := v)
    have hc : (0 : ℝ) ≤ ((Module.finrank ℂ H : ℝ)⁻¹) := by positivity
    simp only [maximallyMixed, LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hc h0
  · have hn : (Module.finrank ℂ H : ℂ) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hne.ne'
    rw [maximallyMixed, map_smul, LinearMap.trace_id, smul_eq_mul]
    push_cast
    field_simp

end TraceMeasureLemmas

section QuadraticFrame

/-- A weaker (and more primitive) form of the analytic core of Gleason's theorem: the frame
function `v ↦ μ (ℂ ∙ v)` is the quadratic form of a symmetric ℝ-bilinear form on `H`, regarded
as a real vector space. -/
def GleasonQuadraticFrameProperty (μ : Submodule ℂ H → ℝ) : Prop :=
  ∃ B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ, (∀ x y, B x y = B y x) ∧
    ∀ v : H, ‖v‖ = 1 → μ (Submodule.span ℂ {v}) = B v v

variable {B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ}

omit [FiniteDimensional ℂ H] in
/-- Phase invariance of a frame function: multiplication by `I` preserves the quadratic form. -/
lemma bilin_smul_I_self {μ : Submodule ℂ H → ℝ} (hB : ∀ v : H, ‖v‖ = 1 →
    μ (Submodule.span ℂ {v}) = B v v) (x : H) :
    B (Complex.I • x) (Complex.I • x) = B x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set u : H := (‖x‖⁻¹ : ℝ) • x with hu
    have hnu : ‖u‖ = 1 := norm_smul_inv_norm hx
    have hnIu : ‖Complex.I • u‖ = 1 := by rw [norm_smul, hnu]; simp
    have hspan : Submodule.span ℂ {Complex.I • u} = Submodule.span ℂ {u} :=
      Submodule.span_singleton_smul_eq (IsUnit.mk0 _ Complex.I_ne_zero) _
    have hkey : B (Complex.I • u) (Complex.I • u) = B u u := by
      rw [← hB _ hnIu, ← hB _ hnu, hspan]
    have hxu : x = (‖x‖ : ℝ) • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
    calc B (Complex.I • x) (Complex.I • x)
        = B ((‖x‖ : ℝ) • (Complex.I • u)) ((‖x‖ : ℝ) • (Complex.I • u)) := by
          rw [← smul_comm, ← hxu]
      _ = ‖x‖ * (‖x‖ * B (Complex.I • u) (Complex.I • u)) := by simp [map_smul]
      _ = ‖x‖ * (‖x‖ * B u u) := by rw [hkey]
      _ = B x x := by
          conv_rhs => rw [hxu]
          simp [map_smul]

omit [FiniteDimensional ℂ H] in
/-- Phase invariance of the associated bilinear form. -/
lemma bilin_smul_I (hs : ∀ x y, B x y = B y x)
    (hq : ∀ x : H, B (Complex.I • x) (Complex.I • x) = B x x) (x y : H) :
    B (Complex.I • x) (Complex.I • y) = B x y := by
  have h := hq (x + y)
  rw [smul_add] at h
  simp only [map_add, LinearMap.add_apply] at h
  have h1 := hq x
  have h2 := hq y
  have h3 : B (Complex.I • y) (Complex.I • x) = B (Complex.I • x) (Complex.I • y) := hs _ _
  have h4 : B y x = B x y := hs _ _
  linarith

omit [FiniteDimensional ℂ H] in
lemma bilin_smul_I_left (hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y) (x y : H) :
    B (Complex.I • x) y = - B x (Complex.I • y) := by
  have h := hI x ((-Complex.I) • y)
  have e1 : (Complex.I • ((-Complex.I) • y) : H) = y := by
    rw [smul_smul]; norm_num
  rw [e1] at h
  rw [h, show ((-Complex.I) • y : H) = -(Complex.I • y) by simp, map_neg]

omit [FiniteDimensional ℂ H] in
lemma bilin_self_smul_I (hs : ∀ x y, B x y = B y x)
    (hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y) (x : H) :
    B x (Complex.I • x) = 0 := by
  have h := bilin_smul_I_left hI x x
  have h2 : B (Complex.I • x) x = B x (Complex.I • x) := hs _ _
  linarith

/-- The sesquilinear form associated with a phase-invariant symmetric real bilinear form. -/
noncomputable def sesqOfBilin (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (x y : H) : ℂ :=
  (B x y : ℂ) - Complex.I * (B x (Complex.I • y) : ℂ)

omit [FiniteDimensional ℂ H] in
lemma sesqOfBilin_add_right (x y z : H) :
    sesqOfBilin B x (y + z) = sesqOfBilin B x y + sesqOfBilin B x z := by
  simp [sesqOfBilin, smul_add]
  ring

omit [FiniteDimensional ℂ H] in
lemma sesqOfBilin_smul_right (c : ℂ) (x y : H) :
    sesqOfBilin B x (c • y) = c * sesqOfBilin B x y := by
  have hII : (Complex.I • (Complex.I • y) : H) = -y := by rw [smul_smul]; norm_num
  have hlin : ∀ w : H, B x (c • w) = c.re * B x w + c.im * B x (Complex.I • w) := by
    intro w
    have hy : c • w = (c.re : ℝ) • w + (c.im : ℝ) • (Complex.I • w) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
        smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im c).symm
    rw [hy, map_add, map_smul, map_smul]
    simp
  have h1 : B x (c • y) = c.re * B x y + c.im * B x (Complex.I • y) := hlin y
  have h2 : B x (Complex.I • (c • y)) = c.re * B x (Complex.I • y) - c.im * B x y := by
    rw [smul_comm, hlin (Complex.I • y), hII, map_neg]
    ring
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [sesqOfBilin, sesqOfBilin, h1, h2]
  push_cast
  linear_combination (-((B x y : ℂ) - Complex.I * (B x (Complex.I • y) : ℂ))) * hc
    + ((c.im : ℂ) * (B x (Complex.I • y) : ℂ)) * Complex.I_sq

omit [FiniteDimensional ℂ H] in
lemma sesqOfBilin_add_left (x y z : H) :
    sesqOfBilin B (x + y) z = sesqOfBilin B x z + sesqOfBilin B y z := by
  simp [sesqOfBilin]
  ring

omit [FiniteDimensional ℂ H] in
lemma sesqOfBilin_zero_left (y : H) : sesqOfBilin B 0 y = 0 := by
  simp [sesqOfBilin]

omit [FiniteDimensional ℂ H] in
lemma sesqOfBilin_smul_left (hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y)
    (c : ℂ) (x y : H) :
    sesqOfBilin B (c • x) y = (starRingEnd ℂ) c * sesqOfBilin B x y := by
  have hII : (Complex.I • (Complex.I • y) : H) = -y := by rw [smul_smul]; norm_num
  have hlin : ∀ w : H, B (c • x) w = c.re * B x w - c.im * B x (Complex.I • w) := by
    intro w
    have hy : c • x = (c.re : ℝ) • x + (c.im : ℝ) • (Complex.I • x) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
        smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im c).symm
    rw [hy, map_add, map_smul, map_smul]
    simp [bilin_smul_I_left hI x w]
    ring
  have h1 : B (c • x) y = c.re * B x y - c.im * B x (Complex.I • y) := hlin y
  have h2 : B (c • x) (Complex.I • y) = c.re * B x (Complex.I • y) + c.im * B x y := by
    rw [hlin (Complex.I • y), hII, map_neg]
    ring
  have hc : (starRingEnd ℂ) c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [sesqOfBilin, sesqOfBilin, h1, h2, hc]
  push_cast
  linear_combination (-((c.im : ℂ) * (B x (Complex.I • y) : ℂ))) * Complex.I_sq

omit [FiniteDimensional ℂ H] in
lemma sesqOfBilin_hermitian (hs : ∀ x y, B x y = B y x)
    (hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y) (x y : H) :
    sesqOfBilin B y x = (starRingEnd ℂ) (sesqOfBilin B x y) := by
  have h1 : B y x = B x y := hs _ _
  have h2 : B y (Complex.I • x) = - B x (Complex.I • y) := by
    rw [hs y (Complex.I • x)]
    exact bilin_smul_I_left hI x y
  simp only [sesqOfBilin, h1, h2]
  apply Complex.ext <;> simp

omit [FiniteDimensional ℂ H] in
lemma sesqOfBilin_self (hs : ∀ x y, B x y = B y x)
    (hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y) (x : H) :
    sesqOfBilin B x x = (B x x : ℂ) := by
  rw [sesqOfBilin, bilin_self_smul_I hs hI x]
  simp

omit [FiniteDimensional ℂ H] in
lemma sesqOfBilin_sum_left (hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → H) (y : H) :
    sesqOfBilin B (∑ i ∈ s, c i • w i) y
      = ∑ i ∈ s, (starRingEnd ℂ) (c i) * sesqOfBilin B (w i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sesqOfBilin_zero_left]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, sesqOfBilin_add_left, sesqOfBilin_smul_left hI, ih,
        Finset.sum_insert ha]

/-- A phase-invariant symmetric real bilinear form is represented by a complex linear operator. -/
lemma exists_operator_of_bilin (hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y) :
    ∃ ρ : H →ₗ[ℂ] H, ∀ x y : H, ⟪x, ρ y⟫_ℂ = sesqOfBilin B x y := by
  classical
  set e := stdOrthonormalBasis ℂ H with he
  refine ⟨∑ i, LinearMap.smulRight
      ({ toFun := fun y => sesqOfBilin B (e i) y
         map_add' := fun y z => sesqOfBilin_add_right _ _ _
         map_smul' := fun c y => by simpa using sesqOfBilin_smul_right c (e i) y } :
        H →ₗ[ℂ] ℂ) (e i), ?_⟩
  intro x y
  have hxe : x = ∑ i, ⟪e i, x⟫_ℂ • e i := (e.sum_repr' x).symm
  have hrhs : sesqOfBilin B x y
      = ∑ i, (starRingEnd ℂ) (⟪e i, x⟫_ℂ) * sesqOfBilin B (e i) y := by
    conv_lhs => rw [hxe]
    exact sesqOfBilin_sum_left hI _ _ _ y
  rw [hrhs]
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.coe_mk,
    AddHom.coe_mk, inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← inner_conj_symm (e i) x]
  simp [mul_comm]

/-- **Reduction of Gleason's theorem to the quadratic form property.**  If the frame function of
`μ` is a symmetric real quadratic form, then it is the quadratic form of a self-adjoint complex
operator. -/
theorem gleasonFrameProperty_of_quadratic {μ : Submodule ℂ H → ℝ}
    (h : GleasonQuadraticFrameProperty μ) : GleasonFrameProperty μ := by
  obtain ⟨B, hs, hB⟩ := h
  have hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y :=
    bilin_smul_I hs (bilin_smul_I_self hB)
  obtain ⟨ρ, hρ⟩ := exists_operator_of_bilin hI
  refine ⟨ρ, ?_, ?_⟩
  · intro x y
    have h0 : (starRingEnd ℂ) ⟪y, ρ x⟫_ℂ = ⟪ρ x, y⟫_ℂ := inner_conj_symm _ _
    have h1 : ⟪ρ x, y⟫_ℂ = (starRingEnd ℂ) (sesqOfBilin B y x) := by
      rw [← h0, hρ y x]
    rw [h1, sesqOfBilin_hermitian hs hI x y]
    simp [hρ x y]
  · intro v hv
    rw [hρ v v, sesqOfBilin_self hs hI v, Complex.ofReal_re]
    exact hB v hv

end QuadraticFrame

/-- **Gleason's theorem** (reduction to its analytic core).

Let `H` be a complex Hilbert space of dimension at least `3` and let `μ` be a quantum measure on
the lattice of subspaces of `H`.  Granting the analytic core of Gleason's theorem
(`GleasonFrameProperty`: the associated frame function on unit vectors is the quadratic form of a
self-adjoint operator — exactly the step that fails in dimension `2`), the measure `μ` comes from
a density operator: there is a density operator `ρ` with `μ S = tr (ρ P_S)` for every subspace `S`.

The dimension hypothesis `hdim` enters only through the core hypothesis and is therefore not used
in this reduction; it is kept because it is part of the statement of Gleason's theorem. -/
theorem gleason_theorem (hdim : 3 ≤ Module.finrank ℂ H) (μ : Submodule ℂ H → ℝ)
    (hμ : QuantumMeasure μ) (hcore : GleasonFrameProperty μ) :
    ∃ ρ : H →ₗ[ℂ] H, IsDensityOperator ρ ∧ ∀ S : Submodule ℂ H, μ S = traceMeasure ρ S := by
  classical
  obtain ⟨ρ, hsymm, hframe⟩ := hcore
  -- the measure of any subspace is the trace of `ρ` against its projection
  have key : ∀ S : Submodule ℂ H, μ S = traceMeasure ρ S := by
    intro S
    set b := stdOrthonormalBasis ℂ S with hb
    have hspan := iSup_span_singleton_orthonormalBasis b
    have horth := orthonormal_coe_orthonormalBasis b
    have hsum := hμ.sum_span_singleton horth (Finset.univ)
    rw [hspan] at hsum
    rw [hsum, traceMeasure_eq_sum b]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hframe _ (b.norm_eq_one i)
  refine ⟨ρ, ⟨hsymm, ?_, ?_⟩, key⟩
  · refine nonneg_of_nonneg_on_unit (fun v hv => ?_)
    rw [← hframe v hv]
    exact hμ.nonneg _
  · have htop := key ⊤
    rw [traceMeasure, Submodule.starProjection_top] at htop
    simp only [ContinuousLinearMap.coe_id, LinearMap.comp_id] at htop
    rw [hμ.top] at htop
    have hre : (ρ.trace ℂ H).re = 1 := htop.symm
    -- the trace is real because `ρ` is symmetric
    have hreal : ρ.trace ℂ H = ((ρ.trace ℂ H).re : ℂ) := by
      rw [LinearMap.trace_eq_sum_inner ρ (stdOrthonormalBasis ℂ H), Complex.re_sum,
        Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => inner_self_apply_eq_ofReal hsymm _
    rw [hreal, hre]
    norm_num

/-- **The base case of Gleason's theorem, in dimension one.**  Here no analytic input is needed:
the only subspaces are `⊥` and `⊤`, and every quantum measure is the one induced by the
identity operator. -/
theorem gleason_theorem_dim_one (hdim : Module.finrank ℂ H = 1) (μ : Submodule ℂ H → ℝ)
    (hμ : QuantumMeasure μ) :
    ∃ ρ : H →ₗ[ℂ] H, IsDensityOperator ρ ∧ ∀ S : Submodule ℂ H, μ S = traceMeasure ρ S := by
  have hpos : 0 < Module.finrank ℂ H := by omega
  refine ⟨maximallyMixed H, isDensityOperator_maximallyMixed hpos, fun S => ?_⟩
  rcases eq_or_ne S ⊥ with rfl | hS
  · rw [hμ.bot, traceMeasure_bot]
  · have hST : S = ⊤ := by
      have h1 : 0 < Module.finrank ℂ S :=
        Nat.pos_of_ne_zero fun h => hS (Submodule.finrank_eq_zero.mp h)
      have h2 : Module.finrank ℂ S ≤ Module.finrank ℂ H := Submodule.finrank_le S
      exact Submodule.eq_top_of_finrank_eq (by omega)
    rw [hST, hμ.top, (traceMeasure_isQuantumMeasure
      (isDensityOperator_maximallyMixed hpos)).top]

/-- **Gleason's theorem from the weaker (quadratic form) core hypothesis.**  If the frame
function of a quantum measure `μ` is a symmetric real quadratic form, then `μ` comes from a
density operator.  As in `gleason_theorem`, the dimension hypothesis is part of the classical
statement but enters only through the core hypothesis. -/
theorem gleason_theorem_of_quadratic (hdim : 3 ≤ Module.finrank ℂ H) (μ : Submodule ℂ H → ℝ)
    (hμ : QuantumMeasure μ) (hcore : GleasonQuadraticFrameProperty μ) :
    ∃ ρ : H →ₗ[ℂ] H, IsDensityOperator ρ ∧ ∀ S : Submodule ℂ H, μ S = traceMeasure ρ S :=
  gleason_theorem hdim μ hμ (gleasonFrameProperty_of_quadratic hcore)

end Frontier

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

