import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
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

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The real quadratic form `x ↦ re ⟪x, M x⟫` associated to a matrix `M`. -/
noncomputable def qform (M : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  RCLike.re (inner ℂ x (Matrix.toEuclideanLin M x))

/-- The number of eigenvalues of a Hermitian matrix that are strictly above `theta`. -/
noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (theta : ℝ) : ℕ :=
  (Finset.univ.filter fun i => theta < hA.eigenvalues i).card

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def posIndex {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  posIndexAbove hA 0

/-- Eigenvectors of a Hermitian matrix, viewed in `EuclideanSpace`, are eigenvectors of the
associated linear map. -/
lemma toEuclideanLin_eigenvectorBasis {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (i : Fin d) :
    Matrix.toEuclideanLin M (hM.eigenvectorBasis i)
      = ((hM.eigenvalues i : ℂ)) • hM.eigenvectorBasis i := by
  ext j
  simp [hM.mulVec_eigenvectorBasis]

/-- Spectral expansion of the quadratic form of a Hermitian matrix. -/
lemma qform_eq {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    qform M x = ∑ i, hM.eigenvalues i * ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 := by
  have hx : x = ∑ i, inner ℂ (hM.eigenvectorBasis i) x • hM.eigenvectorBasis i :=
    (hM.eigenvectorBasis.sum_repr' x).symm
  have key : Matrix.toEuclideanLin M x
      = ∑ i, ((hM.eigenvalues i : ℂ) * inner ℂ (hM.eigenvectorBasis i) x)
          • hM.eigenvectorBasis i := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, toEuclideanLin_eigenvectorBasis hM, smul_smul, mul_comm]
  rw [qform, key, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, ← inner_conj_symm x, mul_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow]
  show (((hM.eigenvalues i : ℝ) : ℂ) * ((‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 : ℝ) : ℂ)).re = _
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

lemma qform_add (A E : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    qform (A + E) x = qform A x + qform E x := by
  simp [qform, map_add]

/-- If all eigenvalues of a Hermitian matrix are at most `c`, its quadratic form is bounded by
`c * ‖x‖ ^ 2`. -/
lemma qform_le {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) {c : ℝ}
    (h : ∀ i, hM.eigenvalues i ≤ c) (x : EuclideanSpace ℂ (Fin d)) :
    qform M x ≤ c * ‖x‖ ^ 2 := by
  rw [qform_eq hM, ← hM.eigenvectorBasis.sum_sq_norm_inner_right x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h2 : (0:ℝ) ≤ ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right (h i) h2

/-- On the span of eigenvectors with nonpositive eigenvalues, the quadratic form is nonpositive. -/
lemma qform_nonpos_of_inner_eq_zero {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) (h : ∀ i ∈ s, hM.eigenvalues i ≤ 0)
    {x : EuclideanSpace ℂ (Fin d)} (hx : ∀ i ∉ s, inner ℂ (hM.eigenvectorBasis i) x = 0) :
    qform M x ≤ 0 := by
  rw [qform_eq hM]
  refine Finset.sum_nonpos fun i _ => ?_
  by_cases hi : i ∈ s
  · exact mul_nonpos_of_nonpos_of_nonneg (h i hi) (by positivity)
  · simp [hx i hi]

/-- On the span of eigenvectors with eigenvalues strictly above `c`, the quadratic form is
strictly above `c * ‖x‖ ^ 2` for nonzero vectors. -/
lemma qform_gt_of_inner_eq_zero {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) {c : ℝ} (h : ∀ i ∈ s, c < hM.eigenvalues i)
    {x : EuclideanSpace ℂ (Fin d)} (hx : ∀ i ∉ s, inner ℂ (hM.eigenvectorBasis i) x = 0)
    (hx0 : x ≠ 0) :
    c * ‖x‖ ^ 2 < qform M x := by
  set t : Fin d → ℝ := fun i => ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 with ht
  have hsum : ∑ i, t i = ‖x‖ ^ 2 := hM.eigenvectorBasis.sum_sq_norm_inner_right x
  have hpos : 0 < ∑ i, (hM.eigenvalues i - c) * t i := by
    refine Finset.sum_pos' (fun i _ => ?_) ?_
    · by_cases hi : i ∈ s
      · exact mul_nonneg (by linarith [h i hi]) (by positivity)
      · simp [ht, hx i hi]
    · have hxn : 0 < ‖x‖ ^ 2 := by positivity
      rw [← hsum] at hxn
      obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt
        (by simpa using hxn : ∑ _i : Fin d, (0:ℝ) < ∑ i, t i)
      have hmem : i ∈ s := by
        by_contra hc
        simp [ht, hx i hc] at hi
      exact ⟨i, Finset.mem_univ i, mul_pos (by linarith [h i hmem]) hi⟩
  rw [qform_eq hM]
  have hrw : ∑ i, (hM.eigenvalues i - c) * t i = (∑ i, hM.eigenvalues i * t i) - c * ‖x‖ ^ 2 := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith [hrw ▸ hpos]

/-- A vector in the span of a subfamily of an orthonormal basis is orthogonal to the remaining
basis vectors. -/
lemma inner_eq_zero_of_mem_span
    (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (s : Finset (Fin d))
    {x : EuclideanSpace ℂ (Fin d)} (hx : x ∈ Submodule.span ℂ (b '' (s : Set (Fin d))))
    {i : Fin d} (hi : i ∉ s) : inner ℂ (b i) x = 0 := by
  have hle : Submodule.span ℂ (b '' (s : Set (Fin d)))
      ≤ LinearMap.ker ((innerSL ℂ (b i) : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ) : _ →ₗ[ℂ] ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [LinearMap.mem_ker, b.orthonormal.2 hij]
  simpa using hle hx

/-- The span of a subfamily of an orthonormal basis has dimension equal to the number of vectors
in the subfamily. -/
lemma finrank_span_image
    (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (s : Finset (Fin d)) :
    Module.finrank ℂ (Submodule.span ℂ (b '' (s : Set (Fin d)))) = s.card := by
  have hli : LinearIndependent ℂ (fun i : (s : Finset (Fin d)) => b i) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range (fun i : (s : Finset (Fin d)) => b i) = b '' (s : Set (Fin d)) := by
    ext y; simp [Set.mem_image]
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_coe]

/-- **Weyl monotonicity**: if all eigenvalues of the Hermitian perturbation `E` are bounded in
absolute value by `theta`, then the number of eigenvalues of `A + E` strictly above `theta` is at
most the number of strictly positive eigenvalues of `A`. -/
theorem weyl_posIndexAbove {A E : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (theta : ℝ)
    (hbound : ∀ i, |hE.eigenvalues i| ≤ theta) :
    posIndexAbove (hA.add hE) theta ≤ posIndex hA := by
  classical
  set hAE : (A + E).IsHermitian := hA.add hE with hAEdef
  set S₁ : Finset (Fin d) := Finset.univ.filter fun i => theta < hAE.eigenvalues i with hS1
  set P₁ : Finset (Fin d) := Finset.univ.filter fun i => 0 < hA.eigenvalues i with hP1
  set T₁ : Finset (Fin d) := Finset.univ.filter fun i => ¬ (0 < hA.eigenvalues i) with hT1
  set S : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    Submodule.span ℂ (hAE.eigenvectorBasis '' (S₁ : Set (Fin d))) with hSdef
  set T : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    Submodule.span ℂ (hA.eigenvectorBasis '' (T₁ : Set (Fin d))) with hTdef
  have hdisj : S ⊓ T = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hxm
    by_contra hx0
    obtain ⟨hxS, hxT⟩ := Submodule.mem_inf.1 hxm
    have h1 : theta * ‖x‖ ^ 2 < qform (A + E) x :=
      qform_gt_of_inner_eq_zero hAE S₁
        (fun i hi => by simpa [hS1] using hi)
        (fun i hi => inner_eq_zero_of_mem_span _ _ hxS hi) hx0
    have h2 : qform E x ≤ theta * ‖x‖ ^ 2 :=
      qform_le hE (fun i => (abs_le.1 (hbound i)).2) x
    have h3 : qform A x ≤ 0 :=
      qform_nonpos_of_inner_eq_zero hA T₁
        (fun i hi => by
          have := (Finset.mem_filter.1 (hT1 ▸ hi)).2
          linarith [not_lt.1 this])
        (fun i hi => inner_eq_zero_of_mem_span _ _ hxT hi)
    rw [qform_add] at h1
    linarith
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [hdisj] at hfr
  have hle : Module.finrank ℂ (S ⊔ T : Submodule ℂ (EuclideanSpace ℂ (Fin d))) ≤ d := by
    have h := Submodule.finrank_le (S ⊔ T)
    rwa [finrank_euclideanSpace_fin] at h
  have hSc : Module.finrank ℂ S = S₁.card := finrank_span_image _ _
  have hTc : Module.finrank ℂ T = T₁.card := finrank_span_image _ _
  have hcard : P₁.card + T₁.card = d := by
    rw [hP1, hT1, Finset.card_filter_add_card_filter_not]
    simp
  have hbot : Module.finrank ℂ (⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin d))) = 0 := by simp
  rw [hbot, hSc, hTc] at hfr
  show S₁.card ≤ P₁.card
  omega

end Zeta23Redux.LinAlg

