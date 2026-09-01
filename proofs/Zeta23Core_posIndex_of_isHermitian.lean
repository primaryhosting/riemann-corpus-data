import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
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

/-!
## Inertia does not increase under compression

For a Hermitian matrix `Q` on a finite type `m` and a rectangular matrix `B : Matrix m d 𝕜`, the
compression `Bᴴ * Q * B` is Hermitian and its positive index of inertia (the number of positive
eigenvalues, counted with multiplicity) is at most that of `Q`.

The proof follows the variational route.  Writing `qform Q x = Re (xᴴ Q x)`, we prove both
directions of the (finite dimensional) Sylvester characterisation of the positive index:

* `Zeta23Core.exists_posdef_matrix`: the column space of `U * posProj` — where `U` diagonalises `Q`
  and `posProj` projects onto the positive eigen-directions — is a subspace of dimension
  `posIndex Q` on which `qform Q` is positive definite;
* `Zeta23Core.finrank_le_posIndex`: any subspace on which `qform Q` is positive definite has
  dimension at most `posIndex Q` (it meets the "non-positive" subspace `ker (posProj * Uᴴ)`
  trivially, and that kernel has codimension `posIndex Q`).

For the compression, such a subspace for `Bᴴ Q B` is pushed forward by `B`; injectivity on it is
forced by positive definiteness, so the dimension is preserved.
-/

namespace Zeta23Core

open Matrix Module

section Defs

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The (real) quadratic form `x ↦ Re (xᴴ Q x)` attached to a matrix `Q`. -/
noncomputable def qform (Q : Matrix n n 𝕜) (x : n → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ Q *ᵥ x)

/-- The positive index of inertia of a Hermitian matrix: the number of positive eigenvalues,
counted with multiplicity.  (It is set to `0` for non-Hermitian matrices.) -/
noncomputable def posIndex (Q : Matrix n n 𝕜) : ℕ :=
  if h : Q.IsHermitian then Nat.card {i // 0 < h.eigenvalues i} else 0

lemma posIndex_of_isHermitian {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    posIndex Q = Nat.card {i // 0 < hQ.eigenvalues i} := dif_pos hQ

omit [DecidableEq n] in
lemma qform_zero (Q : Matrix n n 𝕜) : qform Q 0 = 0 := by
  simp [qform]

omit [DecidableEq n] in
/-- Behaviour of the quadratic form under congruence. -/
lemma qform_conj {p : Type*} [Fintype p] (M : Matrix n n 𝕜) (A : Matrix n p 𝕜) (x : p → 𝕜) :
    qform (Aᴴ * M * A) x = qform M (A *ᵥ x) := by
  unfold qform
  congr 1
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

/-- The quadratic form of a real diagonal matrix. -/
lemma qform_diagonal (w : n → ℝ) (y : n → 𝕜) :
    qform (diagonal (fun i => (RCLike.ofReal (w i) : 𝕜))) y = ∑ i, w i * ‖y i‖ ^ 2 := by
  unfold qform
  rw [dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [RCLike.star_def, Pi.star_apply, RCLike.mul_re, RCLike.mul_im, RCLike.conj_re,
    RCLike.conj_im, RCLike.ofReal_re, RCLike.ofReal_im]
  rw [RCLike.norm_sq_eq_def (z := y i)]
  ring

/-- Diagonalisation of the quadratic form of a Hermitian matrix. -/
lemma qform_eq_sum {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) (x : n → 𝕜) :
    qform Q x =
      ∑ i, hQ.eigenvalues i * ‖(star (hQ.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  have hU : ((star (hQ.eigenvectorUnitary : Matrix n n 𝕜))ᴴ)
      = (hQ.eigenvectorUnitary : Matrix n n 𝕜) := by
    simp [Matrix.star_eq_conjTranspose]
  have hspec : Q = (star (hQ.eigenvectorUnitary : Matrix n n 𝕜))ᴴ *
      diagonal (fun i => (RCLike.ofReal (hQ.eigenvalues i) : 𝕜)) *
      (star (hQ.eigenvectorUnitary : Matrix n n 𝕜)) := by
    rw [hU]
    exact hQ.spectral_theorem
  conv_lhs => rw [hspec]
  rw [qform_conj, qform_diagonal]

/-- The diagonal matrix projecting onto the positive eigen-directions of `Q`. -/
noncomputable def posProj {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) : Matrix n n 𝕜 :=
  diagonal (fun i => if 0 < hQ.eigenvalues i then (1 : 𝕜) else 0)

lemma rank_posProj {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    (posProj hQ).rank = posIndex Q := by
  rw [posProj, Matrix.rank_diagonal, posIndex_of_isHermitian hQ, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (by intro i; simp))

/-- **Easy direction of Sylvester's law**: there is a matrix whose column space is a subspace of
dimension `posIndex Q` on which the form of `Q` is positive definite. -/
lemma exists_posdef_matrix {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    ∃ C : Matrix n n 𝕜, C.rank = posIndex Q ∧ ∀ c : n → 𝕜, C *ᵥ c ≠ 0 → 0 < qform Q (C *ᵥ c) := by
  set U : Matrix n n 𝕜 := (hQ.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  refine ⟨U * posProj hQ, ?_, ?_⟩
  · rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit _),
      rank_posProj]
  · intro c hc
    have hy : star U *ᵥ ((U * posProj hQ) *ᵥ c) = posProj hQ *ᵥ c := by
      rw [mulVec_mulVec, ← Matrix.mul_assoc, UnitaryGroup.star_mul_self, Matrix.one_mul]
    rw [qform_eq_sum hQ, ← hUdef, hy]
    have hne : posProj hQ *ᵥ c ≠ 0 := by
      intro h
      exact hc (by rw [← mulVec_mulVec, h, mulVec_zero])
    obtain ⟨j, hj⟩ : ∃ j, (posProj hQ *ᵥ c) j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hjpos : 0 < hQ.eigenvalues j := by
      by_contra h
      exact hj (by simp [posProj, mulVec_diagonal, h])
    refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · rcases lt_or_ge 0 (hQ.eigenvalues i) with h | h
      · positivity
      · have hz : (posProj hQ *ᵥ c) i = 0 := by simp [posProj, mulVec_diagonal, not_lt.2 h]
        simp [hz]
    · have hpos : (0 : ℝ) < ‖(posProj hQ *ᵥ c) j‖ ^ 2 := by positivity
      exact mul_pos hjpos hpos

/-- **Hard direction of Sylvester's law**: any subspace on which the form of `Q` is positive
definite has dimension at most `posIndex Q`. -/
lemma finrank_le_posIndex {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian)
    (S : Submodule 𝕜 (n → 𝕜)) (hS : ∀ x ∈ S, x ≠ 0 → 0 < qform Q x) :
    finrank 𝕜 S ≤ posIndex Q := by
  set U : Matrix n n 𝕜 := (hQ.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  have hdet : IsUnit (star U).det := by
    simpa [hUdef] using Matrix.UnitaryGroup.det_isUnit (star hQ.eigenvectorUnitary)
  set G : Matrix n n 𝕜 := posProj hQ * star U with hG
  set f : (n → 𝕜) →ₗ[𝕜] (n → 𝕜) := Matrix.mulVecLin G with hf
  have hker : ∀ x ∈ LinearMap.ker f, qform Q x ≤ 0 := by
    intro x hx
    rw [LinearMap.mem_ker, hf, Matrix.mulVecLin_apply, hG, ← mulVec_mulVec] at hx
    rw [qform_eq_sum hQ, ← hUdef]
    refine Finset.sum_nonpos fun i _ => ?_
    rcases lt_or_ge 0 (hQ.eigenvalues i) with h | h
    · have hz : (star U *ᵥ x) i = 0 := by
        simpa [posProj, mulVec_diagonal, h] using congrFun hx i
      simp [hz]
    · have hnn : (0 : ℝ) ≤ ‖(star U *ᵥ x) i‖ ^ 2 := by positivity
      exact mul_nonpos_of_nonpos_of_nonneg h hnn
  have hdisj : Disjoint S (LinearMap.ker f) := by
    rw [Submodule.disjoint_def]
    intro x hxS hxK
    by_contra hx
    exact absurd (hS x hxS hx) (not_lt.2 (hker x hxK))
  have h1 := Submodule.finrank_add_finrank_le_of_disjoint (K := 𝕜) (V := n → 𝕜) hdisj
  have h2 := LinearMap.finrank_range_add_finrank_ker (K := 𝕜) f
  have h3 : finrank 𝕜 (LinearMap.range f) = posIndex Q := by
    rw [← rank_posProj hQ]
    change G.rank = _
    rw [hG, Matrix.rank_mul_eq_left_of_isUnit_det (star U) (posProj hQ) hdet]
  omega

end Defs

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m]
  [Fintype d] [DecidableEq d]

omit [DecidableEq m] [Fintype d] [DecidableEq d] in
/-- A compression of a Hermitian matrix is Hermitian. -/
theorem isHermitian_conj {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul B hQ

/-- **Inertia does not increase under compression**: `n₊(Bᴴ Q B) ≤ n₊(Q)`. -/
theorem posIndex_conj_le {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    posIndex (Bᴴ * Q * B) ≤ posIndex Q := by
  obtain ⟨C, hCrank, hCpos⟩ := exists_posdef_matrix (isHermitian_conj hQ B)
  set G : Matrix m d 𝕜 := B * C with hG
  have hGC : ∀ c : d → 𝕜, G *ᵥ c = B *ᵥ (C *ᵥ c) := fun c => by rw [hG, mulVec_mulVec]
  have hqG : ∀ c : d → 𝕜, qform Q (G *ᵥ c) = qform (Bᴴ * Q * B) (C *ᵥ c) := fun c => by
    rw [hGC, qform_conj]
  have hCne : ∀ c : d → 𝕜, G *ᵥ c ≠ 0 → C *ᵥ c ≠ 0 := by
    intro c hc h0
    exact hc (by rw [hGC, h0, mulVec_zero])
  have hkereq : LinearMap.ker (Matrix.mulVecLin G) = LinearMap.ker (Matrix.mulVecLin C) := by
    apply le_antisymm
    · intro c hc
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc ⊢
      by_contra h
      have hpos := hCpos c h
      rw [← hqG c, hc, qform_zero] at hpos
      exact lt_irrefl _ hpos
    · intro c hc
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc ⊢
      rw [hGC, hc, mulVec_zero]
  have hrank : G.rank = C.rank := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (K := 𝕜) (Matrix.mulVecLin G)
    have h2 := LinearMap.finrank_range_add_finrank_ker (K := 𝕜) (Matrix.mulVecLin C)
    rw [hkereq] at h1
    unfold Matrix.rank
    omega
  have hSpos : ∀ x ∈ LinearMap.range (Matrix.mulVecLin G), x ≠ 0 → 0 < qform Q x := by
    rintro x ⟨c, rfl⟩ hx
    simp only [Matrix.mulVecLin_apply] at hx ⊢
    rw [hqG c]
    exact hCpos c (hCne c hx)
  have hle := finrank_le_posIndex hQ _ hSpos
  rwa [show finrank 𝕜 (LinearMap.range (Matrix.mulVecLin G)) = G.rank from rfl, hrank,
    hCrank] at hle

/-- Sanity check (non-vacuity): the positive index of the `3 × 3` identity matrix is `3`. -/
theorem posIndex_one_fin_three : posIndex (1 : Matrix (Fin 3) (Fin 3) ℂ) = 3 := by
  have hH : (1 : Matrix (Fin 3) (Fin 3) ℂ).IsHermitian := Matrix.isHermitian_one
  have key : ∀ z : ℂ, ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
    intro z; simp [Complex.mul_re, Complex.normSq_apply]
  have hpos : ∀ x ∈ (⊤ : Submodule ℂ (Fin 3 → ℂ)), x ≠ 0 →
      0 < qform (1 : Matrix (Fin 3) (Fin 3) ℂ) x := by
    intro x _ hx
    unfold qform
    rw [one_mulVec]
    have hd : star x ⬝ᵥ x = ∑ i, (starRingEnd ℂ) (x i) * x i := rfl
    rw [hd, map_sum]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
    exact Finset.sum_pos'
      (fun i _ => by rw [RCLike.re_to_complex, key]; exact Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ j, by rw [RCLike.re_to_complex, key]; exact Complex.normSq_pos.mpr hj⟩
  have h1 := finrank_le_posIndex hH ⊤ hpos
  have h2 : posIndex (1 : Matrix (Fin 3) (Fin 3) ℂ) ≤ 3 := by
    rw [posIndex_of_isHermitian hH]
    calc Nat.card {i // 0 < hH.eigenvalues i} ≤ Nat.card (Fin 3) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 3 := by simp
  simp at h1
  omega

end Zeta23Core

