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

open Matrix

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The real quadratic form attached to a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/
noncomputable def qf {m : Type*} [Fintype m] (Q : Matrix m m 𝕜) (x : m → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ Q *ᵥ x)

/-- Compressing the matrix is the same as restricting the quadratic form. -/
theorem qf_conj {m d : Type*} [Fintype m] [Fintype d] (Q : Matrix m m 𝕜) (B : Matrix m d 𝕜)
    (y : d → 𝕜) : qf Q (B *ᵥ y) = qf (Bᴴ * Q * B) y := by
  unfold qf
  rw [Matrix.mul_assoc]
  simp [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec]

/-- The quadratic form of a real diagonal matrix. -/
theorem qf_diagonal {m : Type*} [Fintype m] [DecidableEq m] (l : m → ℝ) (y : m → 𝕜) :
    qf (Matrix.diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ l)) y = ∑ i, l i * ‖y i‖ ^ 2 := by
  unfold qf
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def,
    Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (starRingEnd 𝕜) (y i) * ((l i : 𝕜) * y i)
      = (l i : 𝕜) * ((starRingEnd 𝕜) (y i) * y i) by ring, RCLike.conj_mul]
  simp

/-- Diagonalization of the quadratic form of a Hermitian matrix: in the coordinates given by
the eigenvector unitary, the form is the weighted sum of squares with the eigenvalues as weights. -/
theorem qf_eq_sum {m : Type*} [Fintype m] [DecidableEq m] {Q : Matrix m m 𝕜}
    (hQ : Q.IsHermitian) (x : m → 𝕜) :
    qf Q x = ∑ i, hQ.eigenvalues i *
      ‖(star (hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hQ.eigenvectorUnitary.2
  have hx : U *ᵥ (star U *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hdiag : Uᴴ * Q * U = Matrix.diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hQ.eigenvalues) := by
    have h := hQ.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [hU, Matrix.star_eq_conjTranspose, mul_assoc] using h
  calc qf Q x = qf Q (U *ᵥ (star U *ᵥ x)) := by rw [hx]
    _ = qf (Uᴴ * Q * U) (star U *ᵥ x) := qf_conj _ _ _
    _ = _ := by rw [hdiag, qf_diagonal]

/-- The positive index of inertia `n₊(Q)` of a matrix: the number of positive eigenvalues of `Q`
if `Q` is Hermitian (and `0` otherwise). -/
noncomputable def posIndex {m : Type*} [Fintype m] [DecidableEq m] (Q : Matrix m m 𝕜) : ℕ :=
  if h : Q.IsHermitian then Nat.card {i // 0 < h.eigenvalues i} else 0

theorem posIndex_of_isHermitian {m : Type*} [Fintype m] [DecidableEq m] {Q : Matrix m m 𝕜}
    (hQ : Q.IsHermitian) : posIndex Q = Nat.card {i // 0 < hQ.eigenvalues i} := dif_pos hQ

/-- **Inertia does not increase under compression**: for a Hermitian matrix `Q` and any
rectangular matrix `B`, the compression `Bᴴ Q B` is Hermitian and `n₊(Bᴴ Q B) ≤ n₊(Q)`. -/
theorem posIndex_conj_le {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d] [DecidableEq d]
    {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian ∧ posIndex (Bᴴ * Q * B) ≤ posIndex Q := by
  have hM : (Bᴴ * Q * B).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hQ.eq, Matrix.mul_assoc]
  refine ⟨hM, ?_⟩
  set M : Matrix d d 𝕜 := Bᴴ * Q * B with hMdef
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hUdef
  set V : Matrix d d 𝕜 := (hM.eigenvectorUnitary : Matrix d d 𝕜) with hVdef
  set lam : m → ℝ := hQ.eigenvalues with hlam
  set mu : d → ℝ := hM.eigenvalues with hmu
  -- the linear map from the positive spectral coordinates of `M` to those of `Q`
  set F : ({j : d // 0 < mu j} → 𝕜) →ₗ[𝕜] ({i : m // 0 < lam i} → 𝕜) :=
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i : m // 0 < lam i} → m)).comp
      (((star U).mulVecLin.comp (B.mulVecLin.comp V.mulVecLin)).comp
        (Function.ExtendByZero.linearMap 𝕜 (Subtype.val : {j : d // 0 < mu j} → d))) with hF
  have hFapp : ∀ (z : {j : d // 0 < mu j} → 𝕜) (i : {i : m // 0 < lam i}),
      F z i = (star U *ᵥ (B *ᵥ (V *ᵥ (Function.extend Subtype.val z 0)))) i.1 := by
    intro z i; rfl
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hzne
    set ez : d → 𝕜 := Function.extend Subtype.val z 0 with hez
    have hez_pos : ∀ (j : d) (h : 0 < mu j), ez j = z ⟨j, h⟩ := fun j h =>
      Function.Injective.extend_apply Subtype.val_injective z 0 ⟨j, h⟩
    have hez_neg : ∀ j : d, ¬ (0 < mu j) → ez j = 0 := by
      intro j h
      have hnex : ¬ ∃ a : {j : d // 0 < mu j}, (a : d) = j := by
        rintro ⟨a, ha⟩; exact h (ha ▸ a.2)
      rw [hez, Function.extend_apply' z (0 : d → 𝕜) j hnex]
      rfl
    -- the form of `M` is positive at `V *ᵥ ez`
    have hstarV : star V *ᵥ (V *ᵥ ez) = ez := by
      rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.1 hM.eigenvectorUnitary.2,
        Matrix.one_mulVec]
    have hpos : 0 < qf M (V *ᵥ ez) := by
      rw [qf_eq_sum hM, ← hVdef, ← hmu]
      simp_rw [hstarV]
      obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hzne
      refine Finset.sum_pos' (fun j _ => ?_) ⟨j₀.1, Finset.mem_univ _, ?_⟩
      · by_cases h : 0 < mu j
        · rw [hez_pos j h]
          exact mul_nonneg h.le (sq_nonneg _)
        · rw [hez_neg j h]
          simp
      · rw [hez_pos j₀.1 j₀.2]
        have : z ⟨j₀.1, j₀.2⟩ = z j₀ := by simp
        rw [this]
        have hn : 0 < ‖z j₀‖ ^ 2 := by
          have : ‖z j₀‖ ≠ 0 := by simpa using hj₀
          positivity
        exact mul_pos j₀.2 hn
    -- but the form of `Q` is nonpositive at `B *ᵥ (V *ᵥ ez)`
    have hnonpos : qf Q (B *ᵥ (V *ᵥ ez)) ≤ 0 := by
      rw [qf_eq_sum hQ, ← hUdef, ← hlam]
      refine Finset.sum_nonpos fun i _ => ?_
      by_cases h : 0 < lam i
      · have hzero : (star U *ᵥ (B *ᵥ (V *ᵥ ez))) i = 0 := by
          have := congrFun hz ⟨i, h⟩
          rw [hFapp z ⟨i, h⟩] at this
          simpa [hez] using this
        rw [hzero]
        simp
      · have h1 : lam i ≤ 0 := not_lt.1 h
        have h2 : (0:ℝ) ≤ ‖(star U *ᵥ (B *ᵥ (V *ᵥ ez))) i‖ ^ 2 := sq_nonneg _
        nlinarith
    rw [qf_conj Q B (V *ᵥ ez), ← hMdef] at hnonpos
    exact absurd hpos (not_lt.2 hnonpos)
  have hcard : Module.finrank 𝕜 ({j : d // 0 < mu j} → 𝕜)
      ≤ Module.finrank 𝕜 ({i : m // 0 < lam i} → 𝕜) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hcard
  rw [posIndex_of_isHermitian hM, posIndex_of_isHermitian hQ, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact hcard

section Sanity

attribute [local instance] RCLike.toPartialOrder RCLike.toStarOrderedRing

/-- Sanity check on the definition of `posIndex`: a positive definite matrix has full positive
index of inertia. -/
theorem posIndex_of_posDef {m : Type*} [Fintype m] [DecidableEq m] {Q : Matrix m m 𝕜}
    (hQ : Q.PosDef) : posIndex Q = Fintype.card m := by
  rw [posIndex, dif_pos hQ.1]
  have h : ∀ i, 0 < hQ.1.eigenvalues i := fun i => hQ.eigenvalues_pos i
  simp [h, Nat.card_eq_fintype_card]

end Sanity

end Zeta23Core

