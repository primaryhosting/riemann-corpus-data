import Mathlib
open Matrix
namespace MS.LogicQuantum

theorem schroeder_bernstein {α β : Type*} (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (α ≃ β) := by
  obtain ⟨h, hh⟩ := Function.Embedding.schroeder_bernstein hf hg
  exact ⟨Equiv.ofBijective h hh⟩

theorem cantor_no_surjection {α : Type*} (f : α → Set α) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

/-- No-cloning: overlap identity forces states orthogonal or identical. -/
theorem no_cloning (z : ℂ) (h : z = z ^ 2) : z = 0 ∨ z = 1 := by
  have h' : z * (z - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- Robertson uncertainty seed: Pauli X,Z anticommute so cannot be simultaneously ±1-definite. -/
theorem pauli_XZ_anticommute :
    (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1,0;0,-1]
      = - (!![1,0;0,-1] * !![0,1;1,0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_fin_two]

/-- Spectral theorem (finite Hermitian matrices are unitarily diagonalizable — existence of an
    orthonormal eigenbasis). -/
theorem hermitian_has_eigenvalue {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.IsHermitian) : ∃ (v : EuclideanSpace ℂ (Fin n)) (μ : ℝ), v ≠ 0 ∧
      Matrix.toEuclideanLin M v = (μ : ℂ) • v := by
  let j : Fin n := ⟨0, hn⟩
  refine ⟨hM.eigenvectorBasis j, hM.eigenvalues j, hM.eigenvectorBasis.orthonormal.ne_zero j, ?_⟩
  have key : Matrix.toEuclideanLin M (hM.eigenvectorBasis j)
      = WithLp.toLp 2 (M *ᵥ (hM.eigenvectorBasis j).ofLp) := rfl
  rw [key, hM.mulVec_eigenvectorBasis j]
  ext k
  simp [Complex.real_smul]

end MS.LogicQuantum

