import Mathlib

open InnerProductSpace

namespace C3.LinAlg

/-- Gram–Schmidt applied to a linearly independent family produces an orthonormal family. -/
theorem gram_schmidt_orthonormal {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hv : LinearIndependent ℝ v) :
    ∃ w : Fin n → EuclideanSpace ℝ (Fin n), Orthonormal ℝ w :=
  ⟨gramSchmidtNormed ℝ v, gramSchmidtNormed_orthonormal hv⟩

/-- A real symmetric matrix on a nonempty index type has a (real) eigenvalue with a nonzero
eigenvector. -/
theorem symmetric_real_eigenvalue {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (l : ℝ), v ≠ 0 ∧ Matrix.toEuclideanLin A v = l • v := by
  have hH : A.IsHermitian := hA
  refine ⟨hH.eigenvectorBasis ⟨0, hn⟩, hH.eigenvalues ⟨0, hn⟩,
    hH.eigenvectorBasis.orthonormal.ne_zero _, ?_⟩
  have h := hH.mulVec_eigenvectorBasis ⟨0, hn⟩
  ext i
  have h2 := congrFun h i
  simpa [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct] using h2

/-- The trace of a matrix is the sum of its diagonal entries. -/
theorem trace_eq_sum_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace A = ∑ i, A i i := rfl

end C3.LinAlg

