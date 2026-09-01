import Mathlib
open Matrix Polynomial
namespace C4.BSp5
def P9 : Matrix (Fin 9) (Fin 9) ℝ := Matrix.of (fun i j => if i=j then 2 else if (i:ℤ)-(j:ℤ)=1 ∨ (j:ℤ)-(i:ℤ)=1 then -1 else 0)

/-- `2` is an eigenvalue of the `9 × 9` path Laplacian-type matrix `P9`: the matrix
`2 • 1 - P9` kills the nonzero vector `(1,0,-1,0,1,0,-1,0,1)`, hence has zero
determinant, which by `Matrix.eval_charpoly` is `P9.charpoly.eval 2`. -/
theorem P9_eigen_center : P9.charpoly.eval 2 = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![1, 0, -1, 0, 1, 0, -1, 0, 1], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, P9, Matrix.scalar]

theorem P9_symm : P9.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, P9, Matrix.of_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h), if_congr or_comm rfl rfl]

theorem golden_recip : ((1+Real.sqrt 5)/2)⁻¹ = ((Real.sqrt 5 - 1)/2) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (1 + Real.sqrt 5) / 2 ≠ 0 := by positivity
  field_simp
  nlinarith [h5]

end C4.BSp5

