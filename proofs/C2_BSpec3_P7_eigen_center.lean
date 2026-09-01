import Mathlib
open Matrix Polynomial
namespace C2.BSpec3
def P7 : Matrix (Fin 7) (Fin 7) ℝ :=
  !![2,-1,0,0,0,0,0;-1,2,-1,0,0,0,0;0,-1,2,-1,0,0,0;0,0,-1,2,-1,0,0;0,0,0,-1,2,-1,0;0,0,0,0,-1,2,-1;0,0,0,0,0,-1,2]

set_option maxHeartbeats 1000000 in
/-- `2` is an eigenvalue of the path-graph Laplacian-type matrix `P7`: the matrix
`2 • 1 - P7` is the adjacency matrix of the path on 7 vertices, which is singular
because `(1,0,-1,0,1,0,-1)` lies in its kernel. -/
theorem P7_eigen_center : P7.charpoly.eval 2 = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![1, 0, -1, 0, 1, 0, -1], ?_, ?_⟩
  · intro hv
    have := congrFun hv 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, P7, Matrix.scalar_apply]

theorem P7_symm : P7.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P7, Matrix.transpose_apply]

theorem golden_conjugate : ((1-Real.sqrt 5)/2) * ((1+Real.sqrt 5)/2) = -1 := by
  have h : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h]
end C2.BSpec3

