import Mathlib
open Matrix Polynomial
namespace C6.BSp7

def C8 : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of (fun i j => if ((i:ℤ)-(j:ℤ))%8=1 ∨ ((j:ℤ)-(i:ℤ))%8=1 then 1 else 0)

/-- The cycle adjacency matrix has zero diagonal, hence zero trace. -/
theorem C8_trace : Matrix.trace C8 = 0 := by
  simp [Matrix.trace, C8]

def P11 : Matrix (Fin 11) (Fin 11) ℝ := Matrix.of (fun i j => if i=j then 2 else if (i:ℤ)-(j:ℤ)=1∨(j:ℤ)-(i:ℤ)=1 then -1 else 0)

/-- The path Laplacian-type matrix `P11` is symmetric. -/
theorem P11_symm : P11.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, P11, Matrix.of_apply]
  rcases eq_or_ne i j with h | h
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    congr 1
    exact propext (by tauto)

/-- `2` is an eigenvalue of `P11`: the matrix `2 • 1 - P11` is the adjacency matrix of the
path on 11 vertices, which kills the alternating vector `(1,0,-1,0,1,0,-1,0,1,0,-1)`. -/
theorem P11_eigen : P11.charpoly.eval 2 = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![1,0,-1,0,1,0,-1,0,1,0,-1], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.scalar, P11, Fin.sum_univ_succ]

end C6.BSp7

