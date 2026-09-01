import Mathlib
open Matrix Polynomial
namespace BrockianFrontier.PentagonSpectrum

/-- Adjacency matrix of the 5-cycle Cā‚… (the pentagon graph). -/
def C5 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0]

/-- The 6-cycle Cā‚† adjacency matrix. -/
def C6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,1,0,0,0,1; 1,0,1,0,0,0; 0,1,0,1,0,0; 0,0,1,0,1,0; 0,0,0,1,0,1; 1,0,0,0,1,0]

/-- The eigenvalues of Cā‚™ are `2 cos(2Ļ€k/n)`. For the pentagon this pulls the spectrum
    into the golden-ratio field: `2 cos(2Ļ€/5) = (√5 āˆ’ 1)/2 = Ļ† āˆ’ 1` is an eigenvalue. -/
theorem C5_golden_eigenvalue :
    C5.charpoly.eval ((Real.sqrt 5 - 1) / 2) = 0 := by
  -- The eigenvector for `2 cos(2Ļ€/5)` is `(cos(2Ļ€j/5))ā±¼`, scaled by 4.
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![4, Real.sqrt 5 - 1, -(Real.sqrt 5 + 1), -(Real.sqrt 5 + 1), Real.sqrt 5 - 1], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, C5, Matrix.scalar] <;>
      nlinarith [h5, Real.sqrt_nonneg 5]

/-- Cā‚† has the exact integer eigenvalue `āˆ’2` (`2 cos(3Ļ€/3)`). -/
theorem C6_eigenvalue_neg_two :
    C6.charpoly.eval (-2) = 0 := by
  -- The alternating vector is an eigenvector for the eigenvalue `-2`.
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![1, -1, 1, -1, 1, -1], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, C6, Matrix.scalar] <;> norm_num

end BrockianFrontier.PentagonSpectrum

