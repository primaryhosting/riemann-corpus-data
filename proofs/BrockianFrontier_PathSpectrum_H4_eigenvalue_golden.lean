import Mathlib
open Matrix Polynomial
namespace BrockianFrontier.PathSpectrum

/-- The 4-vertex path Hamiltonian: tridiagonal, 2 on the diagonal, -1 on each path edge.
    (Extends the verified H1, H2, H3 in the Constellation Spectrum.) -/
def H4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2,-1,0,0; -1,2,-1,0; 0,-1,2,-1; 0,0,-1,2]

/-- The 5-vertex path Hamiltonian. -/
def H5 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![2,-1,0,0,0; -1,2,-1,0,0; 0,-1,2,-1,0; 0,0,-1,2,-1; 0,0,0,-1,2]

set_option maxHeartbeats 2000000 in
/-- The n-vertex path Hamiltonian has eigenvalues `2 - 2 cos (k π /(n+1))`.
    For H4 the smallest eigenvalue `2 - 2 cos (π/5)` lives in the golden-ratio field:
    prove it is a root of the characteristic polynomial. -/
theorem H4_eigenvalue_golden :
    H4.charpoly.eval (2 - 2 * Real.cos (Real.pi / 5)) = 0 := by
  rw [Matrix.eval_charpoly]
  set c : ℝ := -(2 * Real.cos (Real.pi / 5)) with hc
  have h : (Matrix.scalar (Fin 4) (2 - 2 * Real.cos (Real.pi / 5))) - H4
      = !![c,1,0,0; 1,c,1,0; 0,1,c,1; 0,0,1,c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H4, hc]
  rw [h]
  have hdet : (!![c,1,0,0; 1,c,1,0; 0,1,c,1; 0,0,1,c] : Matrix (Fin 4) (Fin 4) ℝ).det
      = c ^ 4 - 3 * c ^ 2 + 1 := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    norm_num [Fin.succAbove, Fin.lt_def, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons]
    ring
  rw [hdet]
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hcv : c = -(1 + Real.sqrt 5) / 2 := by
    rw [hc, Real.cos_pi_div_five]; ring
  rw [hcv]
  nlinarith [hs]

set_option maxHeartbeats 2000000 in
/-- H5 (odd length) has the exact central eigenvalue 2. -/
theorem H5_eigenvalue_center :
    H5.charpoly.eval 2 = 0 := by
  rw [Matrix.eval_charpoly]
  have h : (Matrix.scalar (Fin 5) (2:ℝ)) - H5
      = !![0,1,0,0,0; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 0,0,0,1,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H5]
  rw [h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [Fin.succAbove, Fin.lt_def, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]

end BrockianFrontier.PathSpectrum

