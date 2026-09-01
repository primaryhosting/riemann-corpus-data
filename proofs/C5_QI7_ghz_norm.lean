import Mathlib
open Matrix
namespace C5.QI7
def GHZ : Matrix (Fin 8) (Fin 1) ℂ := !![1;0;0;0;0;0;0;1]
def W : Matrix (Fin 8) (Fin 1) ℂ := !![0;1;1;0;1;0;0;0]

theorem ghz_norm : (GHZᴴ * GHZ) 0 0 = 2 := by
  simp [GHZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  norm_num

theorem w_norm : (Wᴴ * W) 0 0 = 3 := by
  simp [W, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  norm_num

theorem ghz_w_orthogonal : (GHZᴴ * W) 0 0 = 0 := by
  simp [GHZ, W, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

end C5.QI7

