import Mathlib
open Matrix
namespace MS2.QI3
def H2 : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,-1]
def CNOT : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0;0,1,0,0;0,0,0,1;0,0,1,0]
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]

theorem cnot_involutive : CNOT * CNOT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cnot_unitary : CNOT * CNOTᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply]

theorem hadamard_unnorm_sq : H2 * H2 = (2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H2, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem xz_eq_neg_zx : X * Z = - (Z * X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauli_z_involutive : Z * Z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Z, Matrix.mul_apply, Fin.sum_univ_succ]
end MS2.QI3

