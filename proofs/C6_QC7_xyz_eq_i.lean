import Mathlib
open Matrix
namespace C6.QC7
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]

theorem xyz_eq_i : X*Y*Z = Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Y, Z, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauli_trace_zero : Matrix.trace X = 0 ∧ Matrix.trace Y = 0 ∧ Matrix.trace Z = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [X, Y, Z, Matrix.trace_fin_two]

theorem xy_anticomm : X*Y + Y*X = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X, Y]
end C6.QC7

