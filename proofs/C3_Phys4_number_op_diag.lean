import Mathlib
open Matrix
namespace C3.Phys4
-- `noncomputable` added: `Real.sqrt` has no executable code.
noncomputable def a : Matrix (Fin 3) (Fin 3) ℝ := !![0,1,0;0,0,Real.sqrt 2;0,0,0]
noncomputable def ad : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,0;1,0,0;0,Real.sqrt 2,0]
theorem number_op_diag : (ad * a).IsDiag := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [ad, a, Matrix.mul_apply, Fin.sum_univ_succ]
def Sx : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
def Sy : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]
theorem pauli_prod_xy : Sx * Sy = Complex.I • (!![1,0;0,-1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sx, Sy, Matrix.mul_apply, Fin.sum_univ_succ]
theorem pauli_trace_x : Matrix.trace Sx = 0 := by
  simp [Sx, Matrix.trace_fin_two]
end C3.Phys4

