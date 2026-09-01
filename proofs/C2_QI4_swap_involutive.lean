import Mathlib
open Matrix
namespace C2.QI4
def SWAP : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0;0,0,1,0;0,1,0,0;0,0,0,1]
def CZ : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,-1]

theorem swap_involutive : SWAP * SWAP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP, Matrix.mul_apply, Fin.sum_univ_four]

theorem cz_involutive : CZ * CZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CZ, Matrix.mul_apply, Fin.sum_univ_four]

theorem cz_diagonal : CZ.IsDiag := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [CZ]

end C2.QI4

