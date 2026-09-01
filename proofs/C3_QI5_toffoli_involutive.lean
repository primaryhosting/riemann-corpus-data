import Mathlib
open Matrix
namespace C3.QI5
def CNOT : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0;0,1,0,0;0,0,0,1;0,0,1,0]
def CCX : Matrix (Fin 8) (Fin 8) ℂ := Matrix.of (fun i j => if (i=6∧j=7)∨(i=7∧j=6) then 1 else if i=j ∧ i≠6 ∧ i≠7 then 1 else 0)

/-- The Toffoli (CCX) gate is an involution. -/
theorem toffoli_involutive : CCX * CCX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CCX, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The CNOT gate is an involution. -/
theorem cnot_sq : CNOT * CNOT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The determinant of CNOT is `-1` (it is a single transposition). -/
theorem cnot_det : CNOT.det = -1 := by
  simp [CNOT, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

end C3.QI5

