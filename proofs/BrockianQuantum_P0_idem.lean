import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
def P0 : Matrix (Fin 2) (Fin 2) ℂ := !![1,0; 0,0]
def P1 : Matrix (Fin 2) (Fin 2) ℂ := !![0,0; 0,1]
noncomputable def Dplus : Matrix (Fin 2) (Fin 2) ℂ := !![1/2,1/2; 1/2,1/2]
def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0,1; 1,0]
def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1,0; 0,-1]

theorem P0_idem : P0 * P0 = P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P0, Matrix.mul_apply, Fin.sum_univ_two]

theorem P0_trace_one : Matrix.trace P0 = 1 := by
  simp [P0, Matrix.trace, Fin.sum_univ_two]

theorem completeness : P0 + P1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P0, P1, Matrix.add_apply]

theorem P0_P1_orthogonal : P0 * P1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P0, P1, Matrix.mul_apply, Fin.sum_univ_two]

theorem Dplus_idem : Dplus * Dplus = Dplus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dplus, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem PX_traceless : Matrix.trace PX = 0 := by
  simp [PX, Matrix.trace, Fin.sum_univ_two]

theorem PX_PZ_traceless : Matrix.trace (PX * PZ) = 0 := by
  simp [PX, PZ, Matrix.trace, Fin.sum_univ_two]
end BrockianQuantum

