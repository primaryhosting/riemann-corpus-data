import Mathlib
/-!
# Batch 16 — measurement projectors (qutrit completeness + Z-eigenprojector decomposition). All TRUE.
-/
namespace BrockianQuantum
open Matrix
def E0 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1,0,0]
def E1 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![0,1,0]
def E2 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![0,0,1]
def P0 : Matrix (Fin 2) (Fin 2) ℂ := !![1,0; 0,0]
def P1 : Matrix (Fin 2) (Fin 2) ℂ := !![0,0; 0,1]
def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1,0; 0,-1]

theorem E0_idem : E0 * E0 = E0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E0, Matrix.mul_apply, Matrix.diagonal]

theorem E1_idem : E1 * E1 = E1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, Matrix.mul_apply, Matrix.diagonal]

theorem qutrit_completeness : E0 + E1 + E2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E0, E1, E2, Matrix.add_apply, Matrix.diagonal]

theorem E0_E1_orthogonal : E0 * E1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E0, E1, Matrix.mul_apply, Matrix.diagonal]

theorem E0_hermitian : E0ᴴ = E0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E0, Matrix.conjTranspose_apply, Matrix.diagonal]

theorem Zproj_plus : (1 : Matrix (Fin 2) (Fin 2) ℂ) + PZ = (2 : ℂ) • P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P0, PZ, Matrix.add_apply, Matrix.smul_apply]; norm_num

theorem Zproj_minus : (1 : Matrix (Fin 2) (Fin 2) ℂ) - PZ = (2 : ℂ) • P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P1, PZ, Matrix.sub_apply, Matrix.smul_apply]; norm_num

end BrockianQuantum

