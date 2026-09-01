import Mathlib
/-!
# Batch 4 — two-qubit gates CNOT, CZ, SWAP (4×4 over ℂ, basis |00>,|01>,|10>,|11>). All TRUE.
-/
namespace BrockianQuantum
open Matrix
/-- CNOT (control q0, target q1): swaps |10> ↔ |11>. -/
def CNOT : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0]
/-- Controlled-Z: diag(1,1,1,-1). -/
def CZ : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,-1]
/-- SWAP: swaps |01> ↔ |10>. -/
def SWAP : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]

theorem CNOT_sq : CNOT * CNOT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT, Matrix.mul_apply, Fin.sum_univ_four]

theorem CNOT_unitary : CNOT * CNOTᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]

theorem CZ_sq : CZ * CZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CZ, Matrix.mul_apply, Fin.sum_univ_four]

theorem CZ_unitary : CZ * CZᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CZ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]

theorem SWAP_sq : SWAP * SWAP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP, Matrix.mul_apply, Fin.sum_univ_four]

theorem SWAP_unitary : SWAP * SWAPᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]

theorem CZ_symmetric : CZᵀ = CZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CZ, Matrix.transpose_apply]

end BrockianQuantum

