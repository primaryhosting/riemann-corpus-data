import Mathlib
/-!
# Batch 14 — three-qubit gates Toffoli, Fredkin, CCZ (8x8 permutation/diagonal). All TRUE.
-/
namespace BrockianQuantum
open Matrix
/-- Toffoli (CCNOT): identity except swap of |110> and |111> (indices 6,7). -/
def Tof : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if i = 6 then (if j = 7 then 1 else 0)
             else if i = 7 then (if j = 6 then 1 else 0)
             else if i = j then 1 else 0
/-- Fredkin (CSWAP): identity except swap of |101> and |110> (indices 5,6). -/
def Fred : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if i = 5 then (if j = 6 then 1 else 0)
             else if i = 6 then (if j = 5 then 1 else 0)
             else if i = j then 1 else 0
/-- CCZ: diag with -1 on |111>. -/
def CCZ : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if i = j then (if i = 7 then -1 else 1) else 0

theorem Tof_sq : Tof * Tof = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Tof]

theorem Tof_unitary : Tof * Tofᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Tof, Matrix.conjTranspose_apply]

theorem Tof_symmetric : Tofᵀ = Tof := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Tof]

theorem Fred_sq : Fred * Fred = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Fred]

theorem Fred_symmetric : Fredᵀ = Fred := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Fred]

theorem CCZ_sq : CCZ * CCZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, CCZ]

theorem CCZ_symmetric : CCZᵀ = CCZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, CCZ]

end BrockianQuantum

