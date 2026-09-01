import Mathlib
/-!
# Batch 1 — single-qubit Pauli algebra (stabilizer/gate foundations). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix
/-- Pauli X. -/           def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- Pauli Y. -/ noncomputable def PY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- Pauli Z. -/           def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem PX_sq : PX * PX = 1 := by
  simp [PX, Matrix.one_fin_two]
theorem PY_sq : PY * PY = 1 := by
  simp [PY, Matrix.one_fin_two, Complex.I_mul_I]
theorem PZ_sq : PZ * PZ = 1 := by
  simp [PZ, Matrix.one_fin_two]
theorem PX_PY : PX * PY = Complex.I • PZ := by
  simp [PX, PY, PZ, Matrix.smul_of, Matrix.smul_cons, Matrix.smul_empty]
theorem PY_PZ : PY * PZ = Complex.I • PX := by
  simp [PX, PY, PZ, Matrix.smul_of, Matrix.smul_cons, Matrix.smul_empty]
theorem PZ_PX : PZ * PX = Complex.I • PY := by
  simp [PX, PY, PZ, Matrix.smul_of, Matrix.smul_cons, Matrix.smul_empty, Complex.I_mul_I]
theorem PX_PY_PZ : PX * PY * PZ = Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [PX_PY]
  simp [PZ, Matrix.one_fin_two, Matrix.smul_of, Matrix.smul_cons, Matrix.smul_empty]
end BrockianQuantum

