import Mathlib
open Matrix
namespace Frontier.PhysicsQM
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]
theorem pauli_sq_X : X * X = 1 := by
  simp [X, Matrix.one_fin_two]
theorem pauli_XY : X * Y = Complex.I • Z := by
  simp [X, Y, Z, Matrix.smul_of]
theorem pauli_commutator : X * Z - Z * X = (-2 * Complex.I) • Y := by
  simp [X, Y, Z, Matrix.smul_of, Complex.ext_iff]
  norm_num [Complex.I_mul_I]
  ext i
  fin_cases i
  rfl
end Frontier.PhysicsQM

