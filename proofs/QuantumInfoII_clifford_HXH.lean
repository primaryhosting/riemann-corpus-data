import Mathlib
open Matrix
namespace QuantumInfoII

/-- Pauli matrices and the unnormalized Hadamard `M = √2·H`, over ℤ. -/
def X : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;1,0]
def Z : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;0,-1]
def M : Matrix (Fin 2) (Fin 2) ℤ := !![1,1;1,-1]

/-- Gottesman–Knill core: Hadamard conjugation swaps X and Z (unnormalized ⇒ factor 2). -/
theorem clifford_HXH : M * X * M = (2 : ℤ) • Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z, M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- And swaps Z to X. -/
theorem clifford_HZH : M * Z * M = (2 : ℤ) • X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z, M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Pauli X and Z anticommute — the algebraic seed of the uncertainty principle. -/
theorem pauli_anticommute : X * Z = - (Z * X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The classical (local hidden-variable) Bell/CHSH bound: every ±1 assignment gives
    `|CHSH| ≤ 2`, versus the quantum Tsirelson value `2√2`. -/
theorem chsh_classical_bound (a0 a1 b0 b1 : ℤ)
    (ha0 : a0 = 1 ∨ a0 = -1) (ha1 : a1 = 1 ∨ a1 = -1)
    (hb0 : b0 = 1 ∨ b0 = -1) (hb1 : b1 = 1 ∨ b1 = -1) :
    a0*b0 + a0*b1 + a1*b0 - a1*b1 ≤ 2 ∧ -2 ≤ a0*b0 + a0*b1 + a1*b0 - a1*b1 := by
  rcases ha0 with h0 | h0 <;> rcases ha1 with h1 | h1 <;>
    rcases hb0 with h2 | h2 <;> rcases hb1 with h3 | h3 <;>
    subst h0 <;> subst h1 <;> subst h2 <;> subst h3 <;> norm_num

end QuantumInfoII

