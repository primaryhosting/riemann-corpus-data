/-
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-- The 3×3 sine-kernel Hankel matrix. -/
def M : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- Explicit inverse of `M`. -/
def Minv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![36/5, -63/5, 24/5; -63/5, 159/5, -72/5; 24/5, -72/5, 36/5]

theorem det_M : M.det = 5/108 := by
  simp [M, Matrix.det_fin_three]
  norm_num

theorem M_mul_Minv : M * Minv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Minv, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem inv_M : M⁻¹ = Minv := Matrix.inv_eq_right_inv M_mul_Minv

/-- Inverse-matrix cross-check for the Christoffel function: `M` is invertible
(`det M = 5/108 ≠ 0`) and `(M⁻¹)₀₀ = 36/5`, so `1 / (e₀ᵀ M⁻¹ e₀) = 5/36`,
agreeing with the determinant-ratio Christoffel value. -/
theorem christoffel_inverse_form :
    M.det = 5/108 ∧ M.det ≠ 0 ∧ M⁻¹ 0 0 = 36/5 ∧ (M⁻¹ 0 0)⁻¹ = 5/36 := by
  refine ⟨det_M, by rw [det_M]; norm_num, ?_, ?_⟩ <;> rw [inv_M] <;> norm_num [Minv]

end Zeta23Scaffold

