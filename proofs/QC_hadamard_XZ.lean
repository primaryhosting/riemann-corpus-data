import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The Pauli `X` matrix. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` matrix. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard matrix, defined as `H = (X + Z) / √2`. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (X + Z)

/-- With `H = (X + Z)/√2`, conjugating `X` by `H` gives `Z`: `H X H = Z`. -/
theorem hadamard_XZ : H * X * H = Z := by
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)]
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs2 : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    field_simp
    linear_combination -h
  simp only [H, X, Z]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> rw [hs2] <;> ring

end QC

