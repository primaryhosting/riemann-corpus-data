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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]` as a complex `2 × 2` matrix. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℂ) / (Real.sqrt 2 : ℂ)) • !![1, 1; 1, -1]

/-- The Hadamard gate is Hermitian and involutive: `Hᴴ = H` and `H * H = 1`. -/
theorem hadamard_involutive :
    hadamard.conjTranspose = hadamard ∧ hadamard * hadamard = 1 := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  have hsq : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hadamard]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamard, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp <;> linear_combination -hsq

end QC

