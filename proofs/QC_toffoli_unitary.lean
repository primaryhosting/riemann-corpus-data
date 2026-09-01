/-
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The Toffoli (CCNOT) gate as an 8×8 complex matrix, in the computational basis
`|000⟩, |001⟩, …, |111⟩`: it is the identity except that it swaps `|110⟩` and `|111⟩`. -/
def toffoli : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- The Toffoli matrix is the permutation matrix of the transposition swapping the
basis vectors `|110⟩` and `|111⟩`. -/
theorem toffoli_eq_permMatrix :
    toffoli = Matrix.of fun i j : Fin 8 =>
      if (Equiv.swap (6 : Fin 8) 7) i = j then (1 : ℂ) else 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, Equiv.swap_apply_def, Matrix.of_apply]

/-- The Toffoli matrix is its own inverse. -/
theorem toffoli_mul_self : toffoli * toffoli = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The Toffoli matrix is Hermitian (equal to its own conjugate transpose). -/
theorem toffoli_conjTranspose : Matrix.conjTranspose toffoli = toffoli := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, Matrix.conjTranspose_apply]

/-- **The Toffoli (CCNOT) matrix is a permutation matrix, hence unitary, and it is its
own inverse.** -/
theorem toffoli_unitary :
    toffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧ toffoli * toffoli = 1 := by
  refine ⟨?_, toffoli_mul_self⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, toffoli_conjTranspose]
  exact toffoli_mul_self

end QC
