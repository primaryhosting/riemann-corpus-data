/-
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the identical header is repeated as a module docstring below.)

import Mathlib

/-!
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The Toffoli (CCNOT) gate acts on the computational basis of three qubits by swapping
the basis states `|110⟩` and `|111⟩` (indices `6` and `7`) and fixing all others. -/
def toffoliPerm : Equiv.Perm (Fin 8) := Equiv.swap 6 7

/-- The Toffoli (CCNOT) matrix, written out explicitly as an `8 × 8` complex matrix. -/
def toffoli : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- The Toffoli matrix is the permutation matrix of `toffoliPerm`. -/
theorem toffoli_eq_permMatrix : toffoli = toffoliPerm.permMatrix ℂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, toffoliPerm, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.swap_apply_def, Fin.ext_iff]

/-- The Toffoli matrix is self-adjoint (it is real and symmetric). -/
theorem toffoli_conjTranspose : toffoliᴴ = toffoli := by
  rw [toffoli_eq_permMatrix, Matrix.conjTranspose_permMatrix]
  simp [toffoliPerm, Equiv.swap_inv]

/-- The Toffoli gate is its own inverse. -/
theorem toffoli_mul_self : toffoli * toffoli = 1 := by
  rw [toffoli_eq_permMatrix, ← Matrix.permMatrix_mul]
  simp [toffoliPerm, Equiv.swap_mul_self]

/-- **The Toffoli (CCNOT) matrix is unitary.**
Being a permutation matrix it is unitary; moreover it is self-adjoint and its own inverse,
so it is an involutive element of the unitary group. -/
theorem toffoli_unitary :
    toffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧ toffoliᴴ = toffoli ∧ toffoli * toffoli = 1 := by
  refine ⟨⟨?_, ?_⟩, toffoli_conjTranspose, toffoli_mul_self⟩ <;>
    simp only [Matrix.star_eq_conjTranspose, toffoli_conjTranspose, toffoli_mul_self]

end QC

