import Mathlib

/-!
# Density Matrix Unitary Invariant
Category: Quantum Computing
Target: QC.density_matrix_unitary_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix
open scoped ComplexOrder

/-- **Density matrices are preserved by unitary conjugation.**

If `ρ` is a density matrix (positive semidefinite with unit trace) and `U` is unitary,
then `U * ρ * Uᴴ` is again a density matrix.

The positivity half is exactly `Matrix.PosSemidef.mul_mul_conjTranspose_same`; the trace
half follows from `Matrix.trace_mul_cycle` together with unitarity `Uᴴ * U = 1`. -/
theorem density_matrix_unitary_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (ρ U : Matrix n n ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    (U * ρ * Uᴴ).PosSemidef ∧ (U * ρ * Uᴴ).trace = 1 := by
  refine ⟨hρ.mul_mul_conjTranspose_same U, ?_⟩
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul, htr]

end QC

