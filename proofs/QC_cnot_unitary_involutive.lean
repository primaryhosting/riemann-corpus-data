/- (module docstring wrapped in a plain comment: Lean requires `import` to precede any command,
including module doc comments)
/-!
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

namespace QC

/-- The CNOT gate on two qubits, as a `4 × 4` complex matrix in the
computational basis ordering `|00⟩, |01⟩, |10⟩, |11⟩`. -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- CNOT is unitary (`CNOTᴴ * CNOT = 1` and `CNOT * CNOTᴴ = 1`) and involutive
(`CNOT * CNOT = 1`). -/
theorem cnot_unitary_involutive :
    cnot.conjTranspose * cnot = 1 ∧ cnot * cnot.conjTranspose = 1 ∧ cnot * cnot = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [cnot, Matrix.conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

end QC

