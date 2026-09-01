/-
# Pauli Anticommute
Category: Quantum Computing
Target: QC.pauli_anticommute
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

/-- The Pauli `X` matrix. -/
def PauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def PauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli `Z` matrix. -/
def PauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli matrices `X`, `Y`, `Z` pairwise anticommute, and each squares to the
identity matrix. -/
theorem pauli_anticommute :
    (PauliX * PauliY + PauliY * PauliX = 0) ∧
    (PauliY * PauliZ + PauliZ * PauliY = 0) ∧
    (PauliX * PauliZ + PauliZ * PauliX = 0) ∧
    (PauliX * PauliX = 1) ∧ (PauliY * PauliY = 1) ∧ (PauliZ * PauliZ = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [PauliX, PauliY, PauliZ, ← Matrix.one_fin_two, Complex.I_mul_I] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp

end QC

