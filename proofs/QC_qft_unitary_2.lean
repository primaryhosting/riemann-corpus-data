import Mathlib

/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Complex

/-- The 2-qubit quantum Fourier transform matrix, a `4 × 4` complex matrix whose
`(j, k)` entry is `(1/√4) * ω ^ (j * k)` with `ω = exp(2πi/4) = i`.  Since `i` has
order `4`, the exponent may be reduced modulo `4`. -/
noncomputable def qftMatrix2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => (1 / 2 : ℂ) * Complex.I ^ ((j.val * k.val) % 4)

/-- The 2-qubit QFT matrix is unitary. -/
theorem qft_unitary_2 : qftMatrix2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, qftMatrix2, Complex.ext_iff,
      pow_succ, Complex.I_mul_I] <;>
    norm_num

/-- Explicit form of unitarity: `qftMatrix2ᴴ * qftMatrix2 = 1`. -/
theorem qft_conjTranspose_mul_self_2 : qftMatrix2ᴴ * qftMatrix2 = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp qft_unitary_2

/-- Explicit form of unitarity: `qftMatrix2 * qftMatrix2ᴴ = 1`. -/
theorem qft_mul_conjTranspose_self_2 : qftMatrix2 * qftMatrix2ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp qft_unitary_2

end QC

