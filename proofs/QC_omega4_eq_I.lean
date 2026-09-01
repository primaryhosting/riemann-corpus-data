import Mathlib

/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The primitive 4-th root of unity `exp (2 π i / 4) = i` used by the 2-qubit QFT. -/
noncomputable def omega4 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 4)

lemma omega4_eq_I : omega4 = Complex.I := by
  have h : (2 * (Real.pi : ℂ) * Complex.I / 4) = (Real.pi / 2 : ℝ) * Complex.I := by
    push_cast
    ring
  rw [omega4, h, Complex.exp_mul_I]
  simp

/-- The 2-qubit quantum Fourier transform matrix: a `4 × 4` matrix with entries
`(1/2) * ω^(j*k)` where `ω = exp (2 π i / 4)`. -/
noncomputable def qft2 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun j k => (1 / 2 : ℂ) * omega4 ^ (j.val * k.val)

/-- The 2-qubit QFT matrix is unitary. -/
theorem qft_unitary_2 : qft2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, qft2, omega4_eq_I,
      pow_succ, Complex.ext_iff] <;>
    norm_num

/-- Explicit form of unitarity: the conjugate transpose of `qft2` is a two-sided inverse. -/
theorem qft2_conjTranspose_mul_self :
    Matrix.conjTranspose qft2 * qft2 = 1 ∧ qft2 * Matrix.conjTranspose qft2 = 1 :=
  ⟨Matrix.mem_unitaryGroup_iff'.mp qft_unitary_2,
   Matrix.mem_unitaryGroup_iff.mp qft_unitary_2⟩

#print axioms qft_unitary_2

end QC

