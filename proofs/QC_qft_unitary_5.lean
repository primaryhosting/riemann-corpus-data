/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
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

set_option grind.warning false

namespace QC

/-- The `N × N` discrete Fourier transform matrix, with entries
`(1/√N) · ω^(j·k)` where `ω = exp(2πi/N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => (Real.sqrt N : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I / N) ^ ((j : ℕ) * (k : ℕ))

/-- The quantum Fourier transform on `n` qubits: the DFT matrix of dimension `2^n`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  qftMatrix (2 ^ n)

/-- The `N`-dimensional DFT matrix is unitary for every `N ≠ 0`. -/
theorem qftMatrix_unitary (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hωdef
  have hprim : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN
  have hnorm : ‖ω‖ = 1 := by rw [hωdef, Complex.norm_exp]; norm_num
  have hω0 : ω ≠ 0 := by intro h; rw [h] at hnorm; simp at hnorm
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (by positivity)
  have hinvsq : ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    rw [← mul_inv, hsq]
  have hconj : (starRingEnd ℂ) ω = ω⁻¹ := (Complex.inv_eq_conj hnorm).symm
  -- Each entry of `F * Fᴴ` is a geometric sum in `z = ω^j * (ω^l)⁻¹`.
  have key : ∀ j l k : Fin N, qftMatrix N j k * (star (qftMatrix N)) k l
      = (N : ℂ)⁻¹ * (ω ^ (j : ℕ) * (ω ^ (l : ℕ))⁻¹) ^ (k : ℕ) := by
    intro j l k
    rw [show (star (qftMatrix N)) k l = (starRingEnd ℂ) (qftMatrix N l k) from rfl]
    simp only [qftMatrix, ← hωdef, map_mul, map_inv₀, Complex.conj_ofReal, map_pow, hconj]
    rw [mul_pow, ← inv_pow, pow_mul, pow_mul, ← hinvsq]
    ring
  have hωN : ω ^ N = 1 := hprim.pow_eq_one
  have hpowN : ∀ m : ℕ, (ω ^ m) ^ N = 1 := by
    intro m; rw [← pow_mul, mul_comm, pow_mul, hωN, one_pow]
  ext j l
  rw [Matrix.mul_apply]
  simp only [key]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun k => (ω ^ (j : ℕ) * (ω ^ (l : ℕ))⁻¹) ^ k)]
  by_cases hjl : j = l
  · -- Diagonal: the summand is `1`, so the sum is `N`.
    subst hjl
    rw [mul_inv_cancel₀ (pow_ne_zero _ hω0)]
    simp [hN]
  · -- Off-diagonal: `z ≠ 1` is an `N`-th root of unity, so the geometric sum vanishes.
    have hzne : ω ^ (j : ℕ) * (ω ^ (l : ℕ))⁻¹ ≠ 1 := by
      intro h
      apply hjl
      have hpe : ω ^ (j : ℕ) = ω ^ (l : ℕ) := by field_simp at h; exact h
      exact Fin.ext (hprim.pow_inj j.isLt l.isLt hpe)
    have hzN : (ω ^ (j : ℕ) * (ω ^ (l : ℕ))⁻¹) ^ N = 1 := by
      rw [mul_pow, inv_pow, hpowN, hpowN, inv_one, mul_one]
    rw [geom_sum_eq hzne, hzN, sub_self, zero_div, mul_zero, Matrix.one_apply_ne hjl]

/-- **The 5-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_5 : qft 5 ∈ Matrix.unitaryGroup (Fin (2 ^ 5)) ℂ :=
  qftMatrix_unitary _ (by positivity)

end QC

#print axioms QC.qft_unitary_5

