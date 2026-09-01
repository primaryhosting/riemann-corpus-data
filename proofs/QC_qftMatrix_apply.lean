import Mathlib

/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix:
`F j k = (1/√N) * exp(2πi·jk/N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ)) / N)

/-- The quantum Fourier transform on `n` qubits, a `2^n × 2^n` matrix. -/
noncomputable def qftQubits (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  qftMatrix (2 ^ n)

lemma qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k =
      ((Real.sqrt N : ℝ) : ℂ)⁻¹ *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N) ^ ((j : ℕ) * (k : ℕ)) := by
  rw [qftMatrix]
  simp only [Matrix.of_apply]
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The DFT matrix satisfies `F * Fᴴ = 1`. -/
lemma qftMatrix_mul_conjTranspose (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N * (qftMatrix N)ᴴ = 1 := by
  have hz := Complex.isPrimitiveRoot_exp N hN
  set z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N) with hzdef
  have hzN : z ^ N = 1 := hz.pow_eq_one
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hsq : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  have hcsq : (((Real.sqrt N : ℝ) : ℂ)⁻¹) ^ 2 = ((N : ℂ))⁻¹ := by
    rw [inv_pow, hsq]
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  set w : ℂ := z ^ (j : ℕ) * (z ^ (l : ℕ))⁻¹ with hw
  have hterm : ∀ k : Fin N,
      qftMatrix N j k * (qftMatrix N)ᴴ k l = ((N : ℂ))⁻¹ * w ^ (k : ℕ) := by
    intro k
    rw [Matrix.conjTranspose_apply, qftMatrix_apply, qftMatrix_apply, ← hzdef,
      Complex.star_def]
    have hcz : (starRingEnd ℂ) (z ^ ((l : ℕ) * (k : ℕ))) = (z ^ ((l : ℕ) * (k : ℕ)))⁻¹ := by
      rw [← Complex.inv_eq_conj]
      rw [norm_pow]
      have : ‖z‖ = 1 := by
        rw [hzdef, Complex.norm_exp]
        norm_num
      rw [this, one_pow]
    rw [map_mul, hcz, map_inv₀, Complex.conj_ofReal, hw]
    rw [mul_pow, pow_mul, pow_mul, ← inv_pow]
    rw [← hcsq]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun k => w ^ k) N]
  by_cases hjl : j = l
  · subst hjl
    have hw1 : w = 1 := by
      rw [hw]
      field_simp
    rw [hw1, if_pos rfl]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN)
  · have hwne : w ≠ 1 := by
      intro h
      apply hjl
      have h' : z ^ (j : ℕ) * (z ^ (l : ℕ))⁻¹ = 1 := h
      have hzl : (z ^ (l : ℕ)) ≠ 0 := pow_ne_zero _ hz0
      field_simp at h'
      exact Fin.ext (hz.pow_inj j.isLt l.isLt h')
    have hwN : w ^ N = 1 := by
      have h1 : (z ^ (j : ℕ)) ^ N = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hzN, one_pow]
      have h2 : (z ^ (l : ℕ)) ^ N = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hzN, one_pow]
      rw [hw, mul_pow, inv_pow, h1, h2]
      simp
    rw [geom_sum_eq hwne, hwN]
    simp [hjl]

/-- The DFT matrix is unitary. -/
theorem qftMatrix_unitary (N : ℕ) (hN : N ≠ 0) : qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr (qftMatrix_mul_conjTranspose N hN)

/-- **The 8-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_8 : qftQubits 8 ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=
  qftMatrix_unitary (2 ^ 8) (by norm_num)

/-- The `8 × 8` quantum Fourier transform matrix (3 qubits) is unitary. -/
theorem qft_unitary_dim8 : qftMatrix 8 ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  qftMatrix_unitary 8 (by norm_num)

end QC
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

