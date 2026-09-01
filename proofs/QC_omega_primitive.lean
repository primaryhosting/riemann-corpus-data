import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

set_option grind.warning false

namespace QC

/-- `omega` is the primitive 8th root of unity `exp (2πi/8)` used by the 3-qubit QFT. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / (8 : ℕ))

/-- The 3-qubit quantum Fourier transform matrix: an `8 × 8` complex matrix with
entries `(1/√8) * ω^(j*k)`, where `ω = exp (2πi/8)`. -/
noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ :=
  fun j k => ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * omega ^ (j.val * k.val)

lemma omega_primitive : IsPrimitiveRoot omega 8 :=
  Complex.isPrimitiveRoot_exp 8 (by norm_num)

lemma omega_ne_zero : omega ≠ 0 := omega_primitive.ne_zero (by norm_num)

lemma conj_omega : (starRingEnd ℂ) omega = omega⁻¹ := by
  rw [omega, ← Complex.inv_eq_conj]
  simp [Complex.norm_exp]

/-- Orthogonality of the columns of the (unnormalized) QFT matrix. -/
lemma key_sum (j k : Fin 8) :
    ∑ l : Fin 8, (starRingEnd ℂ) (omega ^ (l.val * j.val)) * omega ^ (l.val * k.val)
      = if j = k then 8 else 0 := by
  have hterm : ∀ l : Fin 8, (starRingEnd ℂ) (omega ^ (l.val * j.val)) * omega ^ (l.val * k.val)
      = ((omega ^ j.val)⁻¹ * omega ^ k.val) ^ l.val := by
    intro l
    rw [map_pow, conj_omega, mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm j.val l.val,
      mul_comm k.val l.val]
  simp only [hterm]
  by_cases h : j = k
  · subst h
    simp [inv_mul_cancel₀ (pow_ne_zero j.val omega_ne_zero)]
  · have hne : (omega ^ j.val)⁻¹ * omega ^ k.val ≠ 1 := by
      intro hc
      rw [inv_mul_eq_one₀ (pow_ne_zero j.val omega_ne_zero)] at hc
      exact h (Fin.ext (omega_primitive.pow_inj j.isLt k.isLt hc))
    have hpow : ((omega ^ j.val)⁻¹ * omega ^ k.val) ^ 8 = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm j.val 8, mul_comm k.val 8, pow_mul,
        pow_mul, omega_primitive.pow_eq_one, one_pow, one_pow, inv_one, one_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => ((omega ^ j.val)⁻¹ * omega ^ k.val) ^ i) 8,
      geom_sum_eq hne, hpow]
    simp [h]

/-- The 3-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  have h8 : ((Real.sqrt 8 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ) = 8 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs : ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ = (8 : ℂ)⁻¹ := by
    rw [← mul_inv, h8]
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ l : Fin 8, (star qft3) j l * qft3 l k
      = (8 : ℂ)⁻¹ * ((starRingEnd ℂ) (omega ^ (l.val * j.val)) * omega ^ (l.val * k.val)) := by
    intro l
    rw [Matrix.star_apply]
    simp only [qft3, star_mul', Complex.star_def, Complex.conj_ofReal, map_inv₀]
    rw [← hs]
    ring
  simp only [hterm, ← Finset.mul_sum, key_sum, Matrix.one_apply]
  split <;> norm_num

end QC

