import Mathlib
/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `8`-th root of unity `ω = exp(2πi/8)` used by the 3-qubit QFT. -/
noncomputable def qftOmega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The 3-qubit quantum Fourier transform matrix: the `8 × 8` matrix with entries
`(1/√8) · ω^(jk)`, where `ω = exp(2πi/8)`. -/
noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun j k => ((1 / Real.sqrt 8 : ℝ) : ℂ) * qftOmega ^ ((j : ℕ) * (k : ℕ))

lemma qftOmega_primitive : IsPrimitiveRoot qftOmega 8 := by
  have h := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [qftOmega] using h

lemma qftOmega_pow_eight : qftOmega ^ 8 = 1 := qftOmega_primitive.pow_eq_one

lemma qftOmega_pow_eq_one_iff (m : ℕ) : qftOmega ^ m = 1 ↔ 8 ∣ m :=
  qftOmega_primitive.pow_eq_one_iff_dvd m

lemma conj_qftOmega : (starRingEnd ℂ) qftOmega = qftOmega ^ 7 := by
  have h1 : (starRingEnd ℂ) qftOmega = Complex.exp (-(2 * Real.pi * Complex.I / 8)) := by
    rw [qftOmega, ← Complex.exp_conj]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  rw [h1, Complex.exp_neg, ← qftOmega]
  have hne : qftOmega ≠ 0 := Complex.exp_ne_zero _
  field_simp
  exact qftOmega_pow_eight.symm

/-- Orthogonality relation for the 8-th roots of unity. -/
lemma qftOmega_sum (m : ℕ) :
    ∑ k : Fin 8, qftOmega ^ ((k : ℕ) * m) = if 8 ∣ m then 8 else 0 := by
  have hrw : ∀ k : Fin 8, qftOmega ^ ((k : ℕ) * m) = (qftOmega ^ m) ^ (k : ℕ) := by
    intro k; rw [← pow_mul, Nat.mul_comm]
  simp_rw [hrw]
  rw [Fin.sum_univ_eq_sum_range (fun i => (qftOmega ^ m) ^ i) 8]
  by_cases h : 8 ∣ m
  · have hm : qftOmega ^ m = 1 := (qftOmega_pow_eq_one_iff m).mpr h
    simp [hm, h]
  · have hm : qftOmega ^ m ≠ 1 := fun hc => h ((qftOmega_pow_eq_one_iff m).mp hc)
    rw [geom_sum_eq hm]
    have h8 : (qftOmega ^ m) ^ 8 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, qftOmega_pow_eight, one_pow]
    simp [h8, h]

lemma dvd_add_seven_iff_eq : ∀ j l : Fin 8, 8 ∣ ((j : ℕ) + 7 * (l : ℕ)) ↔ j = l := by decide

/-- The 3-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  have hr : (1 / Real.sqrt 8 : ℝ) * (1 / Real.sqrt 8) = 1 / 8 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)]
    norm_num
  have hc : ((1 / Real.sqrt 8 : ℝ) : ℂ) * ((1 / Real.sqrt 8 : ℝ) : ℂ) = 1 / 8 := by
    rw [← Complex.ofReal_mul, hr]; norm_num
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 8, qft3 j k * (star qft3) k l
      = ((1 : ℂ) / 8) * qftOmega ^ ((k : ℕ) * ((j : ℕ) + 7 * (l : ℕ))) := by
    intro k
    simp only [Matrix.star_apply, qft3, Matrix.of_apply, RCLike.star_def, map_mul,
      Complex.conj_ofReal, map_pow, conj_qftOmega, ← pow_mul]
    rw [← hc]
    ring_nf
  simp_rw [key, ← Finset.mul_sum, qftOmega_sum, dvd_add_seven_iff_eq]
  rw [Matrix.one_apply]
  split <;> norm_num

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

