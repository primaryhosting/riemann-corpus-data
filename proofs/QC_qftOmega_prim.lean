/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex

namespace QC

/-- The primitive `2^7 = 128`-th root of unity `exp (2πi/128)`. -/
noncomputable def qftOmega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 128)

lemma qftOmega_prim : IsPrimitiveRoot qftOmega 128 :=
  Complex.isPrimitiveRoot_exp 128 (by norm_num)

lemma qftOmega_pow : qftOmega ^ (128 : ℕ) = 1 := qftOmega_prim.pow_eq_one

lemma qftOmega_ne_zero : qftOmega ≠ 0 := Complex.exp_ne_zero _

lemma conj_qftOmega : (starRingEnd ℂ) qftOmega = qftOmega⁻¹ := by
  rw [qftOmega, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-- The `7`-qubit quantum Fourier transform matrix, of size `2^7 = 128`:
`F j k = (1/√128) * exp(2πi j k / 128)`. -/
noncomputable def qft7 : Matrix (Fin 128) (Fin 128) ℂ :=
  Matrix.of fun j k => ((1 / Real.sqrt 128 : ℝ) : ℂ) * qftOmega ^ (j.val * k.val)

/-- Orthogonality relation for the `128`-th roots of unity. -/
lemma qft_sum (a b : Fin 128) :
    ∑ k : Fin 128, (starRingEnd ℂ) (qftOmega ^ (k.val * a.val)) * qftOmega ^ (k.val * b.val)
      = if a = b then (128 : ℂ) else 0 := by
  set x : ℂ := (starRingEnd ℂ) (qftOmega ^ a.val) * qftOmega ^ b.val with hx
  have hterm : ∀ k : Fin 128,
      (starRingEnd ℂ) (qftOmega ^ (k.val * a.val)) * qftOmega ^ (k.val * b.val) = x ^ k.val := by
    intro k
    rw [hx, mul_pow, mul_comm k.val a.val, mul_comm k.val b.val, pow_mul, pow_mul, map_pow]
  have hxn : x ^ (128 : ℕ) = 1 := by
    rw [hx, mul_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm a.val 128, mul_comm b.val 128,
      pow_mul, pow_mul, qftOmega_pow, one_pow, one_pow, map_one, mul_one]
  have hconj : (starRingEnd ℂ) (qftOmega ^ a.val) = (qftOmega ^ a.val)⁻¹ := by
    rw [map_pow, conj_qftOmega, inv_pow]
  have hx1 : x = 1 ↔ a = b := by
    constructor
    · intro h
      rw [hx, hconj] at h
      have hne : qftOmega ^ a.val ≠ 0 := pow_ne_zero _ qftOmega_ne_zero
      have h2 : qftOmega ^ b.val = qftOmega ^ a.val := by
        field_simp at h
        linear_combination h
      exact Fin.ext (qftOmega_prim.pow_inj a.isLt b.isLt h2.symm)
    · rintro rfl
      rw [hx, hconj, inv_mul_cancel₀ (pow_ne_zero _ qftOmega_ne_zero)]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  have hrange : ∑ k : Fin 128, x ^ k.val = ∑ k ∈ Finset.range 128, x ^ k :=
    (Finset.sum_range fun i => x ^ i).symm
  rw [hrange]
  by_cases h : a = b
  · rw [if_pos h, hx1.mpr h]
    simp
  · rw [if_neg h, geom_sum_eq (fun hc => h (hx1.mp hc)), hxn, sub_self, zero_div]

lemma qft_norm_sq : ((1 / Real.sqrt 128 : ℝ) : ℂ) * ((1 / Real.sqrt 128 : ℝ) : ℂ)
    = (1 / 128 : ℂ) := by
  rw [← Complex.ofReal_mul,
    show (1 / Real.sqrt 128) * (1 / Real.sqrt 128) = 1 / (Real.sqrt 128 * Real.sqrt 128) by ring,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The 7-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_7 : qft7 ∈ Matrix.unitaryGroup (Fin 128) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin 128, (star qft7) a k * qft7 k b
      = (1 / 128 : ℂ) *
        ((starRingEnd ℂ) (qftOmega ^ (k.val * a.val)) * qftOmega ^ (k.val * b.val)) := by
    intro k
    rw [Matrix.star_apply]
    show (starRingEnd ℂ) (qft7 k a) * qft7 k b = _
    rw [qft7]
    simp only [Matrix.of_apply, map_mul, Complex.conj_ofReal]
    rw [← qft_norm_sq]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, qft_sum]
  by_cases h : a = b
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h, mul_zero]

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

