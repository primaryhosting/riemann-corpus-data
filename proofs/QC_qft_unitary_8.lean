import Mathlib
/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: in Lean 4 the `import` command must be the very first command in a file, so the
module docstring header above is placed immediately after `import Mathlib`.
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

/-- The primitive `N`-th root of unity `exp (2 π i / N)` used to build the QFT matrix. -/
noncomputable def qftOmega (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The quantum Fourier transform matrix of size `N`:
`(QFT_N) j k = ω^(j k) / √N` with `ω = exp (2 π i / N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => (Real.sqrt N : ℂ)⁻¹ * qftOmega N ^ (j.val * k.val)

lemma star_qftOmega (N : ℕ) : star (qftOmega N) = (qftOmega N)⁻¹ := by
  rw [qftOmega, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, map_ofNat, Complex.conj_ofReal,
    Complex.conj_natCast]
  ring

lemma qftOmega_ne_zero (N : ℕ) : qftOmega N ≠ 0 := Complex.exp_ne_zero _

lemma qftOmega_pow_self (N : ℕ) (hN : N ≠ 0) : qftOmega N ^ N = 1 :=
  (Complex.isPrimitiveRoot_exp N hN).pow_eq_one

lemma inv_sqrt_mul_inv_sqrt (N : ℕ) :
    (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul_self (Nat.cast_nonneg N)]
  norm_num

/-- The `N`-point quantum Fourier transform matrix is unitary, for every `N ≠ 0`. -/
theorem qft_unitary (N : ℕ) (hN : N ≠ 0) : qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hprim := Complex.isPrimitiveRoot_exp N hN
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  rw [Matrix.mul_apply]
  set x : ℂ := qftOmega N ^ j.val * (qftOmega N ^ k.val)⁻¹ with hx
  have hterm : ∀ m : Fin N,
      qftMatrix N j m * (star (qftMatrix N)) m k = (N : ℂ)⁻¹ * x ^ m.val := by
    intro m
    rw [Matrix.star_apply]
    simp only [qftMatrix, Matrix.of_apply, star_mul', ← Complex.ofReal_inv, Complex.star_def,
      Complex.conj_ofReal, star_pow, star_qftOmega, hx]
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm k.val m.val, Complex.ofReal_inv,
      ← inv_sqrt_mul_inv_sqrt N]
    ring
  rw [Finset.sum_congr rfl (fun m _ => hterm m), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun m => x ^ m) N]
  by_cases hjk : j = k
  · subst hjk
    have h1 : x = 1 := mul_inv_cancel₀ (pow_ne_zero _ (qftOmega_ne_zero N))
    rw [h1]
    simp [Nat.cast_ne_zero.mpr hN]
  · have hx1 : x ≠ 1 := by
      intro h
      rw [hx, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ (qftOmega_ne_zero N))] at h
      exact hjk (Fin.ext (hprim.pow_inj j.isLt k.isLt h))
    have hxN : x ^ N = 1 := by
      rw [hx, mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm j.val N, mul_comm k.val N,
        pow_mul, pow_mul, qftOmega_pow_self N hN, inv_pow, qftOmega_pow_self N hN,
        inv_one, one_pow, one_pow, mul_one]
    rw [geom_sum_eq hx1, hxN, sub_self, zero_div, mul_zero, Matrix.one_apply_ne hjk]

/-- The 8-qubit quantum Fourier transform matrix (size `2^8 = 256`) is unitary. -/
theorem qft_unitary_8 : qftMatrix (2 ^ 8) ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=
  qft_unitary (2 ^ 8) (by norm_num)

end QC

