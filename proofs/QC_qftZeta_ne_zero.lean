/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above uses a plain block comment because Lean requires `import`
-- to precede any module docstring; the docstring form is repeated below.)

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
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

/-- The primitive `N`-th root of unity `exp (2 π i / N)` used by the quantum Fourier
transform on `N` basis states. -/
noncomputable def qftZeta (N : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

/-- The `N`-dimensional quantum Fourier transform matrix:
`F j k = N^(-1/2) * exp (2 π i j k / N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := fun j k =>
  ((Real.sqrt N : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / (N : ℂ))

lemma qftZeta_ne_zero (N : ℕ) : qftZeta N ≠ 0 := Complex.exp_ne_zero _

lemma qftMatrix_apply_pow (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = ((Real.sqrt N : ℝ) : ℂ)⁻¹ * qftZeta N ^ ((j : ℕ) * (k : ℕ)) := by
  rw [qftMatrix, qftZeta, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

lemma qftZeta_conj (N : ℕ) : (starRingEnd ℂ) (qftZeta N) = (qftZeta N)⁻¹ := by
  rw [qftZeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
    Complex.conj_natCast]
  ring

/-- Off-diagonal geometric sums of powers of `qftZeta N` vanish. -/
lemma qft_geom_sum (N : ℕ) (hN : N ≠ 0) (d : ℤ) (hd : ¬ ((N : ℤ) ∣ d)) :
    ∑ m ∈ Finset.range N, (qftZeta N ^ d) ^ m = 0 := by
  have hprim : IsPrimitiveRoot (qftZeta N) N := Complex.isPrimitiveRoot_exp N hN
  have hne : qftZeta N ^ d ≠ 1 := fun h => hd ((hprim.zpow_eq_one_iff_dvd d).mp h)
  have hpow : (qftZeta N ^ d) ^ N = 1 := by
    rw [← zpow_natCast (qftZeta N ^ d) N, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hprim.pow_eq_one, one_zpow]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

lemma qft_prod (N : ℕ) (j k m : Fin N) :
    star (qftMatrix N) j m * qftMatrix N m k
      = (N : ℂ)⁻¹ * (qftZeta N ^ ((k : ℤ) - (j : ℤ))) ^ (m : ℕ) := by
  have hz : qftZeta N ≠ 0 := qftZeta_ne_zero N
  rw [Matrix.star_apply, qftMatrix_apply_pow, qftMatrix_apply_pow]
  have hstar : star (((Real.sqrt N : ℝ) : ℂ)⁻¹ * qftZeta N ^ ((m : ℕ) * (j : ℕ)))
      = ((Real.sqrt N : ℝ) : ℂ)⁻¹ * (qftZeta N)⁻¹ ^ ((m : ℕ) * (j : ℕ)) := by
    simp only [star_mul', star_inv₀, star_pow, Complex.star_def,
      Complex.conj_ofReal, qftZeta_conj]
  rw [hstar]
  have hN2 : ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    have h : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
      push_cast
      ring
    rw [← mul_inv, h]
  have hpow : (qftZeta N)⁻¹ ^ ((m : ℕ) * (j : ℕ)) * qftZeta N ^ ((m : ℕ) * (k : ℕ))
      = (qftZeta N ^ ((k : ℤ) - (j : ℤ))) ^ (m : ℕ) := by
    rw [← zpow_natCast (qftZeta N ^ ((k : ℤ) - (j : ℤ))) (m : ℕ), ← zpow_mul]
    rw [inv_pow, ← zpow_natCast (qftZeta N) ((m : ℕ) * (j : ℕ)),
      ← zpow_natCast (qftZeta N) ((m : ℕ) * (k : ℕ)), ← zpow_neg, ← zpow_add₀ hz]
    congr 1
    push_cast
    ring
  calc ((Real.sqrt N : ℝ) : ℂ)⁻¹ * (qftZeta N)⁻¹ ^ ((m : ℕ) * (j : ℕ)) *
        (((Real.sqrt N : ℝ) : ℂ)⁻¹ * qftZeta N ^ ((m : ℕ) * (k : ℕ)))
      = (((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹) *
        ((qftZeta N)⁻¹ ^ ((m : ℕ) * (j : ℕ)) * qftZeta N ^ ((m : ℕ) * (k : ℕ))) := by ring
    _ = (N : ℂ)⁻¹ * (qftZeta N ^ ((k : ℤ) - (j : ℤ))) ^ (m : ℕ) := by rw [hN2, hpow]

/-- The `N`-dimensional QFT matrix is unitary. -/
theorem qftMatrix_mem_unitaryGroup (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hcast : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [qft_prod, ← Finset.mul_sum]
  by_cases hjk : j = k
  · subst hjk
    simp [hcast]
  · rw [if_neg hjk]
    have hd : ¬ ((N : ℤ) ∣ ((k : ℤ) - (j : ℤ))) := by
      intro hdvd
      have hlt : |((k : ℤ) - (j : ℤ))| < (N : ℤ) := by
        have hj : (j : ℤ) < N := by exact_mod_cast j.isLt
        have hk : (k : ℤ) < N := by exact_mod_cast k.isLt
        have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
        have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
        rw [abs_lt]
        omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      apply hjk
      have : (j : ℕ) = (k : ℕ) := by omega
      exact Fin.ext this
    rw [Fin.sum_univ_eq_sum_range (fun m => (qftZeta N ^ ((k : ℤ) - (j : ℤ))) ^ m) N,
      qft_geom_sum N hN _ hd, mul_zero]

/-- The 4-qubit (16-dimensional) quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_4 : qftMatrix 16 ∈ Matrix.unitaryGroup (Fin 16) ℂ :=
  qftMatrix_mem_unitaryGroup 16 (by norm_num)

end QC

