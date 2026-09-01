/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/
noncomputable def omega (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`F j k = exp (2πi·j·k/N) / √N`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / N) /
    (Real.sqrt N : ℝ)

/-- The QFT matrix on `n` qubits, of size `2^n × 2^n`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := qftMatrix (2 ^ n)

lemma qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = omega N ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt N : ℝ) := by
  unfold qftMatrix omega
  rw [← Complex.exp_nat_mul]
  norm_num
  ring_nf

/-- Conjugating a power of `omega N` inverts the exponent. -/
lemma conj_omega_pow (N : ℕ) (m : ℕ) :
    (starRingEnd ℂ) (omega N ^ m) = omega N ^ (-(m : ℤ)) := by
  have h : (starRingEnd ℂ) (omega N) = (omega N)⁻¹ := by
    unfold omega
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [Complex.ext_iff]
    ring
  rw [map_pow, h, zpow_neg, zpow_natCast, ← inv_pow]

/-- **Key lemma**: orthogonality of the rows of the DFT matrix, i.e. the geometric
sum of powers of a primitive `N`-th root of unity. -/
lemma sum_omega_orthogonality (N : ℕ) (hN : N ≠ 0) (a b : Fin N) :
    ∑ k : Fin N, omega N ^ ((a : ℕ) * (k : ℕ)) *
      (starRingEnd ℂ) (omega N ^ ((b : ℕ) * (k : ℕ))) = if a = b then (N : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (omega N) N := Complex.isPrimitiveRoot_exp N hN
  have hne : omega N ≠ 0 := hprim.ne_zero hN
  set x : ℂ := omega N ^ ((a : ℤ) - (b : ℤ)) with hx
  have hterm : ∀ k : Fin N, omega N ^ ((a : ℕ) * (k : ℕ)) *
      (starRingEnd ℂ) (omega N ^ ((b : ℕ) * (k : ℕ))) = x ^ (k : ℕ) := by
    intro k
    rw [conj_omega_pow, hx, ← zpow_natCast (omega N) ((a : ℕ) * (k : ℕ)), ← zpow_add₀ hne,
      ← zpow_natCast (omega N ^ ((a : ℤ) - (b : ℤ))) (k : ℕ), ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ k) N]
  by_cases hab : a = b
  · subst hab
    simp [hx]
  · have hx1 : x ≠ 1 := by
      rw [hx]
      intro hone
      rw [hprim.zpow_eq_one_iff_dvd] at hone
      apply hab
      have h1 : (a : ℕ) < N := a.isLt
      have h2 : (b : ℕ) < N := b.isLt
      have habs : |((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)| < (N : ℤ) := by
        rw [abs_lt]
        omega
      have := Int.eq_zero_of_abs_lt_dvd hone habs
      have : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := by omega
      exact Fin.ext (by exact_mod_cast this)
    have hxN : x ^ N = 1 := by
      rw [hx, ← zpow_natCast (omega N ^ ((a : ℤ) - (b : ℤ))) N, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow]
    rw [geom_sum_eq hx1, hxN, if_neg hab]
    simp

/-- The DFT / QFT matrix of any positive size is unitary. -/
theorem qftMatrix_unitary (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  have hNpos : (0 : ℝ) < N := by positivity
  have hsq2 : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hNpos)]
    simp
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, star_def]
  have : ∀ k : Fin N, qftMatrix N a k * (starRingEnd ℂ) (qftMatrix N b k) =
      (omega N ^ ((a : ℕ) * (k : ℕ)) *
        (starRingEnd ℂ) (omega N ^ ((b : ℕ) * (k : ℕ)))) / (N : ℂ) := by
    intro k
    rw [qftMatrix_apply, qftMatrix_apply, map_div₀, Complex.conj_ofReal,
      div_mul_div_comm, hsq2]
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.sum_div,
    sum_omega_orthogonality N hN a b]
  by_cases hab : a = b
  · simp [hab, Nat.cast_ne_zero.mpr hN]
  · simp [hab]

/-- The 7-qubit QFT matrix (of size `2^7 = 128`) is unitary. -/
theorem qft_unitary_7 : qft 7 ∈ Matrix.unitaryGroup (Fin (2 ^ 7)) ℂ :=
  qftMatrix_unitary (2 ^ 7) (by norm_num)

/-- Explicit form of unitarity of the 7-qubit QFT: `F * Fᴴ = 1`. -/
theorem qft_mul_conjTranspose_7 : qft 7 * (qft 7).conjTranspose = 1 :=
  (Matrix.mem_unitaryGroup_iff).mp qft_unitary_7

/-- Explicit form of unitarity of the 7-qubit QFT: `Fᴴ * F = 1`. -/
theorem conjTranspose_mul_qft_7 : (qft 7).conjTranspose * qft 7 = 1 :=
  (Matrix.mem_unitaryGroup_iff').mp qft_unitary_7

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

