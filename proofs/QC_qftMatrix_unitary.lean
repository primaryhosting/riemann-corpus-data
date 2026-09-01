/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

open Complex Finset Matrix

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix:
`F i j = exp (2 π i · j / N) / √N`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => Complex.exp (2 * Real.pi * Complex.I * ((i : ℕ) * (j : ℕ)) / N) / Real.sqrt N

/-- The quantum Fourier transform on `n` qubits, a `2 ^ n × 2 ^ n` matrix. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := qftMatrix (2 ^ n)

/-- Powers of an `N`-th root of unity. -/
private lemma exp_root_pow (N : ℕ) (m : ℂ) (k : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * m / N) ^ k
      = Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ) * m) / N) := by
  rw [← Complex.exp_nat_mul]; ring_nf

/-- Orthogonality of characters: the sum of `exp (2 π i k m / N)` over `k < N` vanishes
unless `m = 0` (for `|m| < N`). -/
private lemma root_sum (N : ℕ) (hN : 0 < N) (m : ℤ) (hm : m.natAbs < N) :
    ∑ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * (m : ℂ)) / N)
      = if m = 0 then (N : ℂ) else 0 := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / N) with hζ
  have hsum : ∑ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * (m : ℂ)) / N)
      = ∑ k ∈ Finset.range N, ζ ^ k := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k => Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * (m : ℂ)) / N))]
    exact Finset.sum_congr rfl (fun k _ => (exp_root_pow N (m : ℂ) k).symm)
  rw [hsum]
  by_cases h0 : m = 0
  · subst h0
    simp [hζ]
  · rw [if_neg h0]
    have hζN : ζ ^ N = 1 := by
      rw [hζ, exp_root_pow]
      have h : (2 : ℂ) * Real.pi * Complex.I * ((N : ℂ) * (m : ℂ)) / N
          = (m : ℂ) * (2 * Real.pi * Complex.I) := by field_simp
      rw [h, Complex.exp_int_mul_two_pi_mul_I]
    have hζ1 : ζ ≠ 1 := by
      intro hc
      rw [hζ, Complex.exp_eq_one_iff] at hc
      obtain ⟨n, hn⟩ := hc
      field_simp at hn
      have hmz : m = N * n := by exact_mod_cast hn
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at hmz
        exact h0 hmz
      have hnat : m.natAbs = N * n.natAbs := by
        rw [hmz, Int.natAbs_mul]; simp
      have : N ≤ m.natAbs := by
        rw [hnat]
        exact Nat.le_mul_of_pos_right N (Int.natAbs_pos.mpr hn0)
      omega
    rw [geom_sum_eq hζ1, hζN]
    simp

/-- The `(i, k)`-entry of `Fᴴ` times the `(k, j)`-entry of `F`. -/
private lemma qft_conjT_mul_entry (N : ℕ) (hN : 0 < N) (i j k : Fin N) :
    (qftMatrix N)ᴴ i k * qftMatrix N k j
      = Complex.exp
          (2 * Real.pi * Complex.I * ((k : ℕ) * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ)) / N) / N := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  have hc : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) : ℂ) * ((i : ℕ) : ℂ)) / N)
      = -(2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) : ℂ) * ((i : ℕ) : ℂ)) / N) := by
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      Complex.conj_natCast]
    ring
  rw [Matrix.conjTranspose_apply, Complex.star_def]
  simp only [qftMatrix, map_div₀, Complex.conj_ofReal, ← Complex.exp_conj, hc]
  rw [div_mul_div_comm, ← Complex.exp_add, hsq]
  congr 1
  push_cast
  field_simp
  ring_nf

/-- The `N × N` quantum Fourier transform matrix is unitary, for every `N > 0`. -/
theorem qftMatrix_unitary (N : ℕ) (hN : 0 < N) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  rw [Matrix.mul_apply]
  have hentry : ∀ k : Fin N, (qftMatrix N)ᴴ i k * qftMatrix N k j
      = Complex.exp
          (2 * Real.pi * Complex.I * ((k : ℕ) * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ)) / N) / N :=
    fun k => qft_conjT_mul_entry N hN i j k
  rw [Finset.sum_congr rfl (fun k _ => hentry k), ← Finset.sum_div]
  have hm : (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)).natAbs < N := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  rw [root_sum N hN _ hm]
  by_cases hij : i = j
  · subst hij
    simp [hNC]
  · have : (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) ≠ 0 := by
      simp only [sub_ne_zero, ne_eq, Nat.cast_inj]
      exact fun h => hij (Fin.ext h.symm)
    rw [if_neg this, Matrix.one_apply_ne hij]
    simp

/-- The 8-qubit quantum Fourier transform matrix (of size `2 ^ 8 = 256`) is unitary. -/
theorem qft_unitary_8 : qft 8 ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=
  qftMatrix_unitary (2 ^ 8) (by norm_num)

end QC

