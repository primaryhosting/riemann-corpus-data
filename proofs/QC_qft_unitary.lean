import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `N`-th root of unity `exp(2πi/N)`. -/
noncomputable def omegaRoot (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N × N` discrete Fourier transform matrix, with entries
`(1/√N) * exp(2πi·jk/N)`. -/
noncomputable def dftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => (1 / Real.sqrt N : ℝ) * Complex.exp (2 * Real.pi * Complex.I * (j * k) / N)

/-- The quantum Fourier transform on `n` qubits: the `2^n × 2^n` DFT matrix. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := dftMatrix (2 ^ n)

lemma omegaRoot_isPrimitiveRoot {N : ℕ} (hN : N ≠ 0) :
    IsPrimitiveRoot (omegaRoot N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma omegaRoot_ne_zero (N : ℕ) : omegaRoot N ≠ 0 := Complex.exp_ne_zero _

lemma omegaRoot_zpow (N : ℕ) (d : ℤ) :
    omegaRoot N ^ d = Complex.exp (d * (2 * Real.pi * Complex.I / N)) := by
  rw [omegaRoot, ← Complex.exp_int_mul]

lemma star_omegaRoot_zpow (N : ℕ) (d : ℤ) : star (omegaRoot N ^ d) = omegaRoot N ^ (-d) := by
  rw [omegaRoot_zpow, omegaRoot_zpow, Complex.star_def, ← Complex.exp_conj]
  congr 1
  push_cast
  simp [Complex.ext_iff]
  ring

/-- Orthogonality: a full geometric sum of a nontrivial power of a primitive root vanishes. -/
lemma sum_omega_zpow_eq_zero {N : ℕ} (hN : N ≠ 0) (d : ℤ) (hd : ¬ ((N : ℤ) ∣ d)) :
    ∑ i : Fin N, omegaRoot N ^ (d * (i : ℕ)) = 0 := by
  have hprim := omegaRoot_isPrimitiveRoot hN
  set z : ℂ := omegaRoot N ^ d with hz
  have hz1 : z ≠ 1 := fun h => hd ((hprim.zpow_eq_one_iff_dvd d).mp h)
  have hzN : z ^ N = 1 := by
    rw [hz, ← _root_.zpow_natCast (omegaRoot N ^ d) N, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, _root_.zpow_natCast, hprim.pow_eq_one, _root_.one_zpow]
  have hsum : ∑ i : Fin N, omegaRoot N ^ (d * (i : ℕ)) = ∑ i ∈ Finset.range N, z ^ i := by
    rw [Fin.sum_univ_eq_sum_range (fun i => omegaRoot N ^ (d * (i : ℕ)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz, ← _root_.zpow_natCast (omegaRoot N ^ d) i, ← _root_.zpow_mul]
  rw [hsum, geom_sum_eq hz1, hzN, sub_self, zero_div]

lemma dft_entry (N : ℕ) (j k : Fin N) :
    dftMatrix N j k = (1 / Real.sqrt N : ℝ) * omegaRoot N ^ (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := by
  rw [dftMatrix, omegaRoot_zpow]
  congr 2
  push_cast
  ring

/-- The DFT matrix of any positive size is unitary. -/
theorem dftMatrix_unitary {N : ℕ} (hN : N ≠ 0) :
    dftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hc : ((1 / Real.sqrt N : ℝ) : ℂ) * ((1 / Real.sqrt N : ℝ) : ℂ) = 1 / (N : ℂ) := by
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNpos.le
    have h1 : (1 / Real.sqrt N : ℝ) * (1 / Real.sqrt N : ℝ) = 1 / (N : ℝ) := by
      rw [div_mul_div_comm, one_mul, hsq]
    rw [← Complex.ofReal_mul, h1]
    push_cast
    ring
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstarc : star ((1 / Real.sqrt N : ℝ) : ℂ) = ((1 / Real.sqrt N : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hterm : ∀ i : Fin N,
      (star (dftMatrix N) j i) * dftMatrix N i k
        = (1 / (N : ℂ)) * omegaRoot N ^ ((((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((i : ℕ) : ℤ)) := by
    intro i
    rw [Matrix.star_apply, dft_entry, dft_entry, star_mul', star_omegaRoot_zpow, hstarc,
      mul_mul_mul_comm, hc, ← zpow_add₀ (omegaRoot_ne_zero N)]
    rw [show -(((i : ℕ) : ℤ) * ((j : ℕ) : ℤ)) + ((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)
        = (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((i : ℕ) : ℤ) by ring]
  simp only [hterm, ← Finset.mul_sum]
  by_cases h : j = k
  · subst h
    simp only [sub_self, zero_mul, zpow_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, if_true]
    field_simp
  · rw [if_neg h]
    have hd : ¬ ((N : ℤ) ∣ (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))) := by
      intro hdvd
      have hj : ((j : ℕ) : ℤ) < N := by exact_mod_cast j.isLt
      have hk : ((k : ℕ) : ℤ) < N := by exact_mod_cast k.isLt
      have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
      have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := Int.natCast_nonneg _
      have habs : |((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)| < (N : ℤ) := by
        rw [abs_sub_lt_iff]
        omega
      have hzero := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact h (Fin.ext (by omega))
    rw [sum_omega_zpow_eq_zero hN _ hd, mul_zero]

/-- **The n-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  dftMatrix_unitary (Nat.two_pow_pos n).ne'

end QC

