/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
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

namespace Chem

open Matrix Complex SimpleGraph

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

lemma isPrimitiveRoot_zeta {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma zeta_pow_n {n : ℕ} (hn : n ≠ 0) : zeta n ^ n = 1 := (isPrimitiveRoot_zeta hn).pow_eq_one

/-- Powers of `zeta n` only depend on the exponent modulo `n`. -/
lemma zeta_pow_congr {n : ℕ} (hn : n ≠ 0) {a b : ℕ} (h : a % n = b % n) :
    zeta n ^ a = zeta n ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a n]
  conv_rhs => rw [← Nat.div_add_mod b n]
  rw [pow_add, pow_add, pow_mul, pow_mul, zeta_pow_n hn, one_pow, one_pow, h]

lemma zeta_pow_mod_mul {n : ℕ} (hn : n ≠ 0) (a k : ℕ) :
    zeta n ^ ((a % n) * k) = zeta n ^ (a * k) := by
  refine zeta_pow_congr hn ?_
  conv_lhs => rw [Nat.mul_mod, Nat.mod_mod]
  rw [Nat.mul_mod a k]

/-- `zeta n ^ ((n-1) * k)` is the inverse of `zeta n ^ k`. -/
lemma zeta_pow_pred_mul {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    zeta n ^ ((n - 1) * k) = (zeta n ^ k)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add]
  have h : (n - 1) * k + k = n * k := by
    cases n with
    | zero => exact absurd rfl hn
    | succ p => rw [Nat.succ_sub_one]; ring
  rw [h, pow_mul, zeta_pow_n hn, one_pow]

/-- `zeta n ^ k + (zeta n ^ k)⁻¹ = 2 cos (2πk/n)`, the Hückel eigenvalue. -/
lemma zeta_pow_add_inv (n k : ℕ) :
    zeta n ^ k + (zeta n ^ k)⁻¹ = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have h1 : zeta n ^ k = Complex.exp (((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, ← Complex.exp_neg]
  rw [Complex.exp_mul_I, show -(((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I)
      = ((-(2 * Real.pi * k / n) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The Fourier (Vandermonde) matrix built from the powers of `zeta n`. -/
noncomputable def fourierMat (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vandermonde (fun j : Fin n => zeta n ^ (j : ℕ))

lemma fourierMat_apply {n : ℕ} (j k : Fin n) :
    fourierMat n j k = zeta n ^ ((j : ℕ) * (k : ℕ)) := by
  rw [fourierMat, Matrix.vandermonde_apply, ← pow_mul]

lemma fourierMat_isUnit {n : ℕ} (hn : n ≠ 0) : IsUnit (fourierMat n) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [fourierMat]
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro a b hab
  exact Fin.ext ((isPrimitiveRoot_zeta hn).pow_inj a.isLt b.isLt hab)

/-- The diagonal matrix of Hückel energies `2 cos (2πk/n)`. -/
noncomputable def huckelDiag (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ))

/-- The key intertwining relation `A · F = F · D` between the adjacency matrix of the cycle,
the Fourier matrix and the diagonal matrix of Hückel energies. -/
lemma adjMatrix_mul_fourierMat (m : ℕ) :
    (SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ * fourierMat (m + 3)
      = fourierMat (m + 3) * huckelDiag (m + 3) := by
  have hn : m + 3 ≠ 0 := by omega
  let n : ℕ := m + 3
  ext j k
  rw [SimpleGraph.adjMatrix_mul_apply]
  have hnb : (SimpleGraph.cycleGraph n).neighborFinset j = {j - 1, j + 1} :=
    SimpleGraph.cycleGraph_neighborFinset
  have hne : j - 1 ≠ j + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc j, left_eq_add]
    exact ne_of_beq_false rfl
  rw [hnb, Finset.sum_pair hne]
  have hone : ((1 : Fin n) : ℕ) = 1 := by simp [n]
  have hsucc : ((j + 1 : Fin n) : ℕ) = ((j : ℕ) + 1) % n := by
    rw [Fin.add_def, hone]
  have hpred : ((j - 1 : Fin n) : ℕ) = (n - 1 + (j : ℕ)) % n := by
    rw [Fin.sub_def, hone]
  rw [fourierMat_apply, fourierMat_apply, huckelDiag, Matrix.mul_diagonal, fourierMat_apply]
  have e1 : zeta n ^ (((j + 1 : Fin n) : ℕ) * (k : ℕ))
      = zeta n ^ ((j : ℕ) * (k : ℕ)) * zeta n ^ ((k : ℕ)) := by
    rw [hsucc, zeta_pow_mod_mul hn, add_mul, one_mul, pow_add]
  have e2 : zeta n ^ (((j - 1 : Fin n) : ℕ) * (k : ℕ))
      = zeta n ^ ((j : ℕ) * (k : ℕ)) * (zeta n ^ ((k : ℕ)))⁻¹ := by
    rw [hpred, zeta_pow_mod_mul hn, add_mul, pow_add, zeta_pow_pred_mul hn, mul_comm]
  rw [e1, e2, ← zeta_pow_add_inv n (k : ℕ)]
  ring

/-- **Hückel spectrum of a cycle.**  For `n ≥ 3`, the eigenvalues (the spectrum) of the
adjacency matrix of the cycle graph `C n` are exactly the numbers `2 cos (2πk/n)` for
`k = 0, …, n-1`; these are the Hückel π-orbital energies (in units of `β`, relative to `α`). -/
theorem huckel_cycle_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ ((SimpleGraph.cycleGraph n).adjMatrix ℂ)
      = Set.range (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  obtain ⟨u, huv⟩ := fourierMat_isUnit (n := m + 3) (by omega)
  have key : (SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ
      = (u : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) * huckelDiag (m + 3)
        * ((u⁻¹ : (Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ)ˣ) :
            Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) := by
    have h1 : (u : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) * huckelDiag (m + 3)
        = (SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ * u := by
      rw [huv, adjMatrix_mul_fourierMat]
    rw [h1, mul_assoc]
    simp
  rw [key, spectrum.units_conjugate, huckelDiag, spectrum_diagonal]

/-- **Hückel eigenvectors of a cycle.**  For `n ≥ 3` and each `k`, the vector
`j ↦ exp (2πi jk/n)` is an eigenvector of the adjacency matrix of `C n` with eigenvalue
`2 cos (2πk/n)`. -/
theorem huckel_cycle_eigenvector (m : ℕ) (k : Fin (m + 3)) :
    (SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ *ᵥ (fun j : Fin (m + 3) =>
        zeta (m + 3) ^ ((j : ℕ) * (k : ℕ)))
      = ((2 * Real.cos (2 * Real.pi * k / (m + 3)) : ℝ) : ℂ) •
        (fun j : Fin (m + 3) => zeta (m + 3) ^ ((j : ℕ) * (k : ℕ))) := by
  funext j
  have h := congrFun (congrFun (adjMatrix_mul_fourierMat m) j) k
  rw [huckelDiag, Matrix.mul_diagonal, fourierMat_apply] at h
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, fourierMat_apply, mul_comm]
    using h

end Chem

