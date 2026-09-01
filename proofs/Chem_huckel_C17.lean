/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix Polynomial Complex

namespace Chem

/-- The primitive 17-th root of unity `exp(2πi/17)`. -/
noncomputable def zeta17 : ℂ := Complex.exp (2 * Real.pi * I / 17)

lemma isPrimitiveRoot_zeta17 : IsPrimitiveRoot zeta17 17 :=
  Complex.isPrimitiveRoot_exp 17 (by norm_num)

lemma zeta17_pow_seventeen : zeta17 ^ (17 : ℕ) = 1 := isPrimitiveRoot_zeta17.pow_eq_one

lemma zeta17_pow_congr {a b : ℕ} (h : a % 17 = b % 17) : zeta17 ^ a = zeta17 ^ b := by
  have key : ∀ c : ℕ, zeta17 ^ c = zeta17 ^ (c % 17) := by
    intro c
    conv_lhs => rw [← Nat.div_add_mod c 17]
    rw [pow_add, pow_mul, zeta17_pow_seventeen, one_pow, one_mul]
  rw [key a, key b, h]

lemma zeta17_ne_zero : zeta17 ≠ 0 := by
  intro h
  have := zeta17_pow_seventeen
  rw [h] at this
  norm_num at this

/-- The Fourier / Vandermonde matrix `P j k = ζ^(jk)`. -/
noncomputable def dftMat : Matrix (Fin 17) (Fin 17) ℂ :=
  Matrix.vandermonde (fun j : Fin 17 => zeta17 ^ (j : ℕ))

lemma dftMat_apply (j k : Fin 17) : dftMat j k = zeta17 ^ ((j : ℕ) * (k : ℕ)) := by
  simp [dftMat, pow_mul]

/-- The list of Hückel eigenvalues of the cycle `C₁₇`. -/
noncomputable def huckelEig (k : Fin 17) : ℂ :=
  ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ)

lemma huckelEig_eq (k : Fin 17) :
    huckelEig k = zeta17 ^ ((k : ℕ)) + zeta17 ^ (16 * (k : ℕ)) := by
  have hz : zeta17 ^ ((k : ℕ)) = Complex.exp (2 * Real.pi * I * (k : ℕ) / 17) := by
    rw [zeta17, ← Complex.exp_nat_mul]; ring_nf
  have hz' : zeta17 ^ (16 * (k : ℕ)) = Complex.exp (-(2 * Real.pi * I * (k : ℕ) / 17)) := by
    have h1 : zeta17 ^ ((k : ℕ)) * zeta17 ^ (16 * (k : ℕ)) = 1 := by
      rw [← pow_add]
      have h : (k : ℕ) + 16 * (k : ℕ) = 17 * (k : ℕ) := by ring
      rw [h, pow_mul, zeta17_pow_seventeen, one_pow]
    rw [hz] at h1
    rw [Complex.exp_neg]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  rw [hz, hz', huckelEig,
    show ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ)
        = 2 * Complex.cos ((2 * Real.pi * (k : ℕ) / 17 : ℝ) : ℂ) by
      push_cast [Complex.ofReal_cos]; ring,
    Complex.two_cos]
  push_cast
  ring_nf

lemma adjMatrix_mulVec_cycle17 (v : Fin 17 → ℂ) (j : Fin 17) :
    ((cycleGraph 17).adjMatrix ℂ *ᵥ v) j = v (j - 1) + v (j + 1) := by
  have hne : ∀ x : Fin 17, x - 1 ≠ x + 1 := by decide
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (hne j)]

/-- The diagonalization identity `A · P = P · D`. -/
lemma adj_mul_dftMat :
    (cycleGraph 17).adjMatrix ℂ * dftMat = dftMat * Matrix.diagonal huckelEig := by
  ext j k
  have hL : ((cycleGraph 17).adjMatrix ℂ * dftMat) j k
      = ((cycleGraph 17).adjMatrix ℂ *ᵥ (fun l => dftMat l k)) j := rfl
  rw [hL, adjMatrix_mulVec_cycle17, Matrix.mul_diagonal, dftMat_apply, dftMat_apply,
    dftMat_apply, huckelEig_eq]
  have hsub : (j - 1 : Fin 17) = j + 16 := by
    have : ∀ x : Fin 17, x - 1 = x + 16 := by decide
    exact this j
  rw [hsub]
  have e1 : ((j + 16 : Fin 17) : ℕ) * (k : ℕ) % 17 = ((j : ℕ) * (k : ℕ) + 16 * (k : ℕ)) % 17 := by
    have hv : ((j + 16 : Fin 17) : ℕ) = ((j : ℕ) + 16) % 17 := by
      rw [Fin.val_add]; rfl
    have h1 : ((j : ℕ) + 16) % 17 * (k : ℕ) ≡ ((j : ℕ) + 16) * (k : ℕ) [MOD 17] :=
      Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
    have h2 : ((j : ℕ) + 16) * (k : ℕ) = (j : ℕ) * (k : ℕ) + 16 * (k : ℕ) := by ring
    rw [h2] at h1
    rw [hv]
    exact h1
  have e2 : ((j + 1 : Fin 17) : ℕ) * (k : ℕ) % 17 = ((j : ℕ) * (k : ℕ) + (k : ℕ)) % 17 := by
    have hv : ((j + 1 : Fin 17) : ℕ) = ((j : ℕ) + 1) % 17 := by
      rw [Fin.val_add]; rfl
    have h1 : ((j : ℕ) + 1) % 17 * (k : ℕ) ≡ ((j : ℕ) + 1) * (k : ℕ) [MOD 17] :=
      Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
    have h2 : ((j : ℕ) + 1) * (k : ℕ) = (j : ℕ) * (k : ℕ) + (k : ℕ) := by ring
    rw [h2] at h1
    rw [hv]
    exact h1
  rw [zeta17_pow_congr e1, zeta17_pow_congr e2, pow_add, pow_add]
  ring

lemma dftMat_det_ne_zero : dftMat.det ≠ 0 := by
  rw [dftMat, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  have := isPrimitiveRoot_zeta17.pow_inj a.isLt b.isLt hab
  exact Fin.ext this

/-- **Hückel theory for the annulene `C₁₇`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₇` factors as `∏ (X - 2cos(2πk/17))`, i.e. the adjacency
eigenvalues of `C₁₇` are exactly `2·cos(2πk/17)` for `k = 0, …, 16`. -/
theorem huckel_C17 :
    ((cycleGraph 17).adjMatrix ℂ).charpoly =
      ∏ k : Fin 17, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ)) := by
  have hdet : IsUnit dftMat.det := isUnit_iff_ne_zero.mpr dftMat_det_ne_zero
  let U : (Matrix (Fin 17) (Fin 17) ℂ)ˣ :=
    ⟨dftMat, dftMat⁻¹, Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet⟩
  have hA : (cycleGraph 17).adjMatrix ℂ
      = (U : Matrix (Fin 17) (Fin 17) ℂ) * Matrix.diagonal huckelEig
        * ((U⁻¹ : (Matrix (Fin 17) (Fin 17) ℂ)ˣ) : Matrix (Fin 17) (Fin 17) ℂ) := by
    show (cycleGraph 17).adjMatrix ℂ = dftMat * Matrix.diagonal huckelEig * dftMat⁻¹
    rw [← adj_mul_dftMat, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  rw [hA, Matrix.charpoly_units_conj U, Matrix.charpoly_diagonal]
  rfl

end Chem

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

