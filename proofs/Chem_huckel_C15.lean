/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Matrix

/-- A primitive 15-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 15)

lemma zeta_primitive : IsPrimitiveRoot zeta 15 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 15 (by norm_num)

lemma zeta_pow_15 : zeta ^ 15 = 1 := zeta_primitive.pow_eq_one

lemma zeta_pow_mod (c : ℕ) : zeta ^ c = zeta ^ (c % 15) := by
  conv_lhs => rw [← Nat.div_add_mod c 15]
  rw [pow_add, pow_mul, zeta_pow_15, one_pow, one_mul]

lemma zeta_pow_congr {a b : ℕ} (h : a ≡ b [MOD 15]) : zeta ^ a = zeta ^ b := by
  rw [zeta_pow_mod a, zeta_pow_mod b, show a % 15 = b % 15 from h]

/-- The Fourier (Vandermonde) matrix `U i k = ζ^(i k)` that diagonalizes the cycle. -/
noncomputable def U : Matrix (Fin 15) (Fin 15) ℂ :=
  Matrix.vandermonde (fun i : Fin 15 => zeta ^ (i : ℕ))

lemma U_apply (i k : Fin 15) : U i k = zeta ^ ((i : ℕ) * (k : ℕ)) := by
  rw [U, Matrix.vandermonde_apply, ← pow_mul]

lemma U_det_ne_zero : U.det ≠ 0 := by
  rw [U, Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact Fin.ext (zeta_primitive.pow_inj i.isLt j.isLt hij)

/-- The `k`-th Hückel eigenvalue `2 cos (2πk/15)`. -/
noncomputable def eig (k : Fin 15) : ℂ := ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) : ℝ) : ℂ)

lemma eig_eq (k : Fin 15) : zeta ^ (k : ℕ) + zeta ^ (14 * (k : ℕ)) = eig k := by
  have hz : zeta ^ (k : ℕ) = Complex.exp (((2 * Real.pi * (k : ℕ) / 15 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz' : zeta ^ (14 * (k : ℕ)) =
      Complex.exp (-((2 * Real.pi * (k : ℕ) / 15 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    have h : ((14 * (k : ℕ) : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 15)
        = -((2 * Real.pi * (k : ℕ) / 15 : ℝ) : ℂ) * Complex.I
          + ((k : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [hz, hz', ← Complex.two_cos, eig, Complex.ofReal_mul, Complex.ofReal_cos]
  norm_num

/-- The diagonal matrix of the Hückel eigenvalues. -/
noncomputable def D : Matrix (Fin 15) (Fin 15) ℂ := Matrix.diagonal eig

lemma fin15_add_one_val (i : Fin 15) : ((i + 1 : Fin 15) : ℕ) = ((i : ℕ) + 1) % 15 := by
  simp [Fin.add_def]

lemma fin15_sub_one_val (i : Fin 15) : ((i - 1 : Fin 15) : ℕ) = ((i : ℕ) + 14) % 15 := by
  simp [Fin.sub_def]
  omega

lemma adjMatrix_mul_apply (i k : Fin 15) :
    ((cycleGraph 15).adjMatrix ℂ * U) i k = U (i - 1) k + U (i + 1) k := by
  have hne : (i - 1 : Fin 15) ≠ i + 1 := by
    intro h
    have h2 : ((i - 1 : Fin 15) : ℕ) = ((i + 1 : Fin 15) : ℕ) := by rw [h]
    rw [fin15_sub_one_val, fin15_add_one_val] at h2
    omega
  have h1 : ((cycleGraph 15).adjMatrix ℂ * U) i k =
      ((cycleGraph 15).adjMatrix ℂ *ᵥ (fun j => U j k)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, SimpleGraph.adjMatrix_mulVec_apply]
  have h2 : (cycleGraph 15).neighborFinset i = {i - 1, i + 1} :=
    @SimpleGraph.cycleGraph_neighborFinset 13 i
  rw [h2, Finset.sum_pair hne]

/-- The Fourier matrix diagonalizes the adjacency matrix of the 15-cycle. -/
lemma adj_mul_U : (cycleGraph 15).adjMatrix ℂ * U = U * D := by
  ext i k
  rw [adjMatrix_mul_apply, U_apply, U_apply, D, Matrix.mul_diagonal, U_apply, ← eig_eq]
  have e1 : zeta ^ (((i - 1 : Fin 15) : ℕ) * (k : ℕ))
      = zeta ^ ((i : ℕ) * (k : ℕ) + 14 * (k : ℕ)) := by
    apply zeta_pow_congr
    rw [fin15_sub_one_val]
    calc ((i : ℕ) + 14) % 15 * (k : ℕ)
        ≡ ((i : ℕ) + 14) * (k : ℕ) [MOD 15] := Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
      _ = (i : ℕ) * (k : ℕ) + 14 * (k : ℕ) := by ring
  have e2 : zeta ^ (((i + 1 : Fin 15) : ℕ) * (k : ℕ))
      = zeta ^ ((i : ℕ) * (k : ℕ) + (k : ℕ)) := by
    apply zeta_pow_congr
    rw [fin15_add_one_val]
    calc ((i : ℕ) + 1) % 15 * (k : ℕ)
        ≡ ((i : ℕ) + 1) * (k : ℕ) [MOD 15] := Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
      _ = (i : ℕ) * (k : ℕ) + (k : ℕ) := by ring
  rw [e1, e2, pow_add, pow_add]
  ring

/-- **Hückel theory for the C₁₅ ring.**  The spectrum (set of eigenvalues) of the adjacency
matrix of the cycle graph `C₁₅` is exactly `{2 cos (2πk/15) : k = 0, …, 14}`. -/
theorem huckel_C15 :
    spectrum ℂ ((cycleGraph 15).adjMatrix ℂ) =
      Set.range (fun k : Fin 15 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) : ℝ) : ℂ)) := by
  have hU : IsUnit U.det := isUnit_iff_ne_zero.mpr U_det_ne_zero
  let u : (Matrix (Fin 15) (Fin 15) ℂ)ˣ :=
    ⟨U, U⁻¹, Matrix.mul_nonsing_inv U hU, Matrix.nonsing_inv_mul U hU⟩
  have hA : (cycleGraph 15).adjMatrix ℂ
      = (u : Matrix (Fin 15) (Fin 15) ℂ) * D * ((u⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) :
        Matrix (Fin 15) (Fin 15) ℂ) := by
    show (cycleGraph 15).adjMatrix ℂ = U * D * U⁻¹
    calc (cycleGraph 15).adjMatrix ℂ
        = (cycleGraph 15).adjMatrix ℂ * U * U⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv U hU, Matrix.mul_one]
      _ = U * D * U⁻¹ := by rw [adj_mul_U]
  rw [hA, spectrum.units_conjugate, D, spectrum_diagonal]
  rfl

/-- The explicit Hückel molecular orbitals of C₁₅: the vector `j ↦ ζ^(jk)` is an eigenvector
of the adjacency matrix with eigenvalue `2 cos (2πk/15)`. -/
theorem huckel_C15_eigenvector (k : Fin 15) :
    (cycleGraph 15).adjMatrix ℂ *ᵥ (fun j : Fin 15 => zeta ^ ((j : ℕ) * (k : ℕ)))
      = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) : ℝ) : ℂ) •
          (fun j : Fin 15 => zeta ^ ((j : ℕ) * (k : ℕ))) := by
  funext i
  have hcol : (fun j : Fin 15 => zeta ^ ((j : ℕ) * (k : ℕ))) = fun j => U j k := by
    funext j; rw [U_apply]
  have h1 : ((cycleGraph 15).adjMatrix ℂ *ᵥ (fun j : Fin 15 => U j k)) i
      = ((cycleGraph 15).adjMatrix ℂ * U) i k := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hcol, Pi.smul_apply, smul_eq_mul, h1, adj_mul_U, D, Matrix.mul_diagonal, U_apply, eig]
  ring

end Chem

