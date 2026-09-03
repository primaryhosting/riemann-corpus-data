/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Matrix

/-- The Hückel (adjacency) matrix of the carbon cycle `C₁₄`. -/
noncomputable def A14 : Matrix (Fin 14) (Fin 14) ℂ :=
  (SimpleGraph.cycleGraph 14).adjMatrix ℂ

/-- Eigenvector computation: for any 14-th root of unity `ζ`, the vector `j ↦ ζ ^ j`
is an eigenvector of the adjacency matrix of `C₁₄` with eigenvalue `ζ + ζ⁻¹`. -/
theorem A14_mulVec_pow (ζ : ℂ) (hζ : ζ ^ 14 = 1) :
    A14 *ᵥ (fun j : Fin 14 => ζ ^ (j : ℕ)) = (ζ + ζ⁻¹) • (fun j : Fin 14 => ζ ^ (j : ℕ)) := by
  have hne : ζ ≠ 0 := by rintro rfl; simp at hζ
  funext j
  simp only [A14, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, SimpleGraph.adjMatrix_apply,
    Pi.smul_apply, smul_eq_mul]
  fin_cases j <;> norm_num +decide [SimpleGraph.cycleGraph_adj]
  all_goals field_simp
  all_goals ring_nf
  all_goals first
    | exact hζ
    | linear_combination (-ζ) * hζ

/-- A primitive 14-th root of unity. -/
noncomputable def w14 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 14)

theorem w14_isPrimitiveRoot : IsPrimitiveRoot w14 14 := by
  simpa [w14] using Complex.isPrimitiveRoot_exp 14 (by norm_num)

theorem w14_pow14 : w14 ^ 14 = 1 := w14_isPrimitiveRoot.pow_eq_one

theorem w14_ne_zero : w14 ≠ 0 := Complex.exp_ne_zero _

/-- The eigenvalue attached to the `k`-th 14-th root of unity is `2 cos (2πk/14)`. -/
theorem w14_pow_add_inv (k : ℕ) :
    w14 ^ k + (w14 ^ k)⁻¹ = 2 * Real.cos (2 * Real.pi * k / 14) := by
  have hk : w14 ^ k = Complex.exp (((2 * Real.pi * k / 14 : ℝ) : ℂ) * Complex.I) := by
    simp only [w14]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hk, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos, ← neg_mul]
  ring

theorem w14_pow_pow14 (m : ℕ) : (w14 ^ m) ^ 14 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, w14_pow14, one_pow]

theorem w14_pow_ne_zero (m : ℕ) : w14 ^ m ≠ 0 := pow_ne_zero _ w14_ne_zero

/-- The (unnormalised) discrete Fourier matrix of size 14. -/
noncomputable def F14 : Matrix (Fin 14) (Fin 14) ℂ :=
  Matrix.of fun j k : Fin 14 => w14 ^ ((j : ℕ) * (k : ℕ))

/-- The inverse of the discrete Fourier matrix of size 14. -/
noncomputable def G14 : Matrix (Fin 14) (Fin 14) ℂ :=
  Matrix.of fun k j : Fin 14 => (14 : ℂ)⁻¹ * (w14 ^ ((j : ℕ) * (k : ℕ)))⁻¹

theorem F14_mul_G14 : F14 * G14 = 1 := by
  ext j j'
  have key : ∀ z : ℂ, z ^ 14 = 1 → (∑ k : Fin 14, z ^ (k : ℕ)) = if z = 1 then 14 else 0 := by
    intro z hz
    by_cases h : z = 1
    · simp [h]
    · rw [if_neg h, Fin.sum_univ_eq_sum_range (fun i => z ^ i) 14, geom_sum_eq h, hz]
      simp
  set z : ℂ := w14 ^ (j : ℕ) * (w14 ^ (j' : ℕ))⁻¹ with hzdef
  have hz14 : z ^ 14 = 1 := by
    rw [hzdef, mul_pow, w14_pow_pow14, inv_pow, w14_pow_pow14, inv_one, one_mul]
  have hsum : (F14 * G14) j j' = (14 : ℂ)⁻¹ * ∑ k : Fin 14, z ^ (k : ℕ) := by
    simp only [Matrix.mul_apply, F14, G14, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hE : ((w14 ^ (j' : ℕ))⁻¹) ^ (k : ℕ) = (w14⁻¹) ^ ((j' : ℕ) * (k : ℕ)) := by
      rw [inv_pow, ← pow_mul, ← inv_pow]
    rw [hzdef, mul_pow, hE, ← pow_mul]
    ring
  rw [hsum, key z hz14]
  by_cases hjj : j = j'
  · have hz1 : z = 1 := by
      rw [hzdef, hjj]
      exact mul_inv_cancel₀ (w14_pow_ne_zero _)
    rw [if_pos hz1, hjj]
    simp
  · have hz1 : z ≠ 1 := by
      rw [hzdef]
      intro h
      have hpow : w14 ^ (j : ℕ) = w14 ^ (j' : ℕ) :=
        (mul_inv_eq_one₀ (w14_pow_ne_zero _)).mp h
      exact hjj (Fin.ext (w14_isPrimitiveRoot.pow_inj j.isLt j'.isLt hpow))
    rw [if_neg hz1]
    simp [hjj]

/-- The Fourier matrix diagonalises the adjacency matrix of `C₁₄`. -/
theorem A14_mul_F14 :
    A14 * F14 = F14 * Matrix.diagonal (fun k : Fin 14 => w14 ^ (k : ℕ) + (w14 ^ (k : ℕ))⁻¹) := by
  ext j k
  have h := congrFun (A14_mulVec_pow (w14 ^ (k : ℕ)) (w14_pow_pow14 _)) j
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ← pow_mul,
    Nat.mul_comm] at h
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simpa [F14, mul_comm] using h

end Chem

