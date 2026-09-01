import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₇`: vertices `i, j ∈ Fin 7` (labels taken
modulo `7`) are adjacent iff they differ by `1`.  This is the Hückel matrix of a
7-membered carbon ring in the units `α = 0`, `β = 1`. -/
def adjC7 : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- A primitive 7-th root of unity. -/
noncomputable def w7 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

/-- The discrete Fourier (Vandermonde) matrix built from the 7-th roots of unity. -/
noncomputable def fourier7 : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.vandermonde (fun i : Fin 7 => w7 ^ (i : ℕ))

lemma w7_isPrimitiveRoot : IsPrimitiveRoot w7 7 := by
  have := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  simpa [w7] using this

lemma w7_pow_seven : w7 ^ 7 = 1 := w7_isPrimitiveRoot.pow_eq_one

lemma w7_pow_pow_seven (k : ℕ) : (w7 ^ k) ^ 7 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, w7_pow_seven, one_pow]

/-- The `k`-th Hückel eigenvalue `2 cos (2πk/7)` expressed through the 7-th root of
unity `w7`. -/
lemma eig_eq (k : ℕ) :
    ((2 * Real.cos (2 * Real.pi * k / 7) : ℝ) : ℂ) = w7 ^ k + (w7 ^ k) ^ 6 := by
  have hz : w7 ^ k = Complex.exp ((2 * Real.pi * k / 7 : ℝ) * Complex.I) := by
    rw [w7, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h6 : (w7 ^ k) ^ 6 = Complex.exp (-((2 * Real.pi * k / 7 : ℝ) * Complex.I)) := by
    have h := eq_inv_of_mul_eq_one_left (a := (w7 ^ k) ^ 6) (b := w7 ^ k)
      (by rw [← pow_succ]; exact w7_pow_pow_seven k)
    rw [h, hz, ← Complex.exp_neg]
  rw [h6, hz, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos, neg_mul]
  push_cast
  ring

/-- Row `i` of the adjacency matrix applied to a geometric vector coming from a 7-th
root of unity `z`. -/
lemma adj_row_sum (z : ℂ) (hz : z ^ 7 = 1) (i : Fin 7) :
    ∑ j : Fin 7, adjC7 i j * z ^ (j : ℕ) = (z + z ^ 6) * z ^ (i : ℕ) := by
  fin_cases i <;>
    simp +decide [adjC7, Fin.sum_univ_seven] <;>
    first
      | linear_combination (0 : ℂ) * hz
      | linear_combination -hz
      | linear_combination (-z) * hz
      | linear_combination (-z ^ 2) * hz
      | linear_combination (-z ^ 3) * hz
      | linear_combination (-z ^ 4) * hz
      | linear_combination (-(1 + z ^ 5)) * hz

lemma adj_mul_fourier :
    adjC7 * fourier7 =
      fourier7 * Matrix.diagonal
        (fun k : Fin 7 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) : ℝ) : ℂ)) := by
  ext i k
  have hcol : ∀ j : Fin 7, fourier7 j k = (w7 ^ (k : ℕ)) ^ (j : ℕ) := by
    intro j
    rw [fourier7, Matrix.vandermonde_apply, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [Matrix.mul_apply, Matrix.mul_diagonal, eig_eq]
  simp only [hcol]
  rw [adj_row_sum _ (w7_pow_pow_seven (k : ℕ)) i]
  ring

lemma fourier7_det_ne_zero : fourier7.det ≠ 0 := by
  rw [fourier7]
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro a b hab
  have := w7_isPrimitiveRoot.pow_inj a.isLt b.isLt hab
  exact Fin.ext this

/-- **Hückel theory for the cycle `C₇`.** The characteristic polynomial of the adjacency
matrix of the 7-cycle splits as `∏ (X - 2 cos (2πk/7))`, `k = 0, …, 6`; equivalently, the
Hückel eigenvalues of a 7-membered carbon ring are exactly the seven numbers
`2 cos (2πk/7)`. -/
theorem huckel_C7 :
    adjC7.charpoly =
      ∏ k : Fin 7, (X - C (((2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) : ℝ) : ℂ))) := by
  set D : Matrix (Fin 7) (Fin 7) ℂ :=
    Matrix.diagonal (fun k : Fin 7 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) : ℝ) : ℂ))
    with hD
  obtain ⟨U, hU⟩ : IsUnit fourier7 :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr fourier7_det_ne_zero)
  have hUinv : (U : Matrix (Fin 7) (Fin 7) ℂ) * (↑U⁻¹ : Matrix (Fin 7) (Fin 7) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconj : adjC7 = (U : Matrix (Fin 7) (Fin 7) ℂ) * D * (↑U⁻¹ : Matrix (Fin 7) (Fin 7) ℂ) := by
    have h1 : adjC7 * (U : Matrix (Fin 7) (Fin 7) ℂ) = (U : Matrix (Fin 7) (Fin 7) ℂ) * D := by
      rw [hU, hD]; exact adj_mul_fourier
    calc adjC7 = adjC7 * ((U : Matrix (Fin 7) (Fin 7) ℂ) * (↑U⁻¹ : Matrix (Fin 7) (Fin 7) ℂ)) := by
          rw [hUinv, mul_one]
      _ = (adjC7 * (U : Matrix (Fin 7) (Fin 7) ℂ)) * (↑U⁻¹ : Matrix (Fin 7) (Fin 7) ℂ) := by
          rw [mul_assoc]
      _ = (U : Matrix (Fin 7) (Fin 7) ℂ) * D * (↑U⁻¹ : Matrix (Fin 7) (Fin 7) ℂ) := by rw [h1]
  rw [hconj, Matrix.charpoly_units_conj, hD, Matrix.charpoly_diagonal]

/-- Restatement of `Chem.huckel_C7` as a description of the spectrum: a complex number is an
eigenvalue of the adjacency matrix of `C₇` iff it is of the form `2 cos (2πk/7)`, `k = 0, …, 6`. -/
theorem huckel_C7_spectrum (mu : ℂ) :
    mu ∈ spectrum ℂ adjC7 ↔
      ∃ k : Fin 7, mu = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) : ℝ) : ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C7]
  simp [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

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

