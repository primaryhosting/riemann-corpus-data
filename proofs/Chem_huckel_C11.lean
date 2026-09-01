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

/-!
# Hückel spectrum of the cycle graph `C₁₁`

We compute the adjacency spectrum of the cycle graph `C₁₁` (the carbon skeleton used in
simple Hückel theory for an 11-membered annulene ring): the eigenvalues of the adjacency
matrix of `SimpleGraph.cycleGraph 11` are exactly `2 * cos (2 * π * k / 11)` for `k = 0, …, 10`.

The proof diagonalises the adjacency matrix by the discrete Fourier (Vandermonde) matrix
built from the primitive 11-th root of unity `ω = exp (2πi/11)`.
-/

namespace Chem

open Polynomial Complex Matrix

/-- The primitive 11-th root of unity `exp (2πi/11)`. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11)

/-- The adjacency matrix of the cycle graph `C₁₁`, over `ℂ`. -/
noncomputable def A11 : Matrix (Fin 11) (Fin 11) ℂ :=
  (SimpleGraph.cycleGraph 11).adjMatrix ℂ

/-- The Fourier (Vandermonde) matrix `F j k = ω ^ (j * k)`. -/
noncomputable def F11 : Matrix (Fin 11) (Fin 11) ℂ :=
  Matrix.vandermonde (fun j : Fin 11 => om ^ (j : ℕ))

/-- The list of Hückel eigenvalues `2 cos (2πk/11)`, `k = 0, …, 10`. -/
noncomputable def c11 (k : Fin 11) : ℂ := ((2 * Real.cos (2 * Real.pi * k / 11) : ℝ) : ℂ)

lemma om_isPrimitiveRoot : IsPrimitiveRoot om 11 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 11 (by norm_num)

lemma om_ne_zero : om ≠ 0 := Complex.exp_ne_zero _

lemma om_pow_eleven : om ^ 11 = 1 := om_isPrimitiveRoot.pow_eq_one

lemma om_pow_mod (n : ℕ) : om ^ (n % 11) = om ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 11]
  rw [pow_add, pow_mul, om_pow_eleven, one_pow, one_mul]

lemma om_fin_add (a b : Fin 11) :
    om ^ ((a + b : Fin 11) : ℕ) = om ^ (a : ℕ) * om ^ (b : ℕ) := by
  rw [Fin.val_add, om_pow_mod, pow_add]

lemma om_succ (j : Fin 11) : om ^ ((j + 1 : Fin 11) : ℕ) = om ^ (j : ℕ) * om := by
  rw [om_fin_add]
  norm_num

lemma om_pred (j : Fin 11) : om ^ ((j - 1 : Fin 11) : ℕ) = om ^ (j : ℕ) * om⁻¹ := by
  have h := om_fin_add (j - 1) 1
  rw [sub_add_cancel] at h
  have h1 : ((1 : Fin 11) : ℕ) = 1 := rfl
  rw [h1, pow_one] at h
  field_simp [om_ne_zero] at h ⊢
  linear_combination -h

/-- Each Hückel eigenvalue is `ω ^ k + ω ^ (-k)`. -/
lemma om_pow_add_inv (k : Fin 11) : om ^ (k : ℕ) + (om ^ (k : ℕ))⁻¹ = c11 k := by
  have h1 : om ^ (k : ℕ) = Complex.exp (((2 * Real.pi * k / 11 : ℝ) : ℂ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : c11 k = 2 * Complex.cos (((2 * Real.pi * k / 11 : ℝ) : ℂ)) := by
    rw [c11, Complex.ofReal_mul, ← Complex.ofReal_cos]
    norm_num
  rw [h1, h2, ← Complex.exp_neg, Complex.cos, ← neg_mul]
  ring

/-- The Fourier matrix diagonalises the adjacency matrix of `C₁₁`. -/
lemma A11_mul_F11 : A11 * F11 = F11 * Matrix.diagonal c11 := by
  ext j k
  rw [A11, SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (by revert j; decide : j - 1 ≠ j + 1), Matrix.mul_diagonal]
  simp only [F11, Matrix.vandermonde_apply, om_succ, om_pred, ← om_pow_add_inv k]
  rw [mul_pow, mul_pow, ← inv_pow]
  ring

lemma F11_isUnit : IsUnit F11 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, F11,
    Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  exact Fin.ext (om_isPrimitiveRoot.pow_inj a.isLt b.isLt h)

/-- The characteristic polynomial of the adjacency matrix of `C₁₁` factors as
`∏ k, (X - 2 cos (2πk/11))`. -/
theorem huckel_C11_charpoly :
    ((SimpleGraph.cycleGraph 11).adjMatrix ℂ).charpoly =
      ∏ k : Fin 11, (X - C ((2 * Real.cos (2 * Real.pi * k / 11) : ℝ) : ℂ)) := by
  obtain ⟨U, hU⟩ := F11_isUnit
  have key : ((U : Matrix (Fin 11) (Fin 11) ℂ) * Matrix.diagonal c11
      * ((U⁻¹ : (Matrix (Fin 11) (Fin 11) ℂ)ˣ) : Matrix (Fin 11) (Fin 11) ℂ)) = A11 := by
    rw [hU, ← A11_mul_F11, mul_assoc, ← hU, U.mul_inv, mul_one]
  show A11.charpoly = _
  rw [← key, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

/-- **Hückel spectrum of `C₁₁`.** The eigenvalues of the adjacency matrix of the cycle graph
`C₁₁` are exactly the numbers `2 cos (2πk/11)` for `k = 0, …, 10`. -/
theorem huckel_C11 (z : ℂ) :
    z ∈ spectrum ℂ ((SimpleGraph.cycleGraph 11).adjMatrix ℂ) ↔
      ∃ k : Fin 11, z = ((2 * Real.cos (2 * Real.pi * k / 11) : ℝ) : ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C11_charpoly]
  simp [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

end Chem

