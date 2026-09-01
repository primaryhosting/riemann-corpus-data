/-
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The coordinates of a vector `x` in the orthonormal eigenbasis of a Hermitian matrix `A`,
i.e. `U⁻¹ x = U* x`, where `U` is the unitary matrix of eigenvectors of `A`. -/
noncomputable def eigencoord {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  (star (hA.eigenvectorUnitary : Matrix n n ℂ)) *ᵥ x

/-- Spectral decomposition of a Hermitian matrix in explicit `U * D * U*` form. -/
theorem hermitian_eq_conj_diagonal {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *
        star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]

/-- Key intermediate lemma: in eigencoordinates, the Hermitian quadratic form associated with
`A` becomes the diagonal quadratic form given by the eigenvalues of `A`. -/
theorem quadForm_eq_diagonal {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      star (eigencoord hA x) ⬝ᵥ
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *ᵥ (eigencoord hA x) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hA' : A = U * D * star U := hermitian_eq_conj_diagonal hA
  have hy : eigencoord hA x = (star U) *ᵥ x := rfl
  have h1 : star ((star U) *ᵥ x) = star x ᵥ* U := by
    rw [Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  calc star x ⬝ᵥ A *ᵥ x = star x ⬝ᵥ (U * (D * star U)) *ᵥ x := by rw [hA', mul_assoc]
    _ = star x ⬝ᵥ U *ᵥ ((D * star U) *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    _ = (star x ᵥ* U) ⬝ᵥ ((D * star U) *ᵥ x) := by rw [Matrix.dotProduct_mulVec]
    _ = star ((star U) *ᵥ x) ⬝ᵥ (D *ᵥ ((star U) *ᵥ x)) := by
        rw [h1, Matrix.mulVec_mulVec]
    _ = star (eigencoord hA x) ⬝ᵥ D *ᵥ (eigencoord hA x) := by rw [hy]

/-- **Hermitian quadratic form in eigencoordinates.** For a Hermitian matrix `A` over `ℂ`,
`star x ⬝ᵥ A *ᵥ x = ∑ i, λ i * ‖(eigencoord x) i‖²`, as an equality of complex numbers,
where the `λ i` are the (real) eigenvalues of `A`. -/
theorem quadForm_eq_complex {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      ∑ i, (hA.eigenvalues i : ℂ) * ((‖eigencoord hA x i‖ ^ 2 : ℝ) : ℂ) := by
  rw [quadForm_eq_diagonal hA x]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Function.comp_apply,
    Complex.coe_algebraMap, RCLike.star_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hz : (starRingEnd ℂ) (eigencoord hA x i) * eigencoord hA x i
      = ((‖eigencoord hA x i‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj']
    norm_cast
  rw [← hz]
  ring

end Zeta23Redux.LinAlg

