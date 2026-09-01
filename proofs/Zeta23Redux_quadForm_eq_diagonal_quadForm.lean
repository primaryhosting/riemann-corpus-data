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

import Mathlib

/-!
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux
namespace LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The coordinates of `x` in the eigenbasis of the Hermitian matrix `A`:
`eigencoord hA x = U⋆ x`, where `U` is the unitary whose columns are the eigenvectors of `A`. -/
noncomputable def eigencoord {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ x

/-- Key intermediate step: the Hermitian quadratic form of `A` equals the quadratic form of the
diagonal matrix of eigenvalues, evaluated at the eigencoordinates of `x`. -/
theorem quadForm_eq_diagonal_quadForm {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      star (eigencoord hA x) ⬝ᵥ
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix n n ℂ) *ᵥ eigencoord hA x := by
  have hAeq : A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply]
  have hstar : star (eigencoord hA x) = star x ᵥ* (hA.eigenvectorUnitary : Matrix n n ℂ) := by
    simp [eigencoord, Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
  rw [hstar, eigencoord]
  conv_lhs => rw [hAeq]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

/-- Hermitian quadratic form in eigencoordinates:
`star x ⬝ᵥ A *ᵥ x = ∑ᵢ λᵢ(A) * ‖(eigencoord x)ᵢ‖²` as a complex number, for `A` Hermitian. -/
theorem quadForm_eq_complex {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      ∑ i, (hA.eigenvalues i : ℂ) * (‖eigencoord hA x i‖ : ℂ) ^ 2 := by
  rw [quadForm_eq_diagonal_quadForm hA x]
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : star (eigencoord hA x i) * eigencoord hA x i = (‖eigencoord hA x i‖ : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.conj_mul']
  rw [← hz, ← mul_assoc, mul_comm (star (eigencoord hA x i)), mul_assoc]
  rfl

end LinAlg
end Zeta23Redux

