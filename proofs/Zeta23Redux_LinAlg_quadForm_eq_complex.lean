import Mathlib

/-!
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

/-- The coordinates of a vector `x` in the orthonormal eigenbasis of a Hermitian
matrix `A`, i.e. `x` expressed via the unitary matrix diagonalizing `A`. -/
noncomputable def eigencoord {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  (star (hA.eigenvectorUnitary : Matrix n n ℂ)) *ᵥ x

/-- Key intermediate step: in eigencoordinates the Hermitian quadratic form becomes the
quadratic form of the diagonal matrix of eigenvalues. -/
theorem quadForm_eq_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      star (eigencoord hA x) ⬝ᵥ
        (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix n n ℂ) *ᵥ eigencoord hA x := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hstar : star (eigencoord hA x) = star x ᵥ* U := by
    rw [eigencoord, Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  rw [hstar, ← Matrix.dotProduct_mulVec, eigencoord, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  congr 1
  conv_lhs => rw [hA.spectral_theorem]
  simp [hU, mul_assoc]

/-- Hermitian quadratic form in eigencoordinates:
`star x ⬝ᵥ A *ᵥ x = ∑ i, λ i • ‖(eigencoord x) i‖ ^ 2`, as a complex number. -/
theorem quadForm_eq_complex {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      ∑ i, (hA.eigenvalues i : ℂ) * (‖eigencoord hA x i‖ : ℂ) ^ 2 := by
  rw [quadForm_eq_diagonal hA x]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Function.comp_apply,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.conj_mul' (eigencoord hA x i)]
  simp [RCLike.ofReal]
  ring

end Zeta23Redux.LinAlg

