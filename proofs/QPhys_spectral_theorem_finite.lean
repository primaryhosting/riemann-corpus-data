import Mathlib

/-!
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
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

namespace QPhys

open Matrix

/-- **Spectral theorem, finite-dimensional case.**
Every Hermitian matrix `A` over `ℂ` is unitarily diagonalizable with *real* eigenvalues:
there is a unitary matrix `U` (i.e. `Uᴴ * U = 1` and `U * Uᴴ = 1`) and a real-valued
function `d` on the index type such that `A = U * diagonal (d) * Uᴴ`.
Moreover the `i`-th column of `U` is an eigenvector of `A` with real eigenvalue `d i`. -/
theorem spectral_theorem_finite {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ ∧
      ∀ i, A *ᵥ (fun j => U j i) = ((d i : ℝ) : ℂ) • (fun j => U j i) := by
  classical
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), hA.eigenvalues, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  · have := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, Matrix.conjTranspose, Function.comp_def,
      mul_assoc] using this
  · intro i
    have h := hA.mulVec_eigenvectorBasis i
    have hcol : (fun j => (hA.eigenvectorUnitary : Matrix n n ℂ) j i)
        = ⇑(hA.eigenvectorBasis i) := rfl
    rw [hcol, h]
    ext j
    simp [Complex.real_smul]

end QPhys

