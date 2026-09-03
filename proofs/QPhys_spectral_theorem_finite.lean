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

/-- **Spectral theorem (finite dimensions).**
Every Hermitian matrix `A` over `ℂ` is unitarily diagonalizable with real eigenvalues:
there exist a unitary matrix `U` (i.e. `Uᴴ * U = 1` and `U * Uᴴ = 1`) and a family of
*real* numbers `d : n → ℝ` such that `A = U * diagonal d * Uᴴ`, and the `i`-th column of
`U` is an eigenvector of `A` for the eigenvalue `d i`. -/
theorem spectral_theorem_finite {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * diagonal (fun i => (d i : ℂ)) * Uᴴ ∧
      ∀ i, A *ᵥ (fun k => U k i) = (d i : ℂ) • (fun k => U k i) := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, hA.eigenvectorUnitary.2.1,
    hA.eigenvectorUnitary.2.2, ?_, ?_⟩
  · conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Function.comp_def]
    rfl
  · intro i
    have hcol : (fun k => (hA.eigenvectorUnitary : Matrix n n ℂ) k i) = ⇑(hA.eigenvectorBasis i) :=
      rfl
    rw [hcol, hA.mulVec_eigenvectorBasis i]
    ext k
    simp [Complex.real_smul]

end QPhys

