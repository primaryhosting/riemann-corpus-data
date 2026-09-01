/-
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the header above uses `/-` rather than `/-!` because a module docstring
-- may not precede `import` commands in Lean 4.

import Mathlib

namespace QPhys

open Module Module.End Submodule

/-- **Commuting Hermitian operators are simultaneously diagonalizable.**

If `A` and `B` are symmetric (Hermitian) linear operators on a finite-dimensional inner product
space `E` over `𝕜 = ℝ` or `ℂ`, and `A` and `B` commute, then there is an orthonormal basis of `E`
consisting of vectors that are simultaneously eigenvectors of `A` and of `B`. -/
theorem commuting_simultaneous {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) (a c : Fin (finrank 𝕜 E) → 𝕜),
      ∀ i, A (b i) = a i • b i ∧ B (b i) = c i • b i := by
  letI : DecidableEq (𝕜 × 𝕜) := Classical.decEq _
  have hfam : OrthogonalFamily 𝕜
      (fun i : 𝕜 × 𝕜 => (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E))
      fun i => (eigenspace A i.2 ⊓ eigenspace B i.1).subtypeₗᵢ :=
    hA.orthogonalFamily_eigenspace_inf_eigenspace hB
  have hint : DirectSum.IsInternal
      (fun i : 𝕜 × 𝕜 => (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E)) :=
    hA.directSum_isInternal_of_commute hB hAB
  refine ⟨hint.subordinateOrthonormalBasis rfl hfam,
    fun i => (hint.subordinateOrthonormalBasisIndex rfl i hfam).2,
    fun i => (hint.subordinateOrthonormalBasisIndex rfl i hfam).1, fun i => ?_⟩
  have hmem := hint.subordinateOrthonormalBasis_subordinate rfl i hfam
  exact ⟨mem_eigenspace_iff.mp hmem.1, mem_eigenspace_iff.mp hmem.2⟩

end QPhys

