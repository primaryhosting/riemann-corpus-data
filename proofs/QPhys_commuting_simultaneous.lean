import Mathlib
/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module doc comments, so the header comment appears immediately after the import.

set_option autoImplicit false

namespace QPhys

open Module.End

/-- **Two commuting Hermitian operators are simultaneously diagonalizable.**

If `A` and `B` are symmetric (Hermitian, self-adjoint) linear operators on a
finite-dimensional inner product space `E` over `𝕜 = ℝ` or `ℂ`, and `A` and `B`
commute, then there is an orthonormal basis of `E` all of whose vectors are
simultaneously eigenvectors of `A` and of `B`. -/
theorem commuting_simultaneous {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ v : OrthonormalBasis (Fin n) 𝕜 E,
      ∀ i : Fin n, ∃ α β : 𝕜, A (v i) = α • v i ∧ B (v i) = β • v i := by
  classical
  -- The joint eigenspaces of `A` and `B`, indexed by pairs of scalars.
  set V : 𝕜 × 𝕜 → Submodule 𝕜 E :=
    fun i => (eigenspace A i.2 ⊓ eigenspace B i.1) with hV_def
  have hVint : DirectSum.IsInternal V :=
    hA.directSum_isInternal_of_commute hB hAB
  have hVorth : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ :=
    LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB
  -- Only finitely many of them are nonzero, so we may reindex by a finite type.
  have hindep : iSupIndep V :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top V |>.mp hVint).1
  letI : Fintype {i : 𝕜 × 𝕜 // V i ≠ ⊥} := hindep.fintypeNeBotOfFiniteDimensional
  set W : {i : 𝕜 × 𝕜 // V i ≠ ⊥} → Submodule 𝕜 E := fun i => V i.1 with hW_def
  have hWint : DirectSum.IsInternal W := DirectSum.isInternal_ne_bot_iff.mpr hVint
  have hWorth : OrthogonalFamily 𝕜 (fun i => W i) fun i => (W i).subtypeₗᵢ :=
    hVorth.comp Subtype.val_injective
  refine ⟨hWint.subordinateOrthonormalBasis hn hWorth, fun i => ?_⟩
  obtain ⟨hmemA, hmemB⟩ := hWint.subordinateOrthonormalBasis_subordinate hn i hWorth
  exact ⟨_, _, mem_eigenspace_iff.mp hmemA, mem_eigenspace_iff.mp hmemB⟩

end QPhys

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

