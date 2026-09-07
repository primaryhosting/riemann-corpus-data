/-
  Brockian/WeylFreeLaplacian.lean — free-Laplacian / Fourier-model first rung.

  ## What is proved

  1. **Unitary conjugation preserves self-adjointness and essential self-adjointness**
     for bounded operators (`conjCLM`). Transfer lemma for the Fourier route:
     ESA of a momentum-space real multiplication (bounded cutoff) transfers to
     position space.

  2. **Identity free model** is essentially self-adjoint.

  3. **Bounded self-adjoint perturbation preserves symmetry** of a densely-defined
     symmetric `LinearPMap` (`isSymmetric_vadd_clm`). Symmetry half of unbounded
     Kato–Rellich; range-density half remains open for unbounded free parts.

  ## What is NOT proved

  * Construction of the genuine unbounded free Laplacian `−d²/dx²` on `L²(ℝ)`.
  * Fourier transform as a unitary `L² → L²` with multiplication by `ξ²`.
  * Full unbounded Kato–Rellich (dense ranges of `(T+B) ± i`).

  Owner: Grok (queue #2). Do not clobber without coordination.
  Verification (spec §2A): AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylOperator
import Brockian.WeylEssSelfAdjoint

namespace Brockian.Weyl.FreeLaplacian

open scoped InnerProductSpace
open Brockian.Weyl.Operator Brockian.Weyl.ESA

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Unitary conjugation of bounded operators -/

/-- Conjugation of a bounded operator by a unitary: `U A U⁻¹`. -/
noncomputable def conjCLM (U : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) : K →L[ℂ] K :=
  LinearMap.mkContinuous
    { toFun := fun y => U (A (U.symm y))
      map_add' := by intro x y; simp [map_add]
      map_smul' := by intro c x; simp [map_smul] }
    ‖A‖
    (fun y => by
      -- ‖U (A (U.symm y))‖ = ‖A (U.symm y)‖ ≤ ‖A‖ ‖U.symm y‖ = ‖A‖ ‖y‖
      simpa [U.norm_map, U.symm.norm_map] using A.le_opNorm (U.symm y))

@[simp] theorem conjCLM_apply (U : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) (y : K) :
    conjCLM U A y = U (A (U.symm y)) :=
  rfl

/-- Unitary isometry form of the adjoint relation: `⟪U a, b⟫ = ⟪a, U⁻¹ b⟫`. -/
theorem inner_map_symm (U : H ≃ₗᵢ[ℂ] K) (a : H) (b : K) :
    ⟪U a, b⟫_ℂ = ⟪a, U.symm b⟫_ℂ := by
  rw [← U.inner_map_map a (U.symm b), U.apply_symm_apply]

/-- Symmetric form: `⟪a, U c⟫ = ⟪U⁻¹ a, c⟫`. -/
theorem inner_symm_map (U : H ≃ₗᵢ[ℂ] K) (a : K) (c : H) :
    ⟪a, U c⟫_ℂ = ⟪U.symm a, c⟫_ℂ := by
  calc ⟪a, U c⟫_ℂ
      = ⟪U (U.symm a), U c⟫_ℂ := by rw [U.apply_symm_apply]
    _ = ⟪U.symm a, c⟫_ℂ := U.inner_map_map _ _

/-- Unitary conjugation preserves self-adjointness (inner-product proof). -/
theorem isSelfAdjoint_conjCLM (U : H ≃ₗᵢ[ℂ] K) {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (conjCLM U A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hAs : ∀ u v : H, ⟪A u, v⟫_ℂ = ⟪u, A v⟫_ℂ := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA
    exact hA
  -- unfold conjugation to `U (A (U.symm ·))`
  change ⟪U (A (U.symm x)), y⟫_ℂ = ⟪x, U (A (U.symm y))⟫_ℂ
  calc ⟪U (A (U.symm x)), y⟫_ℂ
      = ⟪A (U.symm x), U.symm y⟫_ℂ := inner_map_symm U _ _
    _ = ⟪U.symm x, A (U.symm y)⟫_ℂ := hAs _ _
    _ = ⟪x, U (A (U.symm y))⟫_ℂ := (inner_symm_map U x _).symm

/-- **ESA transfers under unitary conjugation** (bounded case). -/
theorem essentiallySelfAdjoint_conjCLM (U : H ≃ₗᵢ[ℂ] K) {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) :
    EssentiallySelfAdjoint ((conjCLM U A).toPMap ⊤) :=
  clm_essentiallySelfAdjoint _ (isSelfAdjoint_conjCLM U hA)

/-- The identity operator is essentially self-adjoint. -/
theorem id_essentiallySelfAdjoint :
    EssentiallySelfAdjoint ((1 : H →L[ℂ] H).toPMap ⊤) :=
  clm_essentiallySelfAdjoint _ (IsSelfAdjoint.one (R := H →L[ℂ] H))

/-- Conjugation of the identity is ESA. -/
theorem essentiallySelfAdjoint_conj_id (U : H ≃ₗᵢ[ℂ] K) :
    EssentiallySelfAdjoint ((conjCLM U (1 : H →L[ℂ] H)).toPMap ⊤) :=
  essentiallySelfAdjoint_conjCLM U (IsSelfAdjoint.one (R := H →L[ℂ] H))

/-! ### Abstract free-Laplacian model (Fourier shape; bounded cutoffs only) -/

/-- **Fourier-model free Laplacian (bounded cutoff).** Unitary `U` plus bounded
self-adjoint momentum operator `M`. Transferred free operator is ESA.

Inhabiting with genuine unbounded `−Δ` is the remaining Mathlib-scale step. -/
structure FreeLaplacianModel (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  K : Type*
  [normedK : NormedAddCommGroup K]
  [innerK : InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]
  U : H ≃ₗᵢ[ℂ] K
  M : K →L[ℂ] K
  hM : IsSelfAdjoint M

attribute [instance] FreeLaplacianModel.normedK FreeLaplacianModel.innerK
  FreeLaplacianModel.completeK

/-- The transferred free operator on position space: `U⁻¹ M U`. -/
noncomputable def FreeLaplacianModel.freeOp (F : FreeLaplacianModel H) : H →L[ℂ] H :=
  conjCLM F.U.symm F.M

theorem FreeLaplacianModel.isSelfAdjoint_freeOp (F : FreeLaplacianModel H) :
    IsSelfAdjoint F.freeOp :=
  isSelfAdjoint_conjCLM F.U.symm F.hM

/-- **ESA of a free-Laplacian model.** -/
theorem FreeLaplacianModel.essentiallySelfAdjoint_freeOp (F : FreeLaplacianModel H) :
    EssentiallySelfAdjoint (F.freeOp.toPMap ⊤) :=
  clm_essentiallySelfAdjoint _ F.isSelfAdjoint_freeOp

/-- Concrete inhabitant: identity kinetic energy (`U = id`, `M = 1`). -/
noncomputable def identityFreeModel : FreeLaplacianModel H where
  K := H
  U := LinearIsometryEquiv.refl ℂ H
  M := (1 : H →L[ℂ] H)
  hM := IsSelfAdjoint.one (R := H →L[ℂ] H)

/-! ### Unbounded Kato — symmetry half -/

/-- **Bounded self-adjoint perturbation preserves symmetry.** Symmetry half of
unbounded Kato–Rellich; dense-range transfer for `(T+B)±i` is still open. -/
theorem isSymmetric_vadd_clm (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (T : H →ₗ.[ℂ] H) (hT : IsSymmetric T) :
    IsSymmetric (B.toLinearMap +ᵥ T) := by
  intro x y
  have hBsymm : ⟪B (x : H), (y : H)⟫_ℂ = ⟪(x : H), B (y : H)⟫_ℂ := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hB
    exact hB x y
  have hTsymm : ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ := hT x y
  simp only [LinearPMap.vadd_apply, ContinuousLinearMap.coe_coe]
  rw [inner_add_left, inner_add_right, hBsymm, hTsymm]

omit [CompleteSpace H] in
theorem vadd_clm_domain (B : H →L[ℂ] H) (T : H →ₗ.[ℂ] H) :
    (B.toLinearMap +ᵥ T).domain = T.domain :=
  LinearPMap.vadd_domain _ _

theorem dense_domain_vadd_clm (B : H →L[ℂ] H) {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) :
    Dense ((B.toLinearMap +ᵥ T).domain : Set H) := by
  rwa [vadd_clm_domain]

end Brockian.Weyl.FreeLaplacian
