/-
  Brockian/WeylPlancherelScaffold.lean

  Plancherel/free-Laplacian input scaffold.

  `Brockian.Weyl.FourierMultiplier` already proves that essential
  self-adjointness of a position-space operator follows from dense plus/minus
  imaginary shifts of `M`
  ranges for a unitarily intertwined momentum multiplier.  This file names the
  exact remaining Fourier analytic interface for the genuine free Laplacian:

    * a Plancherel unitary `U` from momentum space to position space;
    * a momentum operator `M`, intended to be multiplication by `xi^2`;
    * a position operator `S`, intended to be `-d^2/dx^2`;
    * dense domain and dense ranges for the two non-real shifts of `M`;
    * the domain/action intertwining `S = U M U^{-1}`.

  Mathlib 4.32 does not expose an `L^2(R)` Plancherel Fourier unitary plus the
  maximal unbounded multiplier/domain API needed to instantiate these fields.
  The declarations below therefore do not claim the free Laplacian is done; they
  isolate precisely the inputs that will make the existing multiplier transfer
  fire once the analytic objects are available.
-/
import Brockian.WeylFourierMultiplier

namespace Brockian.WeylPlancherelScaffold

open scoped InnerProductSpace
open Brockian.Weyl.Cayley Brockian.Weyl.Operator
open Brockian.Weyl.FourierMultiplier

variable {K H : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A unitary already carries the Plancherel norm identity.  This small predicate
is useful for documentation and downstream theorem statements that want to speak
about "the Plancherel input" without depending on a concrete Fourier transform
construction. -/
def IsPlancherelUnitary (U : K ≃ₗᵢ[ℂ] H) : Prop :=
  ∀ f : K, ‖U f‖ = ‖f‖

/-- Every `LinearIsometryEquiv` is Plancherel in the norm-preservation sense. -/
theorem isPlancherelUnitary (U : K ≃ₗᵢ[ℂ] H) : IsPlancherelUnitary U := by
  intro f
  exact U.norm_map f

/-- The exact Plancherel/Fourier input needed for the free-Laplacian route.

In the intended application:

* `momentumSpace` is `L^2(R)` in frequency variables;
* `positionSpace` is `L^2(R)` in physical variables;
* `fourierUnitary` is inverse Fourier/Plancherel;
* `momentumMultiplier` is maximal multiplication by `xi^2`;
* `positionLaplacian` is the minimal or closure-compatible `-d^2/dx^2`;
* `domain_intertwines` and `action_intertwines` are the analytic identity
  `-d^2/dx^2 = F^{-1} xi^2 F`.

The dense range fields are exactly the two non-real shift facts consumed by the Cayley
criterion via `FourierMultiplierInput`. -/
structure PlancherelFreeLaplacianInput where
  fourierUnitary : K ≃ₗᵢ[ℂ] H
  momentumMultiplier : K →ₗ.[ℂ] K
  positionLaplacian : H →ₗ.[ℂ] H
  dense_domain_multiplier : Dense (momentumMultiplier.domain : Set K)
  domain_intertwines :
    positionLaplacian.domain = momentumMultiplier.domain.map fourierUnitary.toLinearMap
  action_intertwines :
    ∀ (y : positionLaplacian.domain) (x : momentumMultiplier.domain),
      (y : H) = fourierUnitary (x : K) →
        positionLaplacian y = fourierUnitary (momentumMultiplier x)
  dense_range_addI_multiplier : Dense (rangeAddI momentumMultiplier : Set K)
  dense_range_subI_multiplier : Dense (rangeSubI momentumMultiplier : Set K)

namespace PlancherelFreeLaplacianInput

/-- The Plancherel unitary field has the norm-preservation identity. -/
theorem isPlancherel (P : PlancherelFreeLaplacianInput (K := K) (H := H)) :
    IsPlancherelUnitary P.fourierUnitary :=
  isPlancherelUnitary P.fourierUnitary

/-- Forget the Plancherel/free-Laplacian names and produce the existing
`FourierMultiplierInput` consumed by the Weyl multiplier transfer layer. -/
def toFourierMultiplierInput
    (P : PlancherelFreeLaplacianInput (K := K) (H := H)) :
    FourierMultiplierInput (K := K) (H := H) where
  M := P.momentumMultiplier
  S := P.positionLaplacian
  U := P.fourierUnitary
  dense_domain_M := P.dense_domain_multiplier
  domain_intertwines := P.domain_intertwines
  action_intertwines := P.action_intertwines
  dense_range_addI_M := P.dense_range_addI_multiplier
  dense_range_subI_M := P.dense_range_subI_multiplier

/-- The position-space free-Laplacian candidate has dense domain once the
Plancherel input is supplied. -/
theorem dense_domain_position
    (P : PlancherelFreeLaplacianInput (K := K) (H := H)) :
    Dense (P.positionLaplacian.domain : Set H) :=
  P.toFourierMultiplierInput.dense_domain_position

/-- Dense range of `S + i` follows from dense range of the multiplier `M + i`
through the Plancherel intertwining. -/
theorem dense_range_addI_position
    (P : PlancherelFreeLaplacianInput (K := K) (H := H)) :
    Dense (rangeAddI P.positionLaplacian : Set H) :=
  (dense_rangeAddI_transfer_iff P.fourierUnitary P.domain_intertwines
    P.action_intertwines).mpr P.dense_range_addI_multiplier

/-- Dense range of `S - i` follows from dense range of the multiplier `M - i`
through the Plancherel intertwining. -/
theorem dense_range_subI_position
    (P : PlancherelFreeLaplacianInput (K := K) (H := H)) :
    Dense (rangeSubI P.positionLaplacian : Set H) :=
  (dense_rangeSubI_transfer_iff P.fourierUnitary P.domain_intertwines
    P.action_intertwines).mpr P.dense_range_subI_multiplier

/-- The exact Gate-1 consequence of a completed Plancherel/free-Laplacian input:
the position-space free-Laplacian candidate is essentially self-adjoint. -/
theorem essentiallySelfAdjoint_position
    (P : PlancherelFreeLaplacianInput (K := K) (H := H)) :
    EssentiallySelfAdjoint P.positionLaplacian :=
  P.toFourierMultiplierInput.essentiallySelfAdjoint_position

/-- If the multiplier side is already known to be essentially self-adjoint, the
same Plancherel domain/action data also transfers ESA to the position operator.
This records compatibility with the older `freeLaplacian_essentiallySelfAdjoint`
route, while the structure above records the stronger dense-range inputs. -/
theorem essentiallySelfAdjoint_position_of_multiplier_esa
    (P : PlancherelFreeLaplacianInput (K := K) (H := H))
    (hM : EssentiallySelfAdjoint P.momentumMultiplier) :
    EssentiallySelfAdjoint P.positionLaplacian :=
  essentiallySelfAdjoint_of_multiplier_esa P.fourierUnitary
    P.dense_domain_multiplier hM P.domain_intertwines P.action_intertwines

end PlancherelFreeLaplacianInput

/-- A lighter constructor theorem for downstream modules that have the analytic
Fourier facts as separate hypotheses and do not want to build the structure by
hand. -/
theorem essentiallySelfAdjoint_of_plancherel_multiplier_dense_ranges
    (U : K ≃ₗᵢ[ℂ] H) {M : K →ₗ.[ℂ] K} {S : H →ₗ.[ℂ] H}
    (hMdom : Dense (M.domain : Set K))
    (hdom : S.domain = M.domain.map U.toLinearMap)
    (hact : ∀ (y : S.domain) (x : M.domain), (y : H) = U (x : K) → S y = U (M x))
    (hM_add : Dense (rangeAddI M : Set K))
    (hM_sub : Dense (rangeSubI M : Set K)) :
    EssentiallySelfAdjoint S :=
  essentiallySelfAdjoint_of_multiplier_dense_ranges U hMdom hdom hact hM_add hM_sub

end Brockian.WeylPlancherelScaffold
