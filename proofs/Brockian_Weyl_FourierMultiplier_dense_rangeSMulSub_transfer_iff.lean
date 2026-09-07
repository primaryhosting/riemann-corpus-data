/-
  Brockian/WeylFourierMultiplier.lean

  A narrow Fourier/free-Laplacian transfer layer.

  `WeylFreeLaplacian2` already proves the main unitary-transfer theorem:
  essential self-adjointness transfers from a momentum-space operator `M` to a
  position-space operator `S` when `S = U M U⁻¹` as a `LinearPMap`.

  This file factors the remaining Fourier multiplier input one level lower:
  it is enough to prove dense range of the two non-real shifts of the multiplier
  model.  The lemmas below transport those dense-range facts across the unitary
  intertwiner and then close essential self-adjointness by the Cayley criterion.

  Scope: no construction of the real Fourier transform on `L²(ℝ)`, no unbounded
  multiplication domain, and no claim about `−d²/dx²` beyond the explicit
  hypotheses.
-/
import Brockian.WeylFreeLaplacian2
import Brockian.WeylChain

namespace Brockian.Weyl.FourierMultiplier

open scoped InnerProductSpace
open Brockian.Weyl.Operator Brockian.Weyl.Cayley Brockian.Weyl.Chain

variable {K H : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Dense range of an arbitrary non-real shift transfers across a unitary
intertwining of partially-defined operators.  This is the range-density form of
the Fourier multiplier route: once `S` is known to be `U M U⁻¹`, no extra
analysis is needed to move density from momentum space to position space. -/
theorem dense_rangeSMulSub_transfer_iff
    (U : K ≃ₗᵢ[ℂ] H) {M : K →ₗ.[ℂ] K} {S : H →ₗ.[ℂ] H}
    (hdom : S.domain = M.domain.map U.toLinearMap)
    (hact : ∀ (y : S.domain) (x : M.domain), (y : H) = U (x : K) → S y = U (M x))
    (w : ℂ) :
    Dense (rangeSMulSub S w : Set H) ↔ Dense (rangeSMulSub M w : Set K) := by
  rw [Brockian.Weyl.FreeLaplacian2.rangeSMulSub_image U hdom hact w]
  exact U.toHomeomorph.isDenseEmbedding.dense_image

/-- The `T + i` Cayley range is dense after Fourier transfer iff the
momentum-space `M + i` range is dense. -/
theorem dense_rangeAddI_transfer_iff
    (U : K ≃ₗᵢ[ℂ] H) {M : K →ₗ.[ℂ] K} {S : H →ₗ.[ℂ] H}
    (hdom : S.domain = M.domain.map U.toLinearMap)
    (hact : ∀ (y : S.domain) (x : M.domain), (y : H) = U (x : K) → S y = U (M x)) :
    Dense (rangeAddI S : Set H) ↔ Dense (rangeAddI M : Set K) := by
  exact dense_rangeSMulSub_transfer_iff U hdom hact (-Complex.I)

/-- The `T - i` Cayley range is dense after Fourier transfer iff the
momentum-space `M - i` range is dense. -/
theorem dense_rangeSubI_transfer_iff
    (U : K ≃ₗᵢ[ℂ] H) {M : K →ₗ.[ℂ] K} {S : H →ₗ.[ℂ] H}
    (hdom : S.domain = M.domain.map U.toLinearMap)
    (hact : ∀ (y : S.domain) (x : M.domain), (y : H) = U (x : K) → S y = U (M x)) :
    Dense (rangeSubI S : Set H) ↔ Dense (rangeSubI M : Set K) := by
  exact dense_rangeSMulSub_transfer_iff U hdom hact Complex.I

/-- Dense domain transfers from the momentum multiplier to the position operator
under the same unitary domain identity. -/
theorem dense_domain_transfer
    (U : K ≃ₗᵢ[ℂ] H) {M : K →ₗ.[ℂ] K} {S : H →ₗ.[ℂ] H}
    (hMdom : Dense (M.domain : Set K))
    (hdom : S.domain = M.domain.map U.toLinearMap) :
    Dense (S.domain : Set H) := by
  rw [hdom]
  exact (Brockian.Weyl.FreeLaplacian2.dense_map_iff U M.domain).mpr hMdom

/-- **Fourier multiplier dense-range criterion.**

If a position-space operator `S` is unitarily intertwined with a densely-defined
momentum multiplier `M`, and the two Cayley ranges of `M` are dense, then `S` is
essentially self-adjoint.  This is the useful reduction for the genuine free
Laplacian: the remaining analytic work is exactly dense range of
`M ± i`, where `M` is multiplication by `ξ²` on its maximal `L²` domain, plus the
Fourier intertwining identity. -/
theorem essentiallySelfAdjoint_of_multiplier_dense_ranges
    (U : K ≃ₗᵢ[ℂ] H) {M : K →ₗ.[ℂ] K} {S : H →ₗ.[ℂ] H}
    (hMdom : Dense (M.domain : Set K))
    (hdom : S.domain = M.domain.map U.toLinearMap)
    (hact : ∀ (y : S.domain) (x : M.domain), (y : H) = U (x : K) → S y = U (M x))
    (hM_add : Dense (rangeAddI M : Set K))
    (hM_sub : Dense (rangeSubI M : Set K)) :
    EssentiallySelfAdjoint S := by
  exact essSelfAdjoint_of_dense_ranges
    (dense_domain_transfer U hMdom hdom)
    ((dense_rangeAddI_transfer_iff U hdom hact).mpr hM_add)
    ((dense_rangeSubI_transfer_iff U hdom hact).mpr hM_sub)

/-- Same reduction packaged with arbitrary non-real shift notation.  The hypotheses
are intentionally `rangeSMulSub M (-I)` and `rangeSMulSub M I`, matching the
multiplier equation `(M + i)f = g` and `(M - i)f = g` directly. -/
theorem essentiallySelfAdjoint_of_multiplier_shift_dense
    (U : K ≃ₗᵢ[ℂ] H) {M : K →ₗ.[ℂ] K} {S : H →ₗ.[ℂ] H}
    (hMdom : Dense (M.domain : Set K))
    (hdom : S.domain = M.domain.map U.toLinearMap)
    (hact : ∀ (y : S.domain) (x : M.domain), (y : H) = U (x : K) → S y = U (M x))
    (hM_plus : Dense (rangeSMulSub M (-Complex.I) : Set K))
    (hM_minus : Dense (rangeSMulSub M Complex.I : Set K)) :
    EssentiallySelfAdjoint S := by
  exact essentiallySelfAdjoint_of_multiplier_dense_ranges U hMdom hdom hact hM_plus hM_minus

/-- If the multiplier model is already known to be essentially self-adjoint, the
dense-range criterion above recovers the usual unitary-transfer theorem.  This
declaration records the compatibility between the "prove `M ± i` dense" route
and the existing `WeylFreeLaplacian2` ESA-transfer route. -/
theorem essentiallySelfAdjoint_of_multiplier_esa
    (U : K ≃ₗᵢ[ℂ] H) {M : K →ₗ.[ℂ] K} {S : H →ₗ.[ℂ] H}
    (hMdom : Dense (M.domain : Set K))
    (hM : EssentiallySelfAdjoint M)
    (hdom : S.domain = M.domain.map U.toLinearMap)
    (hact : ∀ (y : S.domain) (x : M.domain), (y : H) = U (x : K) → S y = U (M x)) :
    EssentiallySelfAdjoint S := by
  have hMranges := (essentiallySelfAdjoint_iff hMdom).mp hM
  exact essentiallySelfAdjoint_of_multiplier_dense_ranges U hMdom hdom hact hMranges.1 hMranges.2

/-- A compact witness object for the Fourier multiplier input.  Future modules can
instantiate this with the Plancherel Fourier unitary and the maximal
multiplication-by-`ξ²` operator without restating the transfer hypotheses. -/
structure FourierMultiplierInput where
  M : K →ₗ.[ℂ] K
  S : H →ₗ.[ℂ] H
  U : K ≃ₗᵢ[ℂ] H
  dense_domain_M : Dense (M.domain : Set K)
  domain_intertwines : S.domain = M.domain.map U.toLinearMap
  action_intertwines :
    ∀ (y : S.domain) (x : M.domain), (y : H) = U (x : K) → S y = U (M x)
  dense_range_addI_M : Dense (rangeAddI M : Set K)
  dense_range_subI_M : Dense (rangeSubI M : Set K)

namespace FourierMultiplierInput

/-- The position-space operator associated to a completed Fourier multiplier input
is essentially self-adjoint. -/
theorem essentiallySelfAdjoint_position (F : FourierMultiplierInput (K := K) (H := H)) :
    EssentiallySelfAdjoint F.S :=
  essentiallySelfAdjoint_of_multiplier_dense_ranges F.U F.dense_domain_M
    F.domain_intertwines F.action_intertwines F.dense_range_addI_M F.dense_range_subI_M

/-- The intertwined position operator has dense domain. -/
theorem dense_domain_position (F : FourierMultiplierInput (K := K) (H := H)) :
    Dense (F.S.domain : Set H) :=
  dense_domain_transfer F.U F.dense_domain_M F.domain_intertwines

end FourierMultiplierInput

end Brockian.Weyl.FourierMultiplier
