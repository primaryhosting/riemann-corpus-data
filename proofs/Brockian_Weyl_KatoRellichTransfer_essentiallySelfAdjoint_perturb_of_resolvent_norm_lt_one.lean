/-
  Brockian/WeylKatoRellichTransfer.lean

  Kato--Rellich bounded-perturbation transfer, in the strongest form currently
  supported by the verified Brockian/Mathlib 4.32 infrastructure.

  This file composes the existing Neumann/resolvent lane:

      right resolvents for T ± i
        + small bounded factors I + B R_±
        -> full perturbed ranges ran((T+B)±i) = H
        -> BoundedPerturbationTransfer T B
        -> EssentiallySelfAdjoint (perturb T B)

  It deliberately does not assert the full unconditional Kato--Rellich theorem.
  The missing classical step is the construction of the shifted resolvents of
  the self-adjoint closure, with the resolvent bound needed to make the Neumann
  factor small.  That remains absent from Mathlib's unbounded-operator API.
-/
import Mathlib
import Brockian.WeylChain
import Brockian.WeylKatoRangeDensity
import Brockian.WeylKatoNeumann
import Brockian.WeylKatoNeumannEstimates

namespace Brockian.Weyl.KatoRellichTransfer

open scoped InnerProductSpace
open Brockian.Weyl.Cayley
open Brockian.Weyl.KatoRellichScaffold
open Brockian.Weyl.KatoUnbounded
open Brockian.Weyl.KatoNeumann
open Brockian.Weyl.KatoNeumannEstimates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Full ranges imply the named Kato transfer -/

/-- If both shifted perturbed ranges are all of `H`, then the named bounded
perturbation transfer hypothesis holds. -/
theorem boundedPerturbationTransfer_of_ranges_eq_univ
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hadd : (rangeAddI (perturb T B) : Set H) = Set.univ)
    (hsub : (rangeSubI (perturb T B) : Set H) = Set.univ) :
    BoundedPerturbationTransfer T B := by
  constructor
  · rw [hadd]
    exact dense_univ
  · rw [hsub]
    exact dense_univ

/-- Full shifted perturbed ranges close the essential-self-adjointness criterion
for the perturbation. -/
theorem essentiallySelfAdjoint_perturb_of_ranges_eq_univ
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H))
    (hadd : (rangeAddI (perturb T B) : Set H) = Set.univ)
    (hsub : (rangeSubI (perturb T B) : Set H) = Set.univ) :
    EssentiallySelfAdjoint (perturb T B) :=
  essentiallySelfAdjoint_perturb hd
    (boundedPerturbationTransfer_of_ranges_eq_univ hadd hsub)

/-! ### Small Neumann factors give full perturbed ranges -/

/-- Small-norm Neumann factors, stated with `‖B.comp R‖ < 1`, give surjectivity
of both shifted perturbed ranges. -/
theorem perturbed_ranges_eq_univ_of_resolvent_norm_lt_one
    {T : H →ₗ.[ℂ] H} {B Radd Rsub : H →L[ℂ] H}
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hBRadd : ‖B.comp Radd‖ < 1)
    (hRsub : RightResolvent T Complex.I Rsub)
    (hBRsub : ‖B.comp Rsub‖ < 1) :
    (rangeAddI (perturb T B) : Set H) = Set.univ ∧
      (rangeSubI (perturb T B) : Set H) = Set.univ :=
  ⟨rangeAddI_perturb_eq_univ_of_resolvent_norm_lt_one hRadd hBRadd,
    rangeSubI_perturb_eq_univ_of_resolvent_norm_lt_one hRsub hBRsub⟩

/-- Product-norm estimates `‖B‖ * ‖R_±‖ < 1` give surjectivity of both shifted
perturbed ranges. -/
theorem perturbed_ranges_eq_univ_of_resolvent_norm_mul_lt_one
    {T : H →ₗ.[ℂ] H} {B Radd Rsub : H →L[ℂ] H}
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hBRadd : ‖B‖ * ‖Radd‖ < 1)
    (hRsub : RightResolvent T Complex.I Rsub)
    (hBRsub : ‖B‖ * ‖Rsub‖ < 1) :
    (rangeAddI (perturb T B) : Set H) = Set.univ ∧
      (rangeSubI (perturb T B) : Set H) = Set.univ :=
  ⟨rangeAddI_perturb_eq_univ_of_resolvent_norm_mul_lt_one hRadd hBRadd,
    rangeSubI_perturb_eq_univ_of_resolvent_norm_mul_lt_one hRsub hBRsub⟩

/-- Small-norm Neumann factors, stated with `‖B.comp R‖ < 1`, give the named
bounded perturbation transfer hypothesis. -/
theorem boundedPerturbationTransfer_of_resolvent_comp_norm_lt_one
    {T : H →ₗ.[ℂ] H} {B Radd Rsub : H →L[ℂ] H}
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hBRadd : ‖B.comp Radd‖ < 1)
    (hRsub : RightResolvent T Complex.I Rsub)
    (hBRsub : ‖B.comp Rsub‖ < 1) :
    BoundedPerturbationTransfer T B := by
  exact boundedPerturbationTransfer_of_resolvent_norm_lt_one
    hRadd hBRadd hRsub hBRsub

/-- Product-norm estimates give the named bounded perturbation transfer
hypothesis. -/
theorem boundedPerturbationTransfer_of_resolvent_product_norm_lt_one
    {T : H →ₗ.[ℂ] H} {B Radd Rsub : H →L[ℂ] H}
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hBRadd : ‖B‖ * ‖Radd‖ < 1)
    (hRsub : RightResolvent T Complex.I Rsub)
    (hBRsub : ‖B‖ * ‖Rsub‖ < 1) :
    BoundedPerturbationTransfer T B := by
  exact boundedPerturbationTransfer_of_resolvent_norm_mul_lt_one
    hRadd hBRadd hRsub hBRsub

/-! ### The A4 transfer endpoint: right resolvents plus smallness imply ESA -/

/-- **Kato--Rellich transfer, Neumann-factor form.** If `T ± i` have bounded
right resolvents and the corresponding factors `I + B R_±` are Neumann-small,
then the bounded perturbation `T+B` is essentially self-adjoint. -/
theorem essentiallySelfAdjoint_perturb_of_resolvent_norm_lt_one
    {T : H →ₗ.[ℂ] H} {B Radd Rsub : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H))
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hBRadd : ‖B.comp Radd‖ < 1)
    (hRsub : RightResolvent T Complex.I Rsub)
    (hBRsub : ‖B.comp Rsub‖ < 1) :
    EssentiallySelfAdjoint (perturb T B) :=
  essentiallySelfAdjoint_perturb hd
    (boundedPerturbationTransfer_of_resolvent_norm_lt_one
      hRadd hBRadd hRsub hBRsub)

/-- **Kato--Rellich transfer, product-estimate form.** If `T ± i` have bounded
right resolvents and `‖B‖ * ‖R_±‖ < 1`, then `T+B` is essentially
self-adjoint. This is the directly usable A4 bridge exported by this file. -/
theorem essentiallySelfAdjoint_perturb_of_resolvent_norm_mul_lt_one
    {T : H →ₗ.[ℂ] H} {B Radd Rsub : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H))
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hBRadd : ‖B‖ * ‖Radd‖ < 1)
    (hRsub : RightResolvent T Complex.I Rsub)
    (hBRsub : ‖B‖ * ‖Rsub‖ < 1) :
    EssentiallySelfAdjoint (perturb T B) :=
  essentiallySelfAdjoint_perturb hd
    (boundedPerturbationTransfer_of_resolvent_norm_mul_lt_one
      hRadd hBRadd hRsub hBRsub)

/-- The same product-estimate transfer written directly through the Weyl chain:
full ranges imply dense ranges, and dense ranges imply essential
self-adjointness. This records explicitly how the A4 bridge plugs into
`WeylChain.essSelfAdjoint_of_dense_ranges`. -/
theorem essentiallySelfAdjoint_perturb_of_resolvent_norm_mul_lt_one_via_chain
    {T : H →ₗ.[ℂ] H} {B Radd Rsub : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H))
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hBRadd : ‖B‖ * ‖Radd‖ < 1)
    (hRsub : RightResolvent T Complex.I Rsub)
    (hBRsub : ‖B‖ * ‖Rsub‖ < 1) :
    EssentiallySelfAdjoint (perturb T B) := by
  have hranges :=
    perturbed_ranges_eq_univ_of_resolvent_norm_mul_lt_one
      hRadd hBRadd hRsub hBRsub
  exact Brockian.Weyl.Chain.essSelfAdjoint_of_dense_ranges
    (perturb_dense_domain B hd)
    (by rw [hranges.1]; exact dense_univ)
    (by rw [hranges.2]; exact dense_univ)

end Brockian.Weyl.KatoRellichTransfer
