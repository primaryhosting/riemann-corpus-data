/-
  Brockian/WeylKatoRangeDensity.lean — range-density consequences for the
  bounded-perturbation (Kato) lane.

  This file deliberately does not prove the full unbounded Kato--Rellich theorem.
  Instead it records the unconditional pieces already available from the repo's
  `EssentiallySelfAdjoint` / `rangeSMulSub` API:

    * unpacking and repacking `BoundedPerturbationTransfer`;
    * deriving the transfer hypothesis from ESA of the perturbed operator;
    * upgrading dense perturbed ranges to all of `H` under closed-range hypotheses;
    * bounded and zero-perturbation witnesses where the transfer is genuinely
      discharged by existing verified theorems.

  The missing unbounded step remains the resolvent/closed-range argument deriving
  `BoundedPerturbationTransfer T B` from `EssentiallySelfAdjoint T` for unbounded
  `T`.
-/
import Mathlib
import Brockian.WeylKatoUnbounded
import Brockian.WeylClosedRange

namespace Brockian.Weyl.KatoRangeDensity

open scoped InnerProductSpace
open Brockian.Weyl.Operator
open Brockian.Weyl.Cayley
open Brockian.Weyl.KatoUnbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Transfer unpacking and the ESA criterion -/

/-- `BoundedPerturbationTransfer` is exactly the pair of dense perturbed Cayley
ranges. This named iff is useful for downstream code that should not unfold the
conditional target manually. -/
theorem boundedPerturbationTransfer_iff_dense_ranges
    (T : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) :
    BoundedPerturbationTransfer T B ↔
      Dense (rangeAddI (perturb T B) : Set H) ∧
      Dense (rangeSubI (perturb T B) : Set H) :=
  Iff.rfl

/-- First projection of the perturbation transfer hypothesis: `ran((T+B)+i)` is
dense. -/
theorem dense_rangeAddI_perturb_of_transfer
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (h : BoundedPerturbationTransfer T B) :
    Dense (rangeAddI (perturb T B) : Set H) :=
  h.1

/-- Second projection of the perturbation transfer hypothesis: `ran((T+B)-i)` is
dense. -/
theorem dense_rangeSubI_perturb_of_transfer
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (h : BoundedPerturbationTransfer T B) :
    Dense (rangeSubI (perturb T B) : Set H) :=
  h.2

/-- ESA of the perturbed operator implies the named range-density transfer
hypothesis. This is the reverse direction of the specialized Cayley criterion. -/
theorem boundedPerturbationTransfer_of_essentiallySelfAdjoint_perturb
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H))
    (h : EssentiallySelfAdjoint (perturb T B)) :
    BoundedPerturbationTransfer T B :=
  (essentiallySelfAdjoint_perturb_iff B hd).mp h

/-- For a densely-defined operator, the Kato transfer hypothesis is equivalent to
essential self-adjointness of the perturbed operator. This is just the specialized
Cayley criterion with the transfer target named. -/
theorem essentiallySelfAdjoint_perturb_iff_transfer
    {T : H →ₗ.[ℂ] H} (B : H →L[ℂ] H)
    (hd : Dense (T.domain : Set H)) :
    EssentiallySelfAdjoint (perturb T B) ↔ BoundedPerturbationTransfer T B :=
  essentiallySelfAdjoint_perturb_iff B hd

/-! ### Dense + closed range upgrades -/

/-- If the `+i` perturbed range is closed, the transfer hypothesis upgrades its
density to surjectivity. This isolates the pure topology half of the closed-range
Kato route. -/
theorem rangeAddI_perturb_eq_univ_of_transfer_of_isClosed
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (h : BoundedPerturbationTransfer T B)
    (hclosed : IsClosed (rangeAddI (perturb T B) : Set H)) :
    (rangeAddI (perturb T B) : Set H) = Set.univ :=
  Brockian.Weyl.ClosedRange.eq_univ_of_dense_isClosed h.1 hclosed

/-- If the `-i` perturbed range is closed, the transfer hypothesis upgrades its
density to surjectivity. -/
theorem rangeSubI_perturb_eq_univ_of_transfer_of_isClosed
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (h : BoundedPerturbationTransfer T B)
    (hclosed : IsClosed (rangeSubI (perturb T B) : Set H)) :
    (rangeSubI (perturb T B) : Set H) = Set.univ :=
  Brockian.Weyl.ClosedRange.eq_univ_of_dense_isClosed h.2 hclosed

/-- Closedness of both perturbed Cayley ranges turns the transfer hypothesis into
surjectivity of both ranges. This is the exact closed-range form needed by a
future resolvent proof. -/
theorem perturbed_ranges_eq_univ_of_transfer_of_isClosed
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (h : BoundedPerturbationTransfer T B)
    (hclosed_add : IsClosed (rangeAddI (perturb T B) : Set H))
    (hclosed_sub : IsClosed (rangeSubI (perturb T B) : Set H)) :
    (rangeAddI (perturb T B) : Set H) = Set.univ ∧
      (rangeSubI (perturb T B) : Set H) = Set.univ :=
  ⟨rangeAddI_perturb_eq_univ_of_transfer_of_isClosed h hclosed_add,
    rangeSubI_perturb_eq_univ_of_transfer_of_isClosed h hclosed_sub⟩

/-! ### Honest witnesses: zero and bounded perturbations -/

/-- The zero bounded perturbation leaves a partial operator unchanged. -/
theorem perturb_zero_eq (T : H →ₗ.[ℂ] H) :
    perturb T (0 : H →L[ℂ] H) = T := by
  apply LinearPMap.ext
  · rw [perturb_domain]
  · intro x hxT hxP
    have hxT' : x ∈ T.domain := by
      rwa [perturb_domain] at hxT
    change (0 : H →L[ℂ] H) x + T ⟨x, hxT'⟩ = T ⟨x, hxP⟩
    simp only [ContinuousLinearMap.zero_apply, zero_add]

/-- The transfer target is discharged for the zero perturbation of an essentially
self-adjoint densely-defined operator. This is not Kato--Rellich; it is the base
case that the named transfer hypothesis is aligned with the Cayley criterion. -/
theorem boundedPerturbationTransfer_zero_of_essentiallySelfAdjoint
    {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (hT : EssentiallySelfAdjoint T) :
    BoundedPerturbationTransfer T (0 : H →L[ℂ] H) := by
  rw [boundedPerturbationTransfer_iff_dense_ranges, perturb_zero_eq]
  exact (Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff hd).mp hT

/-- The bounded self-adjoint witness, restated in range-density form for direct
use by the Kato/range-density route. -/
theorem boundedSelfAdjoint_perturb_dense_ranges
    {A B : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    Dense (rangeAddI (perturb (A.toPMap ⊤) B) : Set H) ∧
      Dense (rangeSubI (perturb (A.toPMap ⊤) B) : Set H) :=
  boundedPerturbationTransfer_clm hA hB

/-- The bounded self-adjoint witness, restated as ESA of the perturbed partial
operator through the transfer equivalence in this file. -/
theorem boundedSelfAdjoint_perturb_essentiallySelfAdjoint
    {A B : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    EssentiallySelfAdjoint (perturb (A.toPMap ⊤) B) :=
  (essentiallySelfAdjoint_perturb_iff_transfer B (Brockian.Weyl.ESA.clm_dense A)).mpr
    (boundedPerturbationTransfer_clm hA hB)

end Brockian.Weyl.KatoRangeDensity
