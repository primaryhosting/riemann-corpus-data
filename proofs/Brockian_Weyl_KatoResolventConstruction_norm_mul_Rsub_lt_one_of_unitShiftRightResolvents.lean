/-
  Brockian/WeylKatoResolventConstruction.lean

  A concrete resolvent package for the Kato--Rellich lane.

  The full self-adjoint-closure resolvent construction is still absent from
  Mathlib 4.32.  This file records the exact usable interface: bounded right
  resolvents for the unit shifts, with the classical `≤ 1` norm bound, imply the
  Neumann smallness hypotheses as soon as the bounded perturbation has norm
  `< 1`.  The conclusion is the existing essential-self-adjointness transfer for
  `T + B`.
-/
import Brockian.WeylKatoRellichTransfer

namespace Brockian.Weyl.KatoResolventConstruction

open scoped InnerProductSpace
open Brockian.Weyl.Cayley
open Brockian.Weyl.KatoRellichScaffold
open Brockian.Weyl.KatoUnbounded
open Brockian.Weyl.KatoRellichTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded right resolvents for the two unit shifts of an unbounded operator,
with the norm bounds supplied by the usual self-adjoint resolvent theorem. -/
structure UnitShiftRightResolvents (T : H →ₗ.[ℂ] H) where
  Radd : H →L[ℂ] H
  Rsub : H →L[ℂ] H
  right_add : RightResolvent T (-Complex.I) Radd
  right_sub : RightResolvent T Complex.I Rsub
  norm_Radd_le_one : ‖Radd‖ ≤ 1
  norm_Rsub_le_one : ‖Rsub‖ ≤ 1

/-- The `+i` unit-shift resolvent bound makes the Neumann product small for
bounded perturbations of norm `< 1`. -/
theorem norm_mul_Radd_lt_one_of_unitShiftRightResolvents
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hres : UnitShiftRightResolvents T) (hB : ‖B‖ < 1) :
    ‖B‖ * ‖hres.Radd‖ < 1 := by
  have hnonneg : 0 ≤ ‖B‖ := norm_nonneg B
  have hle : ‖B‖ * ‖hres.Radd‖ ≤ ‖B‖ * 1 :=
    mul_le_mul_of_nonneg_left hres.norm_Radd_le_one hnonneg
  have hlt : ‖B‖ * 1 < 1 := by simpa using hB
  exact lt_of_le_of_lt hle hlt

/-- The `-i` unit-shift resolvent bound makes the Neumann product small for
bounded perturbations of norm `< 1`. -/
theorem norm_mul_Rsub_lt_one_of_unitShiftRightResolvents
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hres : UnitShiftRightResolvents T) (hB : ‖B‖ < 1) :
    ‖B‖ * ‖hres.Rsub‖ < 1 := by
  have hnonneg : 0 ≤ ‖B‖ := norm_nonneg B
  have hle : ‖B‖ * ‖hres.Rsub‖ ≤ ‖B‖ * 1 :=
    mul_le_mul_of_nonneg_left hres.norm_Rsub_le_one hnonneg
  have hlt : ‖B‖ * 1 < 1 := by simpa using hB
  exact lt_of_le_of_lt hle hlt

/-- Unit-shift right resolvents with norm bound `≤ 1` discharge the named
bounded-perturbation transfer for every perturbation with operator norm `< 1`. -/
theorem boundedPerturbationTransfer_of_unitShiftRightResolvents_norm_lt_one
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hres : UnitShiftRightResolvents T) (hB : ‖B‖ < 1) :
    BoundedPerturbationTransfer T B :=
  boundedPerturbationTransfer_of_resolvent_product_norm_lt_one
    hres.right_add
    (norm_mul_Radd_lt_one_of_unitShiftRightResolvents hres hB)
    hres.right_sub
    (norm_mul_Rsub_lt_one_of_unitShiftRightResolvents hres hB)

/-- Unit-shift right resolvents with norm bound `≤ 1` give essential
self-adjointness of the small bounded perturbation. -/
theorem essentiallySelfAdjoint_perturb_of_unitShiftRightResolvents_norm_lt_one
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H))
    (hres : UnitShiftRightResolvents T) (hB : ‖B‖ < 1) :
    EssentiallySelfAdjoint (perturb T B) :=
  essentiallySelfAdjoint_perturb_of_resolvent_norm_mul_lt_one
    hd hres.right_add
    (norm_mul_Radd_lt_one_of_unitShiftRightResolvents hres hB)
    hres.right_sub
    (norm_mul_Rsub_lt_one_of_unitShiftRightResolvents hres hB)

/-- The same result written through the Weyl dense-range chain. -/
theorem essentiallySelfAdjoint_perturb_of_unitShiftRightResolvents_norm_lt_one_via_chain
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H))
    (hres : UnitShiftRightResolvents T) (hB : ‖B‖ < 1) :
    EssentiallySelfAdjoint (perturb T B) :=
  essentiallySelfAdjoint_perturb_of_resolvent_norm_mul_lt_one_via_chain
    hd hres.right_add
    (norm_mul_Radd_lt_one_of_unitShiftRightResolvents hres hB)
    hres.right_sub
    (norm_mul_Rsub_lt_one_of_unitShiftRightResolvents hres hB)

end Brockian.Weyl.KatoResolventConstruction
