/-
  Brockian/WeylKatoNeumann.lean

  Small-norm Neumann factor for the Kato--Rellich range-density lane.

  `WeylKatoRellichScaffold` proves the algebraic resolvent transfer assuming a
  right inverse for the bounded factor `I + B R`.  This file discharges that
  bounded-factor input under the classical Banach-algebra hypothesis
  `‖B.comp R‖ < 1`, using Mathlib's `Units.oneSub`.
-/
import Mathlib
import Brockian.WeylKatoRellichScaffold

namespace Brockian.Weyl.KatoNeumann

open scoped InnerProductSpace
open Brockian.Weyl.Cayley
open Brockian.Weyl.KatoRellichScaffold
open Brockian.Weyl.KatoUnbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Small-norm inverse for the bounded Kato factor -/

/-- The bounded inverse of `I + B R`, produced by the Neumann-series unit
`(1 - (-(B R)))⁻¹` in the Banach algebra of continuous linear operators. -/
noncomputable def katoFactorInverseOfNormLtOne
    (B R : H →L[ℂ] H) (hBR : ‖B.comp R‖ < 1) : H →L[ℂ] H :=
  let u : (H →L[ℂ] H)ˣ :=
    Units.oneSub (-(B.comp R)) (by simpa [norm_neg] using hBR)
  ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)

/-- Under `‖B R‖ < 1`, the explicit Neumann inverse right-inverts the Kato
factor `I + B R`. -/
theorem katoFactor_rightInverse_of_norm_lt_one
    (B R : H →L[ℂ] H) (hBR : ‖B.comp R‖ < 1) :
    CLMRightInverse (katoFactor B R)
      (katoFactorInverseOfNormLtOne B R hBR) := by
  intro y
  let u : (H →L[ℂ] H)ˣ :=
    Units.oneSub (-(B.comp R)) (by simpa [norm_neg] using hBR)
  have hfactor : katoFactor B R = (u : H →L[ℂ] H) := by
    ext x
    simp [u, katoFactor, ContinuousLinearMap.comp_apply, sub_eq_add_neg]
  change katoFactor B R (katoFactorInverseOfNormLtOne B R hBR y) = y
  rw [hfactor]
  dsimp [katoFactorInverseOfNormLtOne, u]
  change ((u : H →L[ℂ] H) * (((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H))) y = y
  rw [Units.mul_inv]
  rfl

/-! ### Range-density transfer with small-norm factors -/

/-- A right resolvent for `T - w`, together with the small-norm estimate
`‖B R‖ < 1`, produces a right resolvent for the perturbed shift. -/
theorem rightResolvent_perturb_of_norm_lt_one
    {T : H →ₗ.[ℂ] H} {B R : H →L[ℂ] H} {w : ℂ}
    (hR : RightResolvent T w R) (hBR : ‖B.comp R‖ < 1) :
    RightResolvent (perturb T B) w
      (R.comp (katoFactorInverseOfNormLtOne B R hBR)) :=
  rightResolvent_perturb_of_factor_rightInverse hR
    (katoFactor_rightInverse_of_norm_lt_one B R hBR)

/-- Small-norm Neumann packaging for the `+i` perturbed range. -/
theorem rangeAddI_perturb_eq_univ_of_resolvent_norm_lt_one
    {T : H →ₗ.[ℂ] H} {B R : H →L[ℂ] H}
    (hR : RightResolvent T (-Complex.I) R) (hBR : ‖B.comp R‖ < 1) :
    (rangeAddI (perturb T B) : Set H) = Set.univ :=
  rangeSMulSub_eq_univ_of_rightResolvent
    (rightResolvent_perturb_of_norm_lt_one hR hBR)

/-- Small-norm Neumann packaging for the `-i` perturbed range. -/
theorem rangeSubI_perturb_eq_univ_of_resolvent_norm_lt_one
    {T : H →ₗ.[ℂ] H} {B R : H →L[ℂ] H}
    (hR : RightResolvent T Complex.I R) (hBR : ‖B.comp R‖ < 1) :
    (rangeSubI (perturb T B) : Set H) = Set.univ :=
  rangeSMulSub_eq_univ_of_rightResolvent
    (rightResolvent_perturb_of_norm_lt_one hR hBR)

/-- If both free shifted resolvents exist and the corresponding bounded factors
are small, the Kato transfer hypothesis is discharged.  The remaining
unbounded Kato--Rellich analysis is now isolated to constructing those
resolvents and estimates for the concrete operator. -/
theorem boundedPerturbationTransfer_of_resolvent_norm_lt_one
    {T : H →ₗ.[ℂ] H} {B Radd Rsub : H →L[ℂ] H}
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hBRadd : ‖B.comp Radd‖ < 1)
    (hRsub : RightResolvent T Complex.I Rsub)
    (hBRsub : ‖B.comp Rsub‖ < 1) :
    BoundedPerturbationTransfer T B :=
  boundedPerturbationTransfer_of_resolvent_factors
    hRadd (katoFactor_rightInverse_of_norm_lt_one B Radd hBRadd)
    hRsub (katoFactor_rightInverse_of_norm_lt_one B Rsub hBRsub)

end Brockian.Weyl.KatoNeumann
