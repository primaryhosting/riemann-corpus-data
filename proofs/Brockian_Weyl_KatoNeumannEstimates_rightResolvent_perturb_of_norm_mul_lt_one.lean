/-
  Brockian/WeylKatoNeumannEstimates.lean

  Operator-norm estimates feeding the small-norm Neumann factor.

  `WeylKatoNeumann` discharges the bounded Kato factor from
  `‖B.comp R‖ < 1`.  In applications the available estimate is usually the
  coarser but easier condition `‖B‖ * ‖R‖ < 1`; this file packages the
  submultiplicativity step and threads it through the Kato transfer statements.
-/
import Mathlib
import Brockian.WeylKatoNeumann

namespace Brockian.Weyl.KatoNeumannEstimates

open scoped InnerProductSpace
open Brockian.Weyl.Cayley
open Brockian.Weyl.KatoNeumann
open Brockian.Weyl.KatoRellichScaffold
open Brockian.Weyl.KatoUnbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### From product norm estimates to Neumann smallness -/

/-- The standard operator-norm product estimate implies the Neumann smallness
condition for the bounded factor. -/
theorem norm_comp_lt_one_of_norm_mul_lt_one
    (B R : H →L[ℂ] H) (hBR : ‖B‖ * ‖R‖ < 1) :
    ‖B.comp R‖ < 1 :=
  lt_of_le_of_lt (ContinuousLinearMap.opNorm_comp_le (h := B) R) hBR

/-- Product-norm version of the Neumann right inverse for `I + B R`. -/
theorem katoFactor_rightInverse_of_norm_mul_lt_one
    (B R : H →L[ℂ] H) (hBR : ‖B‖ * ‖R‖ < 1) :
    CLMRightInverse (katoFactor B R)
      (katoFactorInverseOfNormLtOne B R
        (norm_comp_lt_one_of_norm_mul_lt_one B R hBR)) :=
  katoFactor_rightInverse_of_norm_lt_one B R
    (norm_comp_lt_one_of_norm_mul_lt_one B R hBR)

/-! ### Range-density transfer from product estimates -/

/-- A right resolvent plus the product estimate `‖B‖‖R‖ < 1` gives a perturbed
right resolvent. -/
theorem rightResolvent_perturb_of_norm_mul_lt_one
    {T : H →ₗ.[ℂ] H} {B R : H →L[ℂ] H} {w : ℂ}
    (hR : RightResolvent T w R) (hBR : ‖B‖ * ‖R‖ < 1) :
    RightResolvent (perturb T B) w
      (R.comp (katoFactorInverseOfNormLtOne B R
        (norm_comp_lt_one_of_norm_mul_lt_one B R hBR))) :=
  rightResolvent_perturb_of_norm_lt_one hR
    (norm_comp_lt_one_of_norm_mul_lt_one B R hBR)

/-- Product-norm version of the `+i` perturbed range surjectivity statement. -/
theorem rangeAddI_perturb_eq_univ_of_resolvent_norm_mul_lt_one
    {T : H →ₗ.[ℂ] H} {B R : H →L[ℂ] H}
    (hR : RightResolvent T (-Complex.I) R) (hBR : ‖B‖ * ‖R‖ < 1) :
    (rangeAddI (perturb T B) : Set H) = Set.univ :=
  rangeAddI_perturb_eq_univ_of_resolvent_norm_lt_one hR
    (norm_comp_lt_one_of_norm_mul_lt_one B R hBR)

/-- Product-norm version of the `-i` perturbed range surjectivity statement. -/
theorem rangeSubI_perturb_eq_univ_of_resolvent_norm_mul_lt_one
    {T : H →ₗ.[ℂ] H} {B R : H →L[ℂ] H}
    (hR : RightResolvent T Complex.I R) (hBR : ‖B‖ * ‖R‖ < 1) :
    (rangeSubI (perturb T B) : Set H) = Set.univ :=
  rangeSubI_perturb_eq_univ_of_resolvent_norm_lt_one hR
    (norm_comp_lt_one_of_norm_mul_lt_one B R hBR)

/-- If both shifted resolvents exist and both product-norm estimates are small,
the Kato transfer hypothesis follows. -/
theorem boundedPerturbationTransfer_of_resolvent_norm_mul_lt_one
    {T : H →ₗ.[ℂ] H} {B Radd Rsub : H →L[ℂ] H}
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hBRadd : ‖B‖ * ‖Radd‖ < 1)
    (hRsub : RightResolvent T Complex.I Rsub)
    (hBRsub : ‖B‖ * ‖Rsub‖ < 1) :
    BoundedPerturbationTransfer T B :=
  boundedPerturbationTransfer_of_resolvent_norm_lt_one
    hRadd (norm_comp_lt_one_of_norm_mul_lt_one B Radd hBRadd)
    hRsub (norm_comp_lt_one_of_norm_mul_lt_one B Rsub hBRsub)

end Brockian.Weyl.KatoNeumannEstimates
