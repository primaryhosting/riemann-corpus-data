/-
  Brockian/SingularSeriesGaps462470.lean — even binary gaps n ∈ {462, 464, 466, 468, 470}.

  HONEST SCOPE: finite/local singular-series arithmetic only.
  Does NOT claim twin-prime / HL asymptotics / Goldbach transfer / infinitude.
-/
import Mathlib
import Brockian.SingularSeries
import Brockian.SingularSeriesWire
import Brockian.SingularSeriesExamples
import Brockian.SingularSeriesMoreExamples

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Classical
open Real Finset
open Brockian.SingularSeries
open Brockian.SingularSeries.Wire
open Brockian.SingularSeries.Examples
open Brockian.SingularSeries.MoreExamples

namespace Brockian.SingularSeries.Gaps462470

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fourHundredSixtyTwo : (evenPair 462).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (462 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredSixtyFour : (evenPair 464).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (464 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredSixtySix : (evenPair 466).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (466 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredSixtyEight : (evenPair 468).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (468 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredSeventy : (evenPair 470).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (470 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fourHundredSixtyTwo : IsAdmissible (evenPair 462) :=
  isAdmissible_evenPair (by decide : Even 462)

theorem isAdmissible_evenPair_fourHundredSixtyFour : IsAdmissible (evenPair 464) :=
  isAdmissible_evenPair (by decide : Even 464)

theorem isAdmissible_evenPair_fourHundredSixtySix : IsAdmissible (evenPair 466) :=
  isAdmissible_evenPair (by decide : Even 466)

theorem isAdmissible_evenPair_fourHundredSixtyEight : IsAdmissible (evenPair 468) :=
  isAdmissible_evenPair (by decide : Even 468)

theorem isAdmissible_evenPair_fourHundredSeventy : IsAdmissible (evenPair 470) :=
  isAdmissible_evenPair (by decide : Even 470)

theorem singular_series_pos_evenPair_fourHundredSixtyTwo : 0 < singularSeries (evenPair 462) :=
  singular_series_pos_evenPair (by decide : Even 462)

theorem singular_series_pos_evenPair_fourHundredSixtyFour : 0 < singularSeries (evenPair 464) :=
  singular_series_pos_evenPair (by decide : Even 464)

theorem singular_series_pos_evenPair_fourHundredSixtySix : 0 < singularSeries (evenPair 466) :=
  singular_series_pos_evenPair (by decide : Even 466)

theorem singular_series_pos_evenPair_fourHundredSixtyEight : 0 < singularSeries (evenPair 468) :=
  singular_series_pos_evenPair (by decide : Even 468)

theorem singular_series_pos_evenPair_fourHundredSeventy : 0 < singularSeries (evenPair 470) :=
  singular_series_pos_evenPair (by decide : Even 470)

theorem singular_series_finite_pos_evenPair_fourHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 462) P :=
  singular_series_finite_pos_evenPair (by decide : Even 462) P

theorem singular_series_finite_pos_evenPair_fourHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 464) P :=
  singular_series_finite_pos_evenPair (by decide : Even 464) P

theorem singular_series_finite_pos_evenPair_fourHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 466) P :=
  singular_series_finite_pos_evenPair (by decide : Even 466) P

theorem singular_series_finite_pos_evenPair_fourHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 468) P :=
  singular_series_finite_pos_evenPair (by decide : Even 468) P

theorem singular_series_finite_pos_evenPair_fourHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 470) P :=
  singular_series_finite_pos_evenPair (by decide : Even 470) P

theorem nu_p_fourHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 462) p = if p = 2 ∨ p ∣ 462 then 1 else 2 :=
  nu_p_evenPair (by decide : (462 : ℕ) ≠ 0) (by decide : Even 462) hp

theorem nu_p_fourHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 464) p = if p = 2 ∨ p ∣ 464 then 1 else 2 :=
  nu_p_evenPair (by decide : (464 : ℕ) ≠ 0) (by decide : Even 464) hp

theorem nu_p_fourHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 466) p = if p = 2 ∨ p ∣ 466 then 1 else 2 :=
  nu_p_evenPair (by decide : (466 : ℕ) ≠ 0) (by decide : Even 466) hp

theorem nu_p_fourHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 468) p = if p = 2 ∨ p ∣ 468 then 1 else 2 :=
  nu_p_evenPair (by decide : (468 : ℕ) ≠ 0) (by decide : Even 468) hp

theorem nu_p_fourHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 470) p = if p = 2 ∨ p ∣ 470 then 1 else 2 :=
  nu_p_evenPair (by decide : (470 : ℕ) ≠ 0) (by decide : Even 470) hp

theorem nu_p_fourHundredSixtyTwo_two : nu_p (evenPair 462) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 462)

theorem localFactor_fourHundredSixtyTwo_two : localFactor (evenPair 462) 2 = 2 :=
  localFactor_evenPair_two (by decide : (462 : ℕ) ≠ 0) (by decide : Even 462)

theorem nu_p_fourHundredSeventy_two : nu_p (evenPair 470) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 470)

theorem localFactor_fourHundredSeventy_two : localFactor (evenPair 470) 2 = 2 :=
  localFactor_evenPair_two (by decide : (470 : ℕ) ≠ 0) (by decide : Even 470)

end Brockian.SingularSeries.Gaps462470
