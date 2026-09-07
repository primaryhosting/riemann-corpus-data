/-
  Brockian/SingularSeriesGaps14621470.lean — even binary gaps n ∈ {1462, 1464, 1466, 1468, 1470}.

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

namespace Brockian.SingularSeries.Gaps14621470

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFourHundredSixtyTwo : (evenPair 1462).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1462 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredSixtyFour : (evenPair 1464).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1464 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredSixtySix : (evenPair 1466).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1466 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredSixtyEight : (evenPair 1468).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1468 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredSeventy : (evenPair 1470).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1470 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFourHundredSixtyTwo : IsAdmissible (evenPair 1462) :=
  isAdmissible_evenPair (by decide : Even 1462)

theorem isAdmissible_evenPair_oneThousandFourHundredSixtyFour : IsAdmissible (evenPair 1464) :=
  isAdmissible_evenPair (by decide : Even 1464)

theorem isAdmissible_evenPair_oneThousandFourHundredSixtySix : IsAdmissible (evenPair 1466) :=
  isAdmissible_evenPair (by decide : Even 1466)

theorem isAdmissible_evenPair_oneThousandFourHundredSixtyEight : IsAdmissible (evenPair 1468) :=
  isAdmissible_evenPair (by decide : Even 1468)

theorem isAdmissible_evenPair_oneThousandFourHundredSeventy : IsAdmissible (evenPair 1470) :=
  isAdmissible_evenPair (by decide : Even 1470)

theorem singular_series_pos_evenPair_oneThousandFourHundredSixtyTwo : 0 < singularSeries (evenPair 1462) :=
  singular_series_pos_evenPair (by decide : Even 1462)

theorem singular_series_pos_evenPair_oneThousandFourHundredSixtyFour : 0 < singularSeries (evenPair 1464) :=
  singular_series_pos_evenPair (by decide : Even 1464)

theorem singular_series_pos_evenPair_oneThousandFourHundredSixtySix : 0 < singularSeries (evenPair 1466) :=
  singular_series_pos_evenPair (by decide : Even 1466)

theorem singular_series_pos_evenPair_oneThousandFourHundredSixtyEight : 0 < singularSeries (evenPair 1468) :=
  singular_series_pos_evenPair (by decide : Even 1468)

theorem singular_series_pos_evenPair_oneThousandFourHundredSeventy : 0 < singularSeries (evenPair 1470) :=
  singular_series_pos_evenPair (by decide : Even 1470)

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1462) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1462) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1464) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1464) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1466) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1466) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1468) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1468) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1470) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1470) P

theorem nu_p_oneThousandFourHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1462) p = if p = 2 ∨ p ∣ 1462 then 1 else 2 :=
  nu_p_evenPair (by decide : (1462 : ℕ) ≠ 0) (by decide : Even 1462) hp

theorem nu_p_oneThousandFourHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1464) p = if p = 2 ∨ p ∣ 1464 then 1 else 2 :=
  nu_p_evenPair (by decide : (1464 : ℕ) ≠ 0) (by decide : Even 1464) hp

theorem nu_p_oneThousandFourHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1466) p = if p = 2 ∨ p ∣ 1466 then 1 else 2 :=
  nu_p_evenPair (by decide : (1466 : ℕ) ≠ 0) (by decide : Even 1466) hp

theorem nu_p_oneThousandFourHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1468) p = if p = 2 ∨ p ∣ 1468 then 1 else 2 :=
  nu_p_evenPair (by decide : (1468 : ℕ) ≠ 0) (by decide : Even 1468) hp

theorem nu_p_oneThousandFourHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1470) p = if p = 2 ∨ p ∣ 1470 then 1 else 2 :=
  nu_p_evenPair (by decide : (1470 : ℕ) ≠ 0) (by decide : Even 1470) hp

theorem nu_p_oneThousandFourHundredSixtyTwo_two : nu_p (evenPair 1462) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1462)

theorem localFactor_oneThousandFourHundredSixtyTwo_two : localFactor (evenPair 1462) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1462 : ℕ) ≠ 0) (by decide : Even 1462)

theorem nu_p_oneThousandFourHundredSeventy_two : nu_p (evenPair 1470) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1470)

theorem localFactor_oneThousandFourHundredSeventy_two : localFactor (evenPair 1470) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1470 : ℕ) ≠ 0) (by decide : Even 1470)

end Brockian.SingularSeries.Gaps14621470
