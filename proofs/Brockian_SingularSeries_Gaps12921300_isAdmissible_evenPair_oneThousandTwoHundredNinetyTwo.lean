/-
  Brockian/SingularSeriesGaps12921300.lean — even binary gaps n ∈ {1292, 1294, 1296, 1298, 1300}.

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

namespace Brockian.SingularSeries.Gaps12921300

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwoHundredNinetyTwo : (evenPair 1292).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1292 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredNinetyFour : (evenPair 1294).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1294 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredNinetySix : (evenPair 1296).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1296 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredNinetyEight : (evenPair 1298).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1298 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundred : (evenPair 1300).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1300 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwoHundredNinetyTwo : IsAdmissible (evenPair 1292) :=
  isAdmissible_evenPair (by decide : Even 1292)

theorem isAdmissible_evenPair_oneThousandTwoHundredNinetyFour : IsAdmissible (evenPair 1294) :=
  isAdmissible_evenPair (by decide : Even 1294)

theorem isAdmissible_evenPair_oneThousandTwoHundredNinetySix : IsAdmissible (evenPair 1296) :=
  isAdmissible_evenPair (by decide : Even 1296)

theorem isAdmissible_evenPair_oneThousandTwoHundredNinetyEight : IsAdmissible (evenPair 1298) :=
  isAdmissible_evenPair (by decide : Even 1298)

theorem isAdmissible_evenPair_oneThousandThreeHundred : IsAdmissible (evenPair 1300) :=
  isAdmissible_evenPair (by decide : Even 1300)

theorem singular_series_pos_evenPair_oneThousandTwoHundredNinetyTwo : 0 < singularSeries (evenPair 1292) :=
  singular_series_pos_evenPair (by decide : Even 1292)

theorem singular_series_pos_evenPair_oneThousandTwoHundredNinetyFour : 0 < singularSeries (evenPair 1294) :=
  singular_series_pos_evenPair (by decide : Even 1294)

theorem singular_series_pos_evenPair_oneThousandTwoHundredNinetySix : 0 < singularSeries (evenPair 1296) :=
  singular_series_pos_evenPair (by decide : Even 1296)

theorem singular_series_pos_evenPair_oneThousandTwoHundredNinetyEight : 0 < singularSeries (evenPair 1298) :=
  singular_series_pos_evenPair (by decide : Even 1298)

theorem singular_series_pos_evenPair_oneThousandThreeHundred : 0 < singularSeries (evenPair 1300) :=
  singular_series_pos_evenPair (by decide : Even 1300)

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1292) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1292) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1294) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1294) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1296) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1296) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1298) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1298) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1300) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1300) P

theorem nu_p_oneThousandTwoHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1292) p = if p = 2 ∨ p ∣ 1292 then 1 else 2 :=
  nu_p_evenPair (by decide : (1292 : ℕ) ≠ 0) (by decide : Even 1292) hp

theorem nu_p_oneThousandTwoHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1294) p = if p = 2 ∨ p ∣ 1294 then 1 else 2 :=
  nu_p_evenPair (by decide : (1294 : ℕ) ≠ 0) (by decide : Even 1294) hp

theorem nu_p_oneThousandTwoHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1296) p = if p = 2 ∨ p ∣ 1296 then 1 else 2 :=
  nu_p_evenPair (by decide : (1296 : ℕ) ≠ 0) (by decide : Even 1296) hp

theorem nu_p_oneThousandTwoHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1298) p = if p = 2 ∨ p ∣ 1298 then 1 else 2 :=
  nu_p_evenPair (by decide : (1298 : ℕ) ≠ 0) (by decide : Even 1298) hp

theorem nu_p_oneThousandThreeHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1300) p = if p = 2 ∨ p ∣ 1300 then 1 else 2 :=
  nu_p_evenPair (by decide : (1300 : ℕ) ≠ 0) (by decide : Even 1300) hp

theorem nu_p_oneThousandTwoHundredNinetyTwo_two : nu_p (evenPair 1292) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1292)

theorem localFactor_oneThousandTwoHundredNinetyTwo_two : localFactor (evenPair 1292) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1292 : ℕ) ≠ 0) (by decide : Even 1292)

theorem nu_p_oneThousandThreeHundred_two : nu_p (evenPair 1300) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1300)

theorem localFactor_oneThousandThreeHundred_two : localFactor (evenPair 1300) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1300 : ℕ) ≠ 0) (by decide : Even 1300)

end Brockian.SingularSeries.Gaps12921300
