/-
  Brockian/SingularSeriesGaps15021510.lean — even binary gaps n ∈ {1502, 1504, 1506, 1508, 1510}.

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

namespace Brockian.SingularSeries.Gaps15021510

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiveHundredTwo : (evenPair 1502).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1502 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredFour : (evenPair 1504).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1504 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredSix : (evenPair 1506).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1506 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredEight : (evenPair 1508).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1508 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredTen : (evenPair 1510).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1510 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiveHundredTwo : IsAdmissible (evenPair 1502) :=
  isAdmissible_evenPair (by decide : Even 1502)

theorem isAdmissible_evenPair_oneThousandFiveHundredFour : IsAdmissible (evenPair 1504) :=
  isAdmissible_evenPair (by decide : Even 1504)

theorem isAdmissible_evenPair_oneThousandFiveHundredSix : IsAdmissible (evenPair 1506) :=
  isAdmissible_evenPair (by decide : Even 1506)

theorem isAdmissible_evenPair_oneThousandFiveHundredEight : IsAdmissible (evenPair 1508) :=
  isAdmissible_evenPair (by decide : Even 1508)

theorem isAdmissible_evenPair_oneThousandFiveHundredTen : IsAdmissible (evenPair 1510) :=
  isAdmissible_evenPair (by decide : Even 1510)

theorem singular_series_pos_evenPair_oneThousandFiveHundredTwo : 0 < singularSeries (evenPair 1502) :=
  singular_series_pos_evenPair (by decide : Even 1502)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFour : 0 < singularSeries (evenPair 1504) :=
  singular_series_pos_evenPair (by decide : Even 1504)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSix : 0 < singularSeries (evenPair 1506) :=
  singular_series_pos_evenPair (by decide : Even 1506)

theorem singular_series_pos_evenPair_oneThousandFiveHundredEight : 0 < singularSeries (evenPair 1508) :=
  singular_series_pos_evenPair (by decide : Even 1508)

theorem singular_series_pos_evenPair_oneThousandFiveHundredTen : 0 < singularSeries (evenPair 1510) :=
  singular_series_pos_evenPair (by decide : Even 1510)

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1502) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1502) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1504) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1504) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1506) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1506) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1508) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1508) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1510) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1510) P

theorem nu_p_oneThousandFiveHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1502) p = if p = 2 ∨ p ∣ 1502 then 1 else 2 :=
  nu_p_evenPair (by decide : (1502 : ℕ) ≠ 0) (by decide : Even 1502) hp

theorem nu_p_oneThousandFiveHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1504) p = if p = 2 ∨ p ∣ 1504 then 1 else 2 :=
  nu_p_evenPair (by decide : (1504 : ℕ) ≠ 0) (by decide : Even 1504) hp

theorem nu_p_oneThousandFiveHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1506) p = if p = 2 ∨ p ∣ 1506 then 1 else 2 :=
  nu_p_evenPair (by decide : (1506 : ℕ) ≠ 0) (by decide : Even 1506) hp

theorem nu_p_oneThousandFiveHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1508) p = if p = 2 ∨ p ∣ 1508 then 1 else 2 :=
  nu_p_evenPair (by decide : (1508 : ℕ) ≠ 0) (by decide : Even 1508) hp

theorem nu_p_oneThousandFiveHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1510) p = if p = 2 ∨ p ∣ 1510 then 1 else 2 :=
  nu_p_evenPair (by decide : (1510 : ℕ) ≠ 0) (by decide : Even 1510) hp

theorem nu_p_oneThousandFiveHundredTwo_two : nu_p (evenPair 1502) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1502)

theorem localFactor_oneThousandFiveHundredTwo_two : localFactor (evenPair 1502) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1502 : ℕ) ≠ 0) (by decide : Even 1502)

theorem nu_p_oneThousandFiveHundredTen_two : nu_p (evenPair 1510) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1510)

theorem localFactor_oneThousandFiveHundredTen_two : localFactor (evenPair 1510) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1510 : ℕ) ≠ 0) (by decide : Even 1510)

end Brockian.SingularSeries.Gaps15021510
