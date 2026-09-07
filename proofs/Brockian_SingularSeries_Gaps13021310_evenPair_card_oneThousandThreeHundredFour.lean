/-
  Brockian/SingularSeriesGaps13021310.lean — even binary gaps n ∈ {1302, 1304, 1306, 1308, 1310}.

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

namespace Brockian.SingularSeries.Gaps13021310

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThreeHundredTwo : (evenPair 1302).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1302 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredFour : (evenPair 1304).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1304 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredSix : (evenPair 1306).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1306 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredEight : (evenPair 1308).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1308 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredTen : (evenPair 1310).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1310 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThreeHundredTwo : IsAdmissible (evenPair 1302) :=
  isAdmissible_evenPair (by decide : Even 1302)

theorem isAdmissible_evenPair_oneThousandThreeHundredFour : IsAdmissible (evenPair 1304) :=
  isAdmissible_evenPair (by decide : Even 1304)

theorem isAdmissible_evenPair_oneThousandThreeHundredSix : IsAdmissible (evenPair 1306) :=
  isAdmissible_evenPair (by decide : Even 1306)

theorem isAdmissible_evenPair_oneThousandThreeHundredEight : IsAdmissible (evenPair 1308) :=
  isAdmissible_evenPair (by decide : Even 1308)

theorem isAdmissible_evenPair_oneThousandThreeHundredTen : IsAdmissible (evenPair 1310) :=
  isAdmissible_evenPair (by decide : Even 1310)

theorem singular_series_pos_evenPair_oneThousandThreeHundredTwo : 0 < singularSeries (evenPair 1302) :=
  singular_series_pos_evenPair (by decide : Even 1302)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFour : 0 < singularSeries (evenPair 1304) :=
  singular_series_pos_evenPair (by decide : Even 1304)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSix : 0 < singularSeries (evenPair 1306) :=
  singular_series_pos_evenPair (by decide : Even 1306)

theorem singular_series_pos_evenPair_oneThousandThreeHundredEight : 0 < singularSeries (evenPair 1308) :=
  singular_series_pos_evenPair (by decide : Even 1308)

theorem singular_series_pos_evenPair_oneThousandThreeHundredTen : 0 < singularSeries (evenPair 1310) :=
  singular_series_pos_evenPair (by decide : Even 1310)

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1302) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1302) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1304) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1304) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1306) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1306) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1308) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1308) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1310) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1310) P

theorem nu_p_oneThousandThreeHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1302) p = if p = 2 ∨ p ∣ 1302 then 1 else 2 :=
  nu_p_evenPair (by decide : (1302 : ℕ) ≠ 0) (by decide : Even 1302) hp

theorem nu_p_oneThousandThreeHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1304) p = if p = 2 ∨ p ∣ 1304 then 1 else 2 :=
  nu_p_evenPair (by decide : (1304 : ℕ) ≠ 0) (by decide : Even 1304) hp

theorem nu_p_oneThousandThreeHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1306) p = if p = 2 ∨ p ∣ 1306 then 1 else 2 :=
  nu_p_evenPair (by decide : (1306 : ℕ) ≠ 0) (by decide : Even 1306) hp

theorem nu_p_oneThousandThreeHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1308) p = if p = 2 ∨ p ∣ 1308 then 1 else 2 :=
  nu_p_evenPair (by decide : (1308 : ℕ) ≠ 0) (by decide : Even 1308) hp

theorem nu_p_oneThousandThreeHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1310) p = if p = 2 ∨ p ∣ 1310 then 1 else 2 :=
  nu_p_evenPair (by decide : (1310 : ℕ) ≠ 0) (by decide : Even 1310) hp

theorem nu_p_oneThousandThreeHundredTwo_two : nu_p (evenPair 1302) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1302)

theorem localFactor_oneThousandThreeHundredTwo_two : localFactor (evenPair 1302) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1302 : ℕ) ≠ 0) (by decide : Even 1302)

theorem nu_p_oneThousandThreeHundredTen_two : nu_p (evenPair 1310) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1310)

theorem localFactor_oneThousandThreeHundredTen_two : localFactor (evenPair 1310) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1310 : ℕ) ≠ 0) (by decide : Even 1310)

end Brockian.SingularSeries.Gaps13021310
