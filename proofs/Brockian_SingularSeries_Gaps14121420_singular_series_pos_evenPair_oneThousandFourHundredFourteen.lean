/-
  Brockian/SingularSeriesGaps14121420.lean — even binary gaps n ∈ {1412, 1414, 1416, 1418, 1420}.

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

namespace Brockian.SingularSeries.Gaps14121420

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFourHundredTwelve : (evenPair 1412).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1412 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredFourteen : (evenPair 1414).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1414 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredSixteen : (evenPair 1416).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1416 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredEighteen : (evenPair 1418).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1418 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredTwenty : (evenPair 1420).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1420 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFourHundredTwelve : IsAdmissible (evenPair 1412) :=
  isAdmissible_evenPair (by decide : Even 1412)

theorem isAdmissible_evenPair_oneThousandFourHundredFourteen : IsAdmissible (evenPair 1414) :=
  isAdmissible_evenPair (by decide : Even 1414)

theorem isAdmissible_evenPair_oneThousandFourHundredSixteen : IsAdmissible (evenPair 1416) :=
  isAdmissible_evenPair (by decide : Even 1416)

theorem isAdmissible_evenPair_oneThousandFourHundredEighteen : IsAdmissible (evenPair 1418) :=
  isAdmissible_evenPair (by decide : Even 1418)

theorem isAdmissible_evenPair_oneThousandFourHundredTwenty : IsAdmissible (evenPair 1420) :=
  isAdmissible_evenPair (by decide : Even 1420)

theorem singular_series_pos_evenPair_oneThousandFourHundredTwelve : 0 < singularSeries (evenPair 1412) :=
  singular_series_pos_evenPair (by decide : Even 1412)

theorem singular_series_pos_evenPair_oneThousandFourHundredFourteen : 0 < singularSeries (evenPair 1414) :=
  singular_series_pos_evenPair (by decide : Even 1414)

theorem singular_series_pos_evenPair_oneThousandFourHundredSixteen : 0 < singularSeries (evenPair 1416) :=
  singular_series_pos_evenPair (by decide : Even 1416)

theorem singular_series_pos_evenPair_oneThousandFourHundredEighteen : 0 < singularSeries (evenPair 1418) :=
  singular_series_pos_evenPair (by decide : Even 1418)

theorem singular_series_pos_evenPair_oneThousandFourHundredTwenty : 0 < singularSeries (evenPair 1420) :=
  singular_series_pos_evenPair (by decide : Even 1420)

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1412) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1412) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1414) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1414) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1416) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1416) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1418) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1418) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1420) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1420) P

theorem nu_p_oneThousandFourHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1412) p = if p = 2 ∨ p ∣ 1412 then 1 else 2 :=
  nu_p_evenPair (by decide : (1412 : ℕ) ≠ 0) (by decide : Even 1412) hp

theorem nu_p_oneThousandFourHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1414) p = if p = 2 ∨ p ∣ 1414 then 1 else 2 :=
  nu_p_evenPair (by decide : (1414 : ℕ) ≠ 0) (by decide : Even 1414) hp

theorem nu_p_oneThousandFourHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1416) p = if p = 2 ∨ p ∣ 1416 then 1 else 2 :=
  nu_p_evenPair (by decide : (1416 : ℕ) ≠ 0) (by decide : Even 1416) hp

theorem nu_p_oneThousandFourHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1418) p = if p = 2 ∨ p ∣ 1418 then 1 else 2 :=
  nu_p_evenPair (by decide : (1418 : ℕ) ≠ 0) (by decide : Even 1418) hp

theorem nu_p_oneThousandFourHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1420) p = if p = 2 ∨ p ∣ 1420 then 1 else 2 :=
  nu_p_evenPair (by decide : (1420 : ℕ) ≠ 0) (by decide : Even 1420) hp

theorem nu_p_oneThousandFourHundredTwelve_two : nu_p (evenPair 1412) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1412)

theorem localFactor_oneThousandFourHundredTwelve_two : localFactor (evenPair 1412) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1412 : ℕ) ≠ 0) (by decide : Even 1412)

theorem nu_p_oneThousandFourHundredTwenty_two : nu_p (evenPair 1420) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1420)

theorem localFactor_oneThousandFourHundredTwenty_two : localFactor (evenPair 1420) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1420 : ℕ) ≠ 0) (by decide : Even 1420)

end Brockian.SingularSeries.Gaps14121420
