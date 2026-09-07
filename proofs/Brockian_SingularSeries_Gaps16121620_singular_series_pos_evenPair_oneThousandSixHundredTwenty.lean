/-
  Brockian/SingularSeriesGaps16121620.lean — even binary gaps n ∈ {1612, 1614, 1616, 1618, 1620}.

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

namespace Brockian.SingularSeries.Gaps16121620

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixHundredTwelve : (evenPair 1612).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1612 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredFourteen : (evenPair 1614).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1614 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredSixteen : (evenPair 1616).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1616 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredEighteen : (evenPair 1618).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1618 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredTwenty : (evenPair 1620).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1620 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixHundredTwelve : IsAdmissible (evenPair 1612) :=
  isAdmissible_evenPair (by decide : Even 1612)

theorem isAdmissible_evenPair_oneThousandSixHundredFourteen : IsAdmissible (evenPair 1614) :=
  isAdmissible_evenPair (by decide : Even 1614)

theorem isAdmissible_evenPair_oneThousandSixHundredSixteen : IsAdmissible (evenPair 1616) :=
  isAdmissible_evenPair (by decide : Even 1616)

theorem isAdmissible_evenPair_oneThousandSixHundredEighteen : IsAdmissible (evenPair 1618) :=
  isAdmissible_evenPair (by decide : Even 1618)

theorem isAdmissible_evenPair_oneThousandSixHundredTwenty : IsAdmissible (evenPair 1620) :=
  isAdmissible_evenPair (by decide : Even 1620)

theorem singular_series_pos_evenPair_oneThousandSixHundredTwelve : 0 < singularSeries (evenPair 1612) :=
  singular_series_pos_evenPair (by decide : Even 1612)

theorem singular_series_pos_evenPair_oneThousandSixHundredFourteen : 0 < singularSeries (evenPair 1614) :=
  singular_series_pos_evenPair (by decide : Even 1614)

theorem singular_series_pos_evenPair_oneThousandSixHundredSixteen : 0 < singularSeries (evenPair 1616) :=
  singular_series_pos_evenPair (by decide : Even 1616)

theorem singular_series_pos_evenPair_oneThousandSixHundredEighteen : 0 < singularSeries (evenPair 1618) :=
  singular_series_pos_evenPair (by decide : Even 1618)

theorem singular_series_pos_evenPair_oneThousandSixHundredTwenty : 0 < singularSeries (evenPair 1620) :=
  singular_series_pos_evenPair (by decide : Even 1620)

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1612) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1612) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1614) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1614) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1616) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1616) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1618) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1618) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1620) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1620) P

theorem nu_p_oneThousandSixHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1612) p = if p = 2 ∨ p ∣ 1612 then 1 else 2 :=
  nu_p_evenPair (by decide : (1612 : ℕ) ≠ 0) (by decide : Even 1612) hp

theorem nu_p_oneThousandSixHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1614) p = if p = 2 ∨ p ∣ 1614 then 1 else 2 :=
  nu_p_evenPair (by decide : (1614 : ℕ) ≠ 0) (by decide : Even 1614) hp

theorem nu_p_oneThousandSixHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1616) p = if p = 2 ∨ p ∣ 1616 then 1 else 2 :=
  nu_p_evenPair (by decide : (1616 : ℕ) ≠ 0) (by decide : Even 1616) hp

theorem nu_p_oneThousandSixHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1618) p = if p = 2 ∨ p ∣ 1618 then 1 else 2 :=
  nu_p_evenPair (by decide : (1618 : ℕ) ≠ 0) (by decide : Even 1618) hp

theorem nu_p_oneThousandSixHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1620) p = if p = 2 ∨ p ∣ 1620 then 1 else 2 :=
  nu_p_evenPair (by decide : (1620 : ℕ) ≠ 0) (by decide : Even 1620) hp

theorem nu_p_oneThousandSixHundredTwelve_two : nu_p (evenPair 1612) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1612)

theorem localFactor_oneThousandSixHundredTwelve_two : localFactor (evenPair 1612) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1612 : ℕ) ≠ 0) (by decide : Even 1612)

theorem nu_p_oneThousandSixHundredTwenty_two : nu_p (evenPair 1620) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1620)

theorem localFactor_oneThousandSixHundredTwenty_two : localFactor (evenPair 1620) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1620 : ℕ) ≠ 0) (by decide : Even 1620)

end Brockian.SingularSeries.Gaps16121620
