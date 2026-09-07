/-
  Brockian/SingularSeriesGaps15121520.lean — even binary gaps n ∈ {1512, 1514, 1516, 1518, 1520}.

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

namespace Brockian.SingularSeries.Gaps15121520

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiveHundredTwelve : (evenPair 1512).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1512 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredFourteen : (evenPair 1514).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1514 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredSixteen : (evenPair 1516).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1516 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredEighteen : (evenPair 1518).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1518 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredTwenty : (evenPair 1520).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1520 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiveHundredTwelve : IsAdmissible (evenPair 1512) :=
  isAdmissible_evenPair (by decide : Even 1512)

theorem isAdmissible_evenPair_oneThousandFiveHundredFourteen : IsAdmissible (evenPair 1514) :=
  isAdmissible_evenPair (by decide : Even 1514)

theorem isAdmissible_evenPair_oneThousandFiveHundredSixteen : IsAdmissible (evenPair 1516) :=
  isAdmissible_evenPair (by decide : Even 1516)

theorem isAdmissible_evenPair_oneThousandFiveHundredEighteen : IsAdmissible (evenPair 1518) :=
  isAdmissible_evenPair (by decide : Even 1518)

theorem isAdmissible_evenPair_oneThousandFiveHundredTwenty : IsAdmissible (evenPair 1520) :=
  isAdmissible_evenPair (by decide : Even 1520)

theorem singular_series_pos_evenPair_oneThousandFiveHundredTwelve : 0 < singularSeries (evenPair 1512) :=
  singular_series_pos_evenPair (by decide : Even 1512)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFourteen : 0 < singularSeries (evenPair 1514) :=
  singular_series_pos_evenPair (by decide : Even 1514)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSixteen : 0 < singularSeries (evenPair 1516) :=
  singular_series_pos_evenPair (by decide : Even 1516)

theorem singular_series_pos_evenPair_oneThousandFiveHundredEighteen : 0 < singularSeries (evenPair 1518) :=
  singular_series_pos_evenPair (by decide : Even 1518)

theorem singular_series_pos_evenPair_oneThousandFiveHundredTwenty : 0 < singularSeries (evenPair 1520) :=
  singular_series_pos_evenPair (by decide : Even 1520)

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1512) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1512) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1514) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1514) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1516) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1516) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1518) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1518) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1520) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1520) P

theorem nu_p_oneThousandFiveHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1512) p = if p = 2 ∨ p ∣ 1512 then 1 else 2 :=
  nu_p_evenPair (by decide : (1512 : ℕ) ≠ 0) (by decide : Even 1512) hp

theorem nu_p_oneThousandFiveHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1514) p = if p = 2 ∨ p ∣ 1514 then 1 else 2 :=
  nu_p_evenPair (by decide : (1514 : ℕ) ≠ 0) (by decide : Even 1514) hp

theorem nu_p_oneThousandFiveHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1516) p = if p = 2 ∨ p ∣ 1516 then 1 else 2 :=
  nu_p_evenPair (by decide : (1516 : ℕ) ≠ 0) (by decide : Even 1516) hp

theorem nu_p_oneThousandFiveHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1518) p = if p = 2 ∨ p ∣ 1518 then 1 else 2 :=
  nu_p_evenPair (by decide : (1518 : ℕ) ≠ 0) (by decide : Even 1518) hp

theorem nu_p_oneThousandFiveHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1520) p = if p = 2 ∨ p ∣ 1520 then 1 else 2 :=
  nu_p_evenPair (by decide : (1520 : ℕ) ≠ 0) (by decide : Even 1520) hp

theorem nu_p_oneThousandFiveHundredTwelve_two : nu_p (evenPair 1512) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1512)

theorem localFactor_oneThousandFiveHundredTwelve_two : localFactor (evenPair 1512) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1512 : ℕ) ≠ 0) (by decide : Even 1512)

theorem nu_p_oneThousandFiveHundredTwenty_two : nu_p (evenPair 1520) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1520)

theorem localFactor_oneThousandFiveHundredTwenty_two : localFactor (evenPair 1520) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1520 : ℕ) ≠ 0) (by decide : Even 1520)

end Brockian.SingularSeries.Gaps15121520
