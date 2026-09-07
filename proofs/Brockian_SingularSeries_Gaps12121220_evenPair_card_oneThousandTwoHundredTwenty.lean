/-
  Brockian/SingularSeriesGaps12121220.lean — even binary gaps n ∈ {1212, 1214, 1216, 1218, 1220}.

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

namespace Brockian.SingularSeries.Gaps12121220

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwoHundredTwelve : (evenPair 1212).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1212 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredFourteen : (evenPair 1214).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1214 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredSixteen : (evenPair 1216).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1216 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredEighteen : (evenPair 1218).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1218 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredTwenty : (evenPair 1220).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1220 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwoHundredTwelve : IsAdmissible (evenPair 1212) :=
  isAdmissible_evenPair (by decide : Even 1212)

theorem isAdmissible_evenPair_oneThousandTwoHundredFourteen : IsAdmissible (evenPair 1214) :=
  isAdmissible_evenPair (by decide : Even 1214)

theorem isAdmissible_evenPair_oneThousandTwoHundredSixteen : IsAdmissible (evenPair 1216) :=
  isAdmissible_evenPair (by decide : Even 1216)

theorem isAdmissible_evenPair_oneThousandTwoHundredEighteen : IsAdmissible (evenPair 1218) :=
  isAdmissible_evenPair (by decide : Even 1218)

theorem isAdmissible_evenPair_oneThousandTwoHundredTwenty : IsAdmissible (evenPair 1220) :=
  isAdmissible_evenPair (by decide : Even 1220)

theorem singular_series_pos_evenPair_oneThousandTwoHundredTwelve : 0 < singularSeries (evenPair 1212) :=
  singular_series_pos_evenPair (by decide : Even 1212)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFourteen : 0 < singularSeries (evenPair 1214) :=
  singular_series_pos_evenPair (by decide : Even 1214)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSixteen : 0 < singularSeries (evenPair 1216) :=
  singular_series_pos_evenPair (by decide : Even 1216)

theorem singular_series_pos_evenPair_oneThousandTwoHundredEighteen : 0 < singularSeries (evenPair 1218) :=
  singular_series_pos_evenPair (by decide : Even 1218)

theorem singular_series_pos_evenPair_oneThousandTwoHundredTwenty : 0 < singularSeries (evenPair 1220) :=
  singular_series_pos_evenPair (by decide : Even 1220)

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1212) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1212) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1214) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1214) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1216) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1216) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1218) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1218) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1220) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1220) P

theorem nu_p_oneThousandTwoHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1212) p = if p = 2 ∨ p ∣ 1212 then 1 else 2 :=
  nu_p_evenPair (by decide : (1212 : ℕ) ≠ 0) (by decide : Even 1212) hp

theorem nu_p_oneThousandTwoHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1214) p = if p = 2 ∨ p ∣ 1214 then 1 else 2 :=
  nu_p_evenPair (by decide : (1214 : ℕ) ≠ 0) (by decide : Even 1214) hp

theorem nu_p_oneThousandTwoHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1216) p = if p = 2 ∨ p ∣ 1216 then 1 else 2 :=
  nu_p_evenPair (by decide : (1216 : ℕ) ≠ 0) (by decide : Even 1216) hp

theorem nu_p_oneThousandTwoHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1218) p = if p = 2 ∨ p ∣ 1218 then 1 else 2 :=
  nu_p_evenPair (by decide : (1218 : ℕ) ≠ 0) (by decide : Even 1218) hp

theorem nu_p_oneThousandTwoHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1220) p = if p = 2 ∨ p ∣ 1220 then 1 else 2 :=
  nu_p_evenPair (by decide : (1220 : ℕ) ≠ 0) (by decide : Even 1220) hp

theorem nu_p_oneThousandTwoHundredTwelve_two : nu_p (evenPair 1212) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1212)

theorem localFactor_oneThousandTwoHundredTwelve_two : localFactor (evenPair 1212) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1212 : ℕ) ≠ 0) (by decide : Even 1212)

theorem nu_p_oneThousandTwoHundredTwenty_two : nu_p (evenPair 1220) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1220)

theorem localFactor_oneThousandTwoHundredTwenty_two : localFactor (evenPair 1220) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1220 : ℕ) ≠ 0) (by decide : Even 1220)

end Brockian.SingularSeries.Gaps12121220
