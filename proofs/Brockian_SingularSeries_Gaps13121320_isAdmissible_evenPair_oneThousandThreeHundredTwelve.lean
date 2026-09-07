/-
  Brockian/SingularSeriesGaps13121320.lean — even binary gaps n ∈ {1312, 1314, 1316, 1318, 1320}.

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

namespace Brockian.SingularSeries.Gaps13121320

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThreeHundredTwelve : (evenPair 1312).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1312 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredFourteen : (evenPair 1314).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1314 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredSixteen : (evenPair 1316).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1316 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredEighteen : (evenPair 1318).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1318 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredTwenty : (evenPair 1320).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1320 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThreeHundredTwelve : IsAdmissible (evenPair 1312) :=
  isAdmissible_evenPair (by decide : Even 1312)

theorem isAdmissible_evenPair_oneThousandThreeHundredFourteen : IsAdmissible (evenPair 1314) :=
  isAdmissible_evenPair (by decide : Even 1314)

theorem isAdmissible_evenPair_oneThousandThreeHundredSixteen : IsAdmissible (evenPair 1316) :=
  isAdmissible_evenPair (by decide : Even 1316)

theorem isAdmissible_evenPair_oneThousandThreeHundredEighteen : IsAdmissible (evenPair 1318) :=
  isAdmissible_evenPair (by decide : Even 1318)

theorem isAdmissible_evenPair_oneThousandThreeHundredTwenty : IsAdmissible (evenPair 1320) :=
  isAdmissible_evenPair (by decide : Even 1320)

theorem singular_series_pos_evenPair_oneThousandThreeHundredTwelve : 0 < singularSeries (evenPair 1312) :=
  singular_series_pos_evenPair (by decide : Even 1312)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFourteen : 0 < singularSeries (evenPair 1314) :=
  singular_series_pos_evenPair (by decide : Even 1314)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSixteen : 0 < singularSeries (evenPair 1316) :=
  singular_series_pos_evenPair (by decide : Even 1316)

theorem singular_series_pos_evenPair_oneThousandThreeHundredEighteen : 0 < singularSeries (evenPair 1318) :=
  singular_series_pos_evenPair (by decide : Even 1318)

theorem singular_series_pos_evenPair_oneThousandThreeHundredTwenty : 0 < singularSeries (evenPair 1320) :=
  singular_series_pos_evenPair (by decide : Even 1320)

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1312) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1312) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1314) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1314) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1316) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1316) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1318) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1318) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1320) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1320) P

theorem nu_p_oneThousandThreeHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1312) p = if p = 2 ∨ p ∣ 1312 then 1 else 2 :=
  nu_p_evenPair (by decide : (1312 : ℕ) ≠ 0) (by decide : Even 1312) hp

theorem nu_p_oneThousandThreeHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1314) p = if p = 2 ∨ p ∣ 1314 then 1 else 2 :=
  nu_p_evenPair (by decide : (1314 : ℕ) ≠ 0) (by decide : Even 1314) hp

theorem nu_p_oneThousandThreeHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1316) p = if p = 2 ∨ p ∣ 1316 then 1 else 2 :=
  nu_p_evenPair (by decide : (1316 : ℕ) ≠ 0) (by decide : Even 1316) hp

theorem nu_p_oneThousandThreeHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1318) p = if p = 2 ∨ p ∣ 1318 then 1 else 2 :=
  nu_p_evenPair (by decide : (1318 : ℕ) ≠ 0) (by decide : Even 1318) hp

theorem nu_p_oneThousandThreeHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1320) p = if p = 2 ∨ p ∣ 1320 then 1 else 2 :=
  nu_p_evenPair (by decide : (1320 : ℕ) ≠ 0) (by decide : Even 1320) hp

theorem nu_p_oneThousandThreeHundredTwelve_two : nu_p (evenPair 1312) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1312)

theorem localFactor_oneThousandThreeHundredTwelve_two : localFactor (evenPair 1312) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1312 : ℕ) ≠ 0) (by decide : Even 1312)

theorem nu_p_oneThousandThreeHundredTwenty_two : nu_p (evenPair 1320) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1320)

theorem localFactor_oneThousandThreeHundredTwenty_two : localFactor (evenPair 1320) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1320 : ℕ) ≠ 0) (by decide : Even 1320)

end Brockian.SingularSeries.Gaps13121320
