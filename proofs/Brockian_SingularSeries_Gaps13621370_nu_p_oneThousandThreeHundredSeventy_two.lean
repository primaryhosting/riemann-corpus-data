/-
  Brockian/SingularSeriesGaps13621370.lean — even binary gaps n ∈ {1362, 1364, 1366, 1368, 1370}.

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

namespace Brockian.SingularSeries.Gaps13621370

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThreeHundredSixtyTwo : (evenPair 1362).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1362 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredSixtyFour : (evenPair 1364).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1364 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredSixtySix : (evenPair 1366).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1366 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredSixtyEight : (evenPair 1368).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1368 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredSeventy : (evenPair 1370).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1370 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThreeHundredSixtyTwo : IsAdmissible (evenPair 1362) :=
  isAdmissible_evenPair (by decide : Even 1362)

theorem isAdmissible_evenPair_oneThousandThreeHundredSixtyFour : IsAdmissible (evenPair 1364) :=
  isAdmissible_evenPair (by decide : Even 1364)

theorem isAdmissible_evenPair_oneThousandThreeHundredSixtySix : IsAdmissible (evenPair 1366) :=
  isAdmissible_evenPair (by decide : Even 1366)

theorem isAdmissible_evenPair_oneThousandThreeHundredSixtyEight : IsAdmissible (evenPair 1368) :=
  isAdmissible_evenPair (by decide : Even 1368)

theorem isAdmissible_evenPair_oneThousandThreeHundredSeventy : IsAdmissible (evenPair 1370) :=
  isAdmissible_evenPair (by decide : Even 1370)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSixtyTwo : 0 < singularSeries (evenPair 1362) :=
  singular_series_pos_evenPair (by decide : Even 1362)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSixtyFour : 0 < singularSeries (evenPair 1364) :=
  singular_series_pos_evenPair (by decide : Even 1364)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSixtySix : 0 < singularSeries (evenPair 1366) :=
  singular_series_pos_evenPair (by decide : Even 1366)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSixtyEight : 0 < singularSeries (evenPair 1368) :=
  singular_series_pos_evenPair (by decide : Even 1368)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSeventy : 0 < singularSeries (evenPair 1370) :=
  singular_series_pos_evenPair (by decide : Even 1370)

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1362) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1362) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1364) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1364) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1366) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1366) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1368) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1368) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1370) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1370) P

theorem nu_p_oneThousandThreeHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1362) p = if p = 2 ∨ p ∣ 1362 then 1 else 2 :=
  nu_p_evenPair (by decide : (1362 : ℕ) ≠ 0) (by decide : Even 1362) hp

theorem nu_p_oneThousandThreeHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1364) p = if p = 2 ∨ p ∣ 1364 then 1 else 2 :=
  nu_p_evenPair (by decide : (1364 : ℕ) ≠ 0) (by decide : Even 1364) hp

theorem nu_p_oneThousandThreeHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1366) p = if p = 2 ∨ p ∣ 1366 then 1 else 2 :=
  nu_p_evenPair (by decide : (1366 : ℕ) ≠ 0) (by decide : Even 1366) hp

theorem nu_p_oneThousandThreeHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1368) p = if p = 2 ∨ p ∣ 1368 then 1 else 2 :=
  nu_p_evenPair (by decide : (1368 : ℕ) ≠ 0) (by decide : Even 1368) hp

theorem nu_p_oneThousandThreeHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1370) p = if p = 2 ∨ p ∣ 1370 then 1 else 2 :=
  nu_p_evenPair (by decide : (1370 : ℕ) ≠ 0) (by decide : Even 1370) hp

theorem nu_p_oneThousandThreeHundredSixtyTwo_two : nu_p (evenPair 1362) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1362)

theorem localFactor_oneThousandThreeHundredSixtyTwo_two : localFactor (evenPair 1362) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1362 : ℕ) ≠ 0) (by decide : Even 1362)

theorem nu_p_oneThousandThreeHundredSeventy_two : nu_p (evenPair 1370) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1370)

theorem localFactor_oneThousandThreeHundredSeventy_two : localFactor (evenPair 1370) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1370 : ℕ) ≠ 0) (by decide : Even 1370)

end Brockian.SingularSeries.Gaps13621370
