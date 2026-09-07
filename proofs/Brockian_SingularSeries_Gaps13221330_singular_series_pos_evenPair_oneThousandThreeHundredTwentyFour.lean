/-
  Brockian/SingularSeriesGaps13221330.lean — even binary gaps n ∈ {1322, 1324, 1326, 1328, 1330}.

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

namespace Brockian.SingularSeries.Gaps13221330

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThreeHundredTwentyTwo : (evenPair 1322).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1322 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredTwentyFour : (evenPair 1324).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1324 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredTwentySix : (evenPair 1326).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1326 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredTwentyEight : (evenPair 1328).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1328 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredThirty : (evenPair 1330).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1330 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThreeHundredTwentyTwo : IsAdmissible (evenPair 1322) :=
  isAdmissible_evenPair (by decide : Even 1322)

theorem isAdmissible_evenPair_oneThousandThreeHundredTwentyFour : IsAdmissible (evenPair 1324) :=
  isAdmissible_evenPair (by decide : Even 1324)

theorem isAdmissible_evenPair_oneThousandThreeHundredTwentySix : IsAdmissible (evenPair 1326) :=
  isAdmissible_evenPair (by decide : Even 1326)

theorem isAdmissible_evenPair_oneThousandThreeHundredTwentyEight : IsAdmissible (evenPair 1328) :=
  isAdmissible_evenPair (by decide : Even 1328)

theorem isAdmissible_evenPair_oneThousandThreeHundredThirty : IsAdmissible (evenPair 1330) :=
  isAdmissible_evenPair (by decide : Even 1330)

theorem singular_series_pos_evenPair_oneThousandThreeHundredTwentyTwo : 0 < singularSeries (evenPair 1322) :=
  singular_series_pos_evenPair (by decide : Even 1322)

theorem singular_series_pos_evenPair_oneThousandThreeHundredTwentyFour : 0 < singularSeries (evenPair 1324) :=
  singular_series_pos_evenPair (by decide : Even 1324)

theorem singular_series_pos_evenPair_oneThousandThreeHundredTwentySix : 0 < singularSeries (evenPair 1326) :=
  singular_series_pos_evenPair (by decide : Even 1326)

theorem singular_series_pos_evenPair_oneThousandThreeHundredTwentyEight : 0 < singularSeries (evenPair 1328) :=
  singular_series_pos_evenPair (by decide : Even 1328)

theorem singular_series_pos_evenPair_oneThousandThreeHundredThirty : 0 < singularSeries (evenPair 1330) :=
  singular_series_pos_evenPair (by decide : Even 1330)

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1322) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1322) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1324) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1324) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1326) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1326) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1328) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1328) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1330) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1330) P

theorem nu_p_oneThousandThreeHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1322) p = if p = 2 ∨ p ∣ 1322 then 1 else 2 :=
  nu_p_evenPair (by decide : (1322 : ℕ) ≠ 0) (by decide : Even 1322) hp

theorem nu_p_oneThousandThreeHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1324) p = if p = 2 ∨ p ∣ 1324 then 1 else 2 :=
  nu_p_evenPair (by decide : (1324 : ℕ) ≠ 0) (by decide : Even 1324) hp

theorem nu_p_oneThousandThreeHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1326) p = if p = 2 ∨ p ∣ 1326 then 1 else 2 :=
  nu_p_evenPair (by decide : (1326 : ℕ) ≠ 0) (by decide : Even 1326) hp

theorem nu_p_oneThousandThreeHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1328) p = if p = 2 ∨ p ∣ 1328 then 1 else 2 :=
  nu_p_evenPair (by decide : (1328 : ℕ) ≠ 0) (by decide : Even 1328) hp

theorem nu_p_oneThousandThreeHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1330) p = if p = 2 ∨ p ∣ 1330 then 1 else 2 :=
  nu_p_evenPair (by decide : (1330 : ℕ) ≠ 0) (by decide : Even 1330) hp

theorem nu_p_oneThousandThreeHundredTwentyTwo_two : nu_p (evenPair 1322) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1322)

theorem localFactor_oneThousandThreeHundredTwentyTwo_two : localFactor (evenPair 1322) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1322 : ℕ) ≠ 0) (by decide : Even 1322)

theorem nu_p_oneThousandThreeHundredThirty_two : nu_p (evenPair 1330) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1330)

theorem localFactor_oneThousandThreeHundredThirty_two : localFactor (evenPair 1330) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1330 : ℕ) ≠ 0) (by decide : Even 1330)

end Brockian.SingularSeries.Gaps13221330
