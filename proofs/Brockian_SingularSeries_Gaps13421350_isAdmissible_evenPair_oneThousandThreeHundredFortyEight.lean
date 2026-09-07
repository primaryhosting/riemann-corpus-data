/-
  Brockian/SingularSeriesGaps13421350.lean — even binary gaps n ∈ {1342, 1344, 1346, 1348, 1350}.

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

namespace Brockian.SingularSeries.Gaps13421350

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThreeHundredFortyTwo : (evenPair 1342).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1342 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredFortyFour : (evenPair 1344).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1344 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredFortySix : (evenPair 1346).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1346 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredFortyEight : (evenPair 1348).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1348 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredFifty : (evenPair 1350).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1350 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThreeHundredFortyTwo : IsAdmissible (evenPair 1342) :=
  isAdmissible_evenPair (by decide : Even 1342)

theorem isAdmissible_evenPair_oneThousandThreeHundredFortyFour : IsAdmissible (evenPair 1344) :=
  isAdmissible_evenPair (by decide : Even 1344)

theorem isAdmissible_evenPair_oneThousandThreeHundredFortySix : IsAdmissible (evenPair 1346) :=
  isAdmissible_evenPair (by decide : Even 1346)

theorem isAdmissible_evenPair_oneThousandThreeHundredFortyEight : IsAdmissible (evenPair 1348) :=
  isAdmissible_evenPair (by decide : Even 1348)

theorem isAdmissible_evenPair_oneThousandThreeHundredFifty : IsAdmissible (evenPair 1350) :=
  isAdmissible_evenPair (by decide : Even 1350)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFortyTwo : 0 < singularSeries (evenPair 1342) :=
  singular_series_pos_evenPair (by decide : Even 1342)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFortyFour : 0 < singularSeries (evenPair 1344) :=
  singular_series_pos_evenPair (by decide : Even 1344)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFortySix : 0 < singularSeries (evenPair 1346) :=
  singular_series_pos_evenPair (by decide : Even 1346)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFortyEight : 0 < singularSeries (evenPair 1348) :=
  singular_series_pos_evenPair (by decide : Even 1348)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFifty : 0 < singularSeries (evenPair 1350) :=
  singular_series_pos_evenPair (by decide : Even 1350)

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1342) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1342) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1344) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1344) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1346) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1346) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1348) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1348) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1350) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1350) P

theorem nu_p_oneThousandThreeHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1342) p = if p = 2 ∨ p ∣ 1342 then 1 else 2 :=
  nu_p_evenPair (by decide : (1342 : ℕ) ≠ 0) (by decide : Even 1342) hp

theorem nu_p_oneThousandThreeHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1344) p = if p = 2 ∨ p ∣ 1344 then 1 else 2 :=
  nu_p_evenPair (by decide : (1344 : ℕ) ≠ 0) (by decide : Even 1344) hp

theorem nu_p_oneThousandThreeHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1346) p = if p = 2 ∨ p ∣ 1346 then 1 else 2 :=
  nu_p_evenPair (by decide : (1346 : ℕ) ≠ 0) (by decide : Even 1346) hp

theorem nu_p_oneThousandThreeHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1348) p = if p = 2 ∨ p ∣ 1348 then 1 else 2 :=
  nu_p_evenPair (by decide : (1348 : ℕ) ≠ 0) (by decide : Even 1348) hp

theorem nu_p_oneThousandThreeHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1350) p = if p = 2 ∨ p ∣ 1350 then 1 else 2 :=
  nu_p_evenPair (by decide : (1350 : ℕ) ≠ 0) (by decide : Even 1350) hp

theorem nu_p_oneThousandThreeHundredFortyTwo_two : nu_p (evenPair 1342) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1342)

theorem localFactor_oneThousandThreeHundredFortyTwo_two : localFactor (evenPair 1342) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1342 : ℕ) ≠ 0) (by decide : Even 1342)

theorem nu_p_oneThousandThreeHundredFifty_two : nu_p (evenPair 1350) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1350)

theorem localFactor_oneThousandThreeHundredFifty_two : localFactor (evenPair 1350) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1350 : ℕ) ≠ 0) (by decide : Even 1350)

end Brockian.SingularSeries.Gaps13421350
