/-
  Brockian/SingularSeriesGaps15221530.lean — even binary gaps n ∈ {1522, 1524, 1526, 1528, 1530}.

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

namespace Brockian.SingularSeries.Gaps15221530

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiveHundredTwentyTwo : (evenPair 1522).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1522 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredTwentyFour : (evenPair 1524).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1524 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredTwentySix : (evenPair 1526).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1526 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredTwentyEight : (evenPair 1528).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1528 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredThirty : (evenPair 1530).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1530 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiveHundredTwentyTwo : IsAdmissible (evenPair 1522) :=
  isAdmissible_evenPair (by decide : Even 1522)

theorem isAdmissible_evenPair_oneThousandFiveHundredTwentyFour : IsAdmissible (evenPair 1524) :=
  isAdmissible_evenPair (by decide : Even 1524)

theorem isAdmissible_evenPair_oneThousandFiveHundredTwentySix : IsAdmissible (evenPair 1526) :=
  isAdmissible_evenPair (by decide : Even 1526)

theorem isAdmissible_evenPair_oneThousandFiveHundredTwentyEight : IsAdmissible (evenPair 1528) :=
  isAdmissible_evenPair (by decide : Even 1528)

theorem isAdmissible_evenPair_oneThousandFiveHundredThirty : IsAdmissible (evenPair 1530) :=
  isAdmissible_evenPair (by decide : Even 1530)

theorem singular_series_pos_evenPair_oneThousandFiveHundredTwentyTwo : 0 < singularSeries (evenPair 1522) :=
  singular_series_pos_evenPair (by decide : Even 1522)

theorem singular_series_pos_evenPair_oneThousandFiveHundredTwentyFour : 0 < singularSeries (evenPair 1524) :=
  singular_series_pos_evenPair (by decide : Even 1524)

theorem singular_series_pos_evenPair_oneThousandFiveHundredTwentySix : 0 < singularSeries (evenPair 1526) :=
  singular_series_pos_evenPair (by decide : Even 1526)

theorem singular_series_pos_evenPair_oneThousandFiveHundredTwentyEight : 0 < singularSeries (evenPair 1528) :=
  singular_series_pos_evenPair (by decide : Even 1528)

theorem singular_series_pos_evenPair_oneThousandFiveHundredThirty : 0 < singularSeries (evenPair 1530) :=
  singular_series_pos_evenPair (by decide : Even 1530)

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1522) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1522) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1524) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1524) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1526) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1526) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1528) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1528) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1530) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1530) P

theorem nu_p_oneThousandFiveHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1522) p = if p = 2 ∨ p ∣ 1522 then 1 else 2 :=
  nu_p_evenPair (by decide : (1522 : ℕ) ≠ 0) (by decide : Even 1522) hp

theorem nu_p_oneThousandFiveHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1524) p = if p = 2 ∨ p ∣ 1524 then 1 else 2 :=
  nu_p_evenPair (by decide : (1524 : ℕ) ≠ 0) (by decide : Even 1524) hp

theorem nu_p_oneThousandFiveHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1526) p = if p = 2 ∨ p ∣ 1526 then 1 else 2 :=
  nu_p_evenPair (by decide : (1526 : ℕ) ≠ 0) (by decide : Even 1526) hp

theorem nu_p_oneThousandFiveHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1528) p = if p = 2 ∨ p ∣ 1528 then 1 else 2 :=
  nu_p_evenPair (by decide : (1528 : ℕ) ≠ 0) (by decide : Even 1528) hp

theorem nu_p_oneThousandFiveHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1530) p = if p = 2 ∨ p ∣ 1530 then 1 else 2 :=
  nu_p_evenPair (by decide : (1530 : ℕ) ≠ 0) (by decide : Even 1530) hp

theorem nu_p_oneThousandFiveHundredTwentyTwo_two : nu_p (evenPair 1522) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1522)

theorem localFactor_oneThousandFiveHundredTwentyTwo_two : localFactor (evenPair 1522) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1522 : ℕ) ≠ 0) (by decide : Even 1522)

theorem nu_p_oneThousandFiveHundredThirty_two : nu_p (evenPair 1530) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1530)

theorem localFactor_oneThousandFiveHundredThirty_two : localFactor (evenPair 1530) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1530 : ℕ) ≠ 0) (by decide : Even 1530)

end Brockian.SingularSeries.Gaps15221530
