/-
  Brockian/SingularSeriesGaps15521560.lean — even binary gaps n ∈ {1552, 1554, 1556, 1558, 1560}.

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

namespace Brockian.SingularSeries.Gaps15521560

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiveHundredFiftyTwo : (evenPair 1552).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1552 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredFiftyFour : (evenPair 1554).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1554 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredFiftySix : (evenPair 1556).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1556 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredFiftyEight : (evenPair 1558).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1558 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredSixty : (evenPair 1560).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1560 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiveHundredFiftyTwo : IsAdmissible (evenPair 1552) :=
  isAdmissible_evenPair (by decide : Even 1552)

theorem isAdmissible_evenPair_oneThousandFiveHundredFiftyFour : IsAdmissible (evenPair 1554) :=
  isAdmissible_evenPair (by decide : Even 1554)

theorem isAdmissible_evenPair_oneThousandFiveHundredFiftySix : IsAdmissible (evenPair 1556) :=
  isAdmissible_evenPair (by decide : Even 1556)

theorem isAdmissible_evenPair_oneThousandFiveHundredFiftyEight : IsAdmissible (evenPair 1558) :=
  isAdmissible_evenPair (by decide : Even 1558)

theorem isAdmissible_evenPair_oneThousandFiveHundredSixty : IsAdmissible (evenPair 1560) :=
  isAdmissible_evenPair (by decide : Even 1560)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFiftyTwo : 0 < singularSeries (evenPair 1552) :=
  singular_series_pos_evenPair (by decide : Even 1552)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFiftyFour : 0 < singularSeries (evenPair 1554) :=
  singular_series_pos_evenPair (by decide : Even 1554)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFiftySix : 0 < singularSeries (evenPair 1556) :=
  singular_series_pos_evenPair (by decide : Even 1556)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFiftyEight : 0 < singularSeries (evenPair 1558) :=
  singular_series_pos_evenPair (by decide : Even 1558)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSixty : 0 < singularSeries (evenPair 1560) :=
  singular_series_pos_evenPair (by decide : Even 1560)

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1552) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1552) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1554) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1554) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1556) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1556) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1558) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1558) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1560) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1560) P

theorem nu_p_oneThousandFiveHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1552) p = if p = 2 ∨ p ∣ 1552 then 1 else 2 :=
  nu_p_evenPair (by decide : (1552 : ℕ) ≠ 0) (by decide : Even 1552) hp

theorem nu_p_oneThousandFiveHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1554) p = if p = 2 ∨ p ∣ 1554 then 1 else 2 :=
  nu_p_evenPair (by decide : (1554 : ℕ) ≠ 0) (by decide : Even 1554) hp

theorem nu_p_oneThousandFiveHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1556) p = if p = 2 ∨ p ∣ 1556 then 1 else 2 :=
  nu_p_evenPair (by decide : (1556 : ℕ) ≠ 0) (by decide : Even 1556) hp

theorem nu_p_oneThousandFiveHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1558) p = if p = 2 ∨ p ∣ 1558 then 1 else 2 :=
  nu_p_evenPair (by decide : (1558 : ℕ) ≠ 0) (by decide : Even 1558) hp

theorem nu_p_oneThousandFiveHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1560) p = if p = 2 ∨ p ∣ 1560 then 1 else 2 :=
  nu_p_evenPair (by decide : (1560 : ℕ) ≠ 0) (by decide : Even 1560) hp

theorem nu_p_oneThousandFiveHundredFiftyTwo_two : nu_p (evenPair 1552) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1552)

theorem localFactor_oneThousandFiveHundredFiftyTwo_two : localFactor (evenPair 1552) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1552 : ℕ) ≠ 0) (by decide : Even 1552)

theorem nu_p_oneThousandFiveHundredSixty_two : nu_p (evenPair 1560) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1560)

theorem localFactor_oneThousandFiveHundredSixty_two : localFactor (evenPair 1560) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1560 : ℕ) ≠ 0) (by decide : Even 1560)

end Brockian.SingularSeries.Gaps15521560
