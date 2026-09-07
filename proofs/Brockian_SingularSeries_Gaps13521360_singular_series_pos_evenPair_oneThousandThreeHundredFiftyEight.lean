/-
  Brockian/SingularSeriesGaps13521360.lean — even binary gaps n ∈ {1352, 1354, 1356, 1358, 1360}.

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

namespace Brockian.SingularSeries.Gaps13521360

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThreeHundredFiftyTwo : (evenPair 1352).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1352 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredFiftyFour : (evenPair 1354).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1354 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredFiftySix : (evenPair 1356).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1356 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredFiftyEight : (evenPair 1358).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1358 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredSixty : (evenPair 1360).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1360 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThreeHundredFiftyTwo : IsAdmissible (evenPair 1352) :=
  isAdmissible_evenPair (by decide : Even 1352)

theorem isAdmissible_evenPair_oneThousandThreeHundredFiftyFour : IsAdmissible (evenPair 1354) :=
  isAdmissible_evenPair (by decide : Even 1354)

theorem isAdmissible_evenPair_oneThousandThreeHundredFiftySix : IsAdmissible (evenPair 1356) :=
  isAdmissible_evenPair (by decide : Even 1356)

theorem isAdmissible_evenPair_oneThousandThreeHundredFiftyEight : IsAdmissible (evenPair 1358) :=
  isAdmissible_evenPair (by decide : Even 1358)

theorem isAdmissible_evenPair_oneThousandThreeHundredSixty : IsAdmissible (evenPair 1360) :=
  isAdmissible_evenPair (by decide : Even 1360)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFiftyTwo : 0 < singularSeries (evenPair 1352) :=
  singular_series_pos_evenPair (by decide : Even 1352)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFiftyFour : 0 < singularSeries (evenPair 1354) :=
  singular_series_pos_evenPair (by decide : Even 1354)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFiftySix : 0 < singularSeries (evenPair 1356) :=
  singular_series_pos_evenPair (by decide : Even 1356)

theorem singular_series_pos_evenPair_oneThousandThreeHundredFiftyEight : 0 < singularSeries (evenPair 1358) :=
  singular_series_pos_evenPair (by decide : Even 1358)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSixty : 0 < singularSeries (evenPair 1360) :=
  singular_series_pos_evenPair (by decide : Even 1360)

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1352) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1352) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1354) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1354) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1356) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1356) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1358) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1358) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1360) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1360) P

theorem nu_p_oneThousandThreeHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1352) p = if p = 2 ∨ p ∣ 1352 then 1 else 2 :=
  nu_p_evenPair (by decide : (1352 : ℕ) ≠ 0) (by decide : Even 1352) hp

theorem nu_p_oneThousandThreeHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1354) p = if p = 2 ∨ p ∣ 1354 then 1 else 2 :=
  nu_p_evenPair (by decide : (1354 : ℕ) ≠ 0) (by decide : Even 1354) hp

theorem nu_p_oneThousandThreeHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1356) p = if p = 2 ∨ p ∣ 1356 then 1 else 2 :=
  nu_p_evenPair (by decide : (1356 : ℕ) ≠ 0) (by decide : Even 1356) hp

theorem nu_p_oneThousandThreeHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1358) p = if p = 2 ∨ p ∣ 1358 then 1 else 2 :=
  nu_p_evenPair (by decide : (1358 : ℕ) ≠ 0) (by decide : Even 1358) hp

theorem nu_p_oneThousandThreeHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1360) p = if p = 2 ∨ p ∣ 1360 then 1 else 2 :=
  nu_p_evenPair (by decide : (1360 : ℕ) ≠ 0) (by decide : Even 1360) hp

theorem nu_p_oneThousandThreeHundredFiftyTwo_two : nu_p (evenPair 1352) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1352)

theorem localFactor_oneThousandThreeHundredFiftyTwo_two : localFactor (evenPair 1352) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1352 : ℕ) ≠ 0) (by decide : Even 1352)

theorem nu_p_oneThousandThreeHundredSixty_two : nu_p (evenPair 1360) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1360)

theorem localFactor_oneThousandThreeHundredSixty_two : localFactor (evenPair 1360) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1360 : ℕ) ≠ 0) (by decide : Even 1360)

end Brockian.SingularSeries.Gaps13521360
