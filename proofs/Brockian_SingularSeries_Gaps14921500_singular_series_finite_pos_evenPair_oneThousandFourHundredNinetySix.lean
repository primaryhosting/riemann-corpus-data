/-
  Brockian/SingularSeriesGaps14921500.lean — even binary gaps n ∈ {1492, 1494, 1496, 1498, 1500}.

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

namespace Brockian.SingularSeries.Gaps14921500

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFourHundredNinetyTwo : (evenPair 1492).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1492 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredNinetyFour : (evenPair 1494).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1494 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredNinetySix : (evenPair 1496).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1496 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredNinetyEight : (evenPair 1498).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1498 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundred : (evenPair 1500).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1500 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFourHundredNinetyTwo : IsAdmissible (evenPair 1492) :=
  isAdmissible_evenPair (by decide : Even 1492)

theorem isAdmissible_evenPair_oneThousandFourHundredNinetyFour : IsAdmissible (evenPair 1494) :=
  isAdmissible_evenPair (by decide : Even 1494)

theorem isAdmissible_evenPair_oneThousandFourHundredNinetySix : IsAdmissible (evenPair 1496) :=
  isAdmissible_evenPair (by decide : Even 1496)

theorem isAdmissible_evenPair_oneThousandFourHundredNinetyEight : IsAdmissible (evenPair 1498) :=
  isAdmissible_evenPair (by decide : Even 1498)

theorem isAdmissible_evenPair_oneThousandFiveHundred : IsAdmissible (evenPair 1500) :=
  isAdmissible_evenPair (by decide : Even 1500)

theorem singular_series_pos_evenPair_oneThousandFourHundredNinetyTwo : 0 < singularSeries (evenPair 1492) :=
  singular_series_pos_evenPair (by decide : Even 1492)

theorem singular_series_pos_evenPair_oneThousandFourHundredNinetyFour : 0 < singularSeries (evenPair 1494) :=
  singular_series_pos_evenPair (by decide : Even 1494)

theorem singular_series_pos_evenPair_oneThousandFourHundredNinetySix : 0 < singularSeries (evenPair 1496) :=
  singular_series_pos_evenPair (by decide : Even 1496)

theorem singular_series_pos_evenPair_oneThousandFourHundredNinetyEight : 0 < singularSeries (evenPair 1498) :=
  singular_series_pos_evenPair (by decide : Even 1498)

theorem singular_series_pos_evenPair_oneThousandFiveHundred : 0 < singularSeries (evenPair 1500) :=
  singular_series_pos_evenPair (by decide : Even 1500)

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1492) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1492) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1494) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1494) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1496) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1496) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1498) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1498) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1500) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1500) P

theorem nu_p_oneThousandFourHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1492) p = if p = 2 ∨ p ∣ 1492 then 1 else 2 :=
  nu_p_evenPair (by decide : (1492 : ℕ) ≠ 0) (by decide : Even 1492) hp

theorem nu_p_oneThousandFourHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1494) p = if p = 2 ∨ p ∣ 1494 then 1 else 2 :=
  nu_p_evenPair (by decide : (1494 : ℕ) ≠ 0) (by decide : Even 1494) hp

theorem nu_p_oneThousandFourHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1496) p = if p = 2 ∨ p ∣ 1496 then 1 else 2 :=
  nu_p_evenPair (by decide : (1496 : ℕ) ≠ 0) (by decide : Even 1496) hp

theorem nu_p_oneThousandFourHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1498) p = if p = 2 ∨ p ∣ 1498 then 1 else 2 :=
  nu_p_evenPair (by decide : (1498 : ℕ) ≠ 0) (by decide : Even 1498) hp

theorem nu_p_oneThousandFiveHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1500) p = if p = 2 ∨ p ∣ 1500 then 1 else 2 :=
  nu_p_evenPair (by decide : (1500 : ℕ) ≠ 0) (by decide : Even 1500) hp

theorem nu_p_oneThousandFourHundredNinetyTwo_two : nu_p (evenPair 1492) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1492)

theorem localFactor_oneThousandFourHundredNinetyTwo_two : localFactor (evenPair 1492) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1492 : ℕ) ≠ 0) (by decide : Even 1492)

theorem nu_p_oneThousandFiveHundred_two : nu_p (evenPair 1500) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1500)

theorem localFactor_oneThousandFiveHundred_two : localFactor (evenPair 1500) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1500 : ℕ) ≠ 0) (by decide : Even 1500)

end Brockian.SingularSeries.Gaps14921500
