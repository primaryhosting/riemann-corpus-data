/-
  Brockian/SingularSeriesGaps14021410.lean — even binary gaps n ∈ {1402, 1404, 1406, 1408, 1410}.

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

namespace Brockian.SingularSeries.Gaps14021410

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFourHundredTwo : (evenPair 1402).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1402 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredFour : (evenPair 1404).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1404 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredSix : (evenPair 1406).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1406 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredEight : (evenPair 1408).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1408 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredTen : (evenPair 1410).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1410 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFourHundredTwo : IsAdmissible (evenPair 1402) :=
  isAdmissible_evenPair (by decide : Even 1402)

theorem isAdmissible_evenPair_oneThousandFourHundredFour : IsAdmissible (evenPair 1404) :=
  isAdmissible_evenPair (by decide : Even 1404)

theorem isAdmissible_evenPair_oneThousandFourHundredSix : IsAdmissible (evenPair 1406) :=
  isAdmissible_evenPair (by decide : Even 1406)

theorem isAdmissible_evenPair_oneThousandFourHundredEight : IsAdmissible (evenPair 1408) :=
  isAdmissible_evenPair (by decide : Even 1408)

theorem isAdmissible_evenPair_oneThousandFourHundredTen : IsAdmissible (evenPair 1410) :=
  isAdmissible_evenPair (by decide : Even 1410)

theorem singular_series_pos_evenPair_oneThousandFourHundredTwo : 0 < singularSeries (evenPair 1402) :=
  singular_series_pos_evenPair (by decide : Even 1402)

theorem singular_series_pos_evenPair_oneThousandFourHundredFour : 0 < singularSeries (evenPair 1404) :=
  singular_series_pos_evenPair (by decide : Even 1404)

theorem singular_series_pos_evenPair_oneThousandFourHundredSix : 0 < singularSeries (evenPair 1406) :=
  singular_series_pos_evenPair (by decide : Even 1406)

theorem singular_series_pos_evenPair_oneThousandFourHundredEight : 0 < singularSeries (evenPair 1408) :=
  singular_series_pos_evenPair (by decide : Even 1408)

theorem singular_series_pos_evenPair_oneThousandFourHundredTen : 0 < singularSeries (evenPair 1410) :=
  singular_series_pos_evenPair (by decide : Even 1410)

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1402) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1402) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1404) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1404) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1406) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1406) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1408) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1408) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1410) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1410) P

theorem nu_p_oneThousandFourHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1402) p = if p = 2 ∨ p ∣ 1402 then 1 else 2 :=
  nu_p_evenPair (by decide : (1402 : ℕ) ≠ 0) (by decide : Even 1402) hp

theorem nu_p_oneThousandFourHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1404) p = if p = 2 ∨ p ∣ 1404 then 1 else 2 :=
  nu_p_evenPair (by decide : (1404 : ℕ) ≠ 0) (by decide : Even 1404) hp

theorem nu_p_oneThousandFourHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1406) p = if p = 2 ∨ p ∣ 1406 then 1 else 2 :=
  nu_p_evenPair (by decide : (1406 : ℕ) ≠ 0) (by decide : Even 1406) hp

theorem nu_p_oneThousandFourHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1408) p = if p = 2 ∨ p ∣ 1408 then 1 else 2 :=
  nu_p_evenPair (by decide : (1408 : ℕ) ≠ 0) (by decide : Even 1408) hp

theorem nu_p_oneThousandFourHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1410) p = if p = 2 ∨ p ∣ 1410 then 1 else 2 :=
  nu_p_evenPair (by decide : (1410 : ℕ) ≠ 0) (by decide : Even 1410) hp

theorem nu_p_oneThousandFourHundredTwo_two : nu_p (evenPair 1402) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1402)

theorem localFactor_oneThousandFourHundredTwo_two : localFactor (evenPair 1402) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1402 : ℕ) ≠ 0) (by decide : Even 1402)

theorem nu_p_oneThousandFourHundredTen_two : nu_p (evenPair 1410) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1410)

theorem localFactor_oneThousandFourHundredTen_two : localFactor (evenPair 1410) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1410 : ℕ) ≠ 0) (by decide : Even 1410)

end Brockian.SingularSeries.Gaps14021410
