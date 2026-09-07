/-
  Brockian/SingularSeriesGaps14821490.lean — even binary gaps n ∈ {1482, 1484, 1486, 1488, 1490}.

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

namespace Brockian.SingularSeries.Gaps14821490

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFourHundredEightyTwo : (evenPair 1482).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1482 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredEightyFour : (evenPair 1484).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1484 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredEightySix : (evenPair 1486).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1486 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredEightyEight : (evenPair 1488).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1488 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredNinety : (evenPair 1490).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1490 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFourHundredEightyTwo : IsAdmissible (evenPair 1482) :=
  isAdmissible_evenPair (by decide : Even 1482)

theorem isAdmissible_evenPair_oneThousandFourHundredEightyFour : IsAdmissible (evenPair 1484) :=
  isAdmissible_evenPair (by decide : Even 1484)

theorem isAdmissible_evenPair_oneThousandFourHundredEightySix : IsAdmissible (evenPair 1486) :=
  isAdmissible_evenPair (by decide : Even 1486)

theorem isAdmissible_evenPair_oneThousandFourHundredEightyEight : IsAdmissible (evenPair 1488) :=
  isAdmissible_evenPair (by decide : Even 1488)

theorem isAdmissible_evenPair_oneThousandFourHundredNinety : IsAdmissible (evenPair 1490) :=
  isAdmissible_evenPair (by decide : Even 1490)

theorem singular_series_pos_evenPair_oneThousandFourHundredEightyTwo : 0 < singularSeries (evenPair 1482) :=
  singular_series_pos_evenPair (by decide : Even 1482)

theorem singular_series_pos_evenPair_oneThousandFourHundredEightyFour : 0 < singularSeries (evenPair 1484) :=
  singular_series_pos_evenPair (by decide : Even 1484)

theorem singular_series_pos_evenPair_oneThousandFourHundredEightySix : 0 < singularSeries (evenPair 1486) :=
  singular_series_pos_evenPair (by decide : Even 1486)

theorem singular_series_pos_evenPair_oneThousandFourHundredEightyEight : 0 < singularSeries (evenPair 1488) :=
  singular_series_pos_evenPair (by decide : Even 1488)

theorem singular_series_pos_evenPair_oneThousandFourHundredNinety : 0 < singularSeries (evenPair 1490) :=
  singular_series_pos_evenPair (by decide : Even 1490)

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1482) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1482) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1484) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1484) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1486) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1486) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1488) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1488) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1490) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1490) P

theorem nu_p_oneThousandFourHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1482) p = if p = 2 ∨ p ∣ 1482 then 1 else 2 :=
  nu_p_evenPair (by decide : (1482 : ℕ) ≠ 0) (by decide : Even 1482) hp

theorem nu_p_oneThousandFourHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1484) p = if p = 2 ∨ p ∣ 1484 then 1 else 2 :=
  nu_p_evenPair (by decide : (1484 : ℕ) ≠ 0) (by decide : Even 1484) hp

theorem nu_p_oneThousandFourHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1486) p = if p = 2 ∨ p ∣ 1486 then 1 else 2 :=
  nu_p_evenPair (by decide : (1486 : ℕ) ≠ 0) (by decide : Even 1486) hp

theorem nu_p_oneThousandFourHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1488) p = if p = 2 ∨ p ∣ 1488 then 1 else 2 :=
  nu_p_evenPair (by decide : (1488 : ℕ) ≠ 0) (by decide : Even 1488) hp

theorem nu_p_oneThousandFourHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1490) p = if p = 2 ∨ p ∣ 1490 then 1 else 2 :=
  nu_p_evenPair (by decide : (1490 : ℕ) ≠ 0) (by decide : Even 1490) hp

theorem nu_p_oneThousandFourHundredEightyTwo_two : nu_p (evenPair 1482) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1482)

theorem localFactor_oneThousandFourHundredEightyTwo_two : localFactor (evenPair 1482) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1482 : ℕ) ≠ 0) (by decide : Even 1482)

theorem nu_p_oneThousandFourHundredNinety_two : nu_p (evenPair 1490) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1490)

theorem localFactor_oneThousandFourHundredNinety_two : localFactor (evenPair 1490) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1490 : ℕ) ≠ 0) (by decide : Even 1490)

end Brockian.SingularSeries.Gaps14821490
