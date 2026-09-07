/-
  Brockian/SingularSeriesGaps15821590.lean — even binary gaps n ∈ {1582, 1584, 1586, 1588, 1590}.

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

namespace Brockian.SingularSeries.Gaps15821590

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiveHundredEightyTwo : (evenPair 1582).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1582 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredEightyFour : (evenPair 1584).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1584 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredEightySix : (evenPair 1586).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1586 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredEightyEight : (evenPair 1588).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1588 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredNinety : (evenPair 1590).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1590 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiveHundredEightyTwo : IsAdmissible (evenPair 1582) :=
  isAdmissible_evenPair (by decide : Even 1582)

theorem isAdmissible_evenPair_oneThousandFiveHundredEightyFour : IsAdmissible (evenPair 1584) :=
  isAdmissible_evenPair (by decide : Even 1584)

theorem isAdmissible_evenPair_oneThousandFiveHundredEightySix : IsAdmissible (evenPair 1586) :=
  isAdmissible_evenPair (by decide : Even 1586)

theorem isAdmissible_evenPair_oneThousandFiveHundredEightyEight : IsAdmissible (evenPair 1588) :=
  isAdmissible_evenPair (by decide : Even 1588)

theorem isAdmissible_evenPair_oneThousandFiveHundredNinety : IsAdmissible (evenPair 1590) :=
  isAdmissible_evenPair (by decide : Even 1590)

theorem singular_series_pos_evenPair_oneThousandFiveHundredEightyTwo : 0 < singularSeries (evenPair 1582) :=
  singular_series_pos_evenPair (by decide : Even 1582)

theorem singular_series_pos_evenPair_oneThousandFiveHundredEightyFour : 0 < singularSeries (evenPair 1584) :=
  singular_series_pos_evenPair (by decide : Even 1584)

theorem singular_series_pos_evenPair_oneThousandFiveHundredEightySix : 0 < singularSeries (evenPair 1586) :=
  singular_series_pos_evenPair (by decide : Even 1586)

theorem singular_series_pos_evenPair_oneThousandFiveHundredEightyEight : 0 < singularSeries (evenPair 1588) :=
  singular_series_pos_evenPair (by decide : Even 1588)

theorem singular_series_pos_evenPair_oneThousandFiveHundredNinety : 0 < singularSeries (evenPair 1590) :=
  singular_series_pos_evenPair (by decide : Even 1590)

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1582) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1582) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1584) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1584) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1586) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1586) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1588) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1588) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1590) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1590) P

theorem nu_p_oneThousandFiveHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1582) p = if p = 2 ∨ p ∣ 1582 then 1 else 2 :=
  nu_p_evenPair (by decide : (1582 : ℕ) ≠ 0) (by decide : Even 1582) hp

theorem nu_p_oneThousandFiveHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1584) p = if p = 2 ∨ p ∣ 1584 then 1 else 2 :=
  nu_p_evenPair (by decide : (1584 : ℕ) ≠ 0) (by decide : Even 1584) hp

theorem nu_p_oneThousandFiveHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1586) p = if p = 2 ∨ p ∣ 1586 then 1 else 2 :=
  nu_p_evenPair (by decide : (1586 : ℕ) ≠ 0) (by decide : Even 1586) hp

theorem nu_p_oneThousandFiveHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1588) p = if p = 2 ∨ p ∣ 1588 then 1 else 2 :=
  nu_p_evenPair (by decide : (1588 : ℕ) ≠ 0) (by decide : Even 1588) hp

theorem nu_p_oneThousandFiveHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1590) p = if p = 2 ∨ p ∣ 1590 then 1 else 2 :=
  nu_p_evenPair (by decide : (1590 : ℕ) ≠ 0) (by decide : Even 1590) hp

theorem nu_p_oneThousandFiveHundredEightyTwo_two : nu_p (evenPair 1582) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1582)

theorem localFactor_oneThousandFiveHundredEightyTwo_two : localFactor (evenPair 1582) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1582 : ℕ) ≠ 0) (by decide : Even 1582)

theorem nu_p_oneThousandFiveHundredNinety_two : nu_p (evenPair 1590) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1590)

theorem localFactor_oneThousandFiveHundredNinety_two : localFactor (evenPair 1590) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1590 : ℕ) ≠ 0) (by decide : Even 1590)

end Brockian.SingularSeries.Gaps15821590
