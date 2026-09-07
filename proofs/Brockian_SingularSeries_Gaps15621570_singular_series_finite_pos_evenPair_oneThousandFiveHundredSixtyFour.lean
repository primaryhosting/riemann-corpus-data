/-
  Brockian/SingularSeriesGaps15621570.lean — even binary gaps n ∈ {1562, 1564, 1566, 1568, 1570}.

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

namespace Brockian.SingularSeries.Gaps15621570

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiveHundredSixtyTwo : (evenPair 1562).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1562 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredSixtyFour : (evenPair 1564).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1564 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredSixtySix : (evenPair 1566).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1566 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredSixtyEight : (evenPair 1568).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1568 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredSeventy : (evenPair 1570).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1570 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiveHundredSixtyTwo : IsAdmissible (evenPair 1562) :=
  isAdmissible_evenPair (by decide : Even 1562)

theorem isAdmissible_evenPair_oneThousandFiveHundredSixtyFour : IsAdmissible (evenPair 1564) :=
  isAdmissible_evenPair (by decide : Even 1564)

theorem isAdmissible_evenPair_oneThousandFiveHundredSixtySix : IsAdmissible (evenPair 1566) :=
  isAdmissible_evenPair (by decide : Even 1566)

theorem isAdmissible_evenPair_oneThousandFiveHundredSixtyEight : IsAdmissible (evenPair 1568) :=
  isAdmissible_evenPair (by decide : Even 1568)

theorem isAdmissible_evenPair_oneThousandFiveHundredSeventy : IsAdmissible (evenPair 1570) :=
  isAdmissible_evenPair (by decide : Even 1570)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSixtyTwo : 0 < singularSeries (evenPair 1562) :=
  singular_series_pos_evenPair (by decide : Even 1562)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSixtyFour : 0 < singularSeries (evenPair 1564) :=
  singular_series_pos_evenPair (by decide : Even 1564)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSixtySix : 0 < singularSeries (evenPair 1566) :=
  singular_series_pos_evenPair (by decide : Even 1566)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSixtyEight : 0 < singularSeries (evenPair 1568) :=
  singular_series_pos_evenPair (by decide : Even 1568)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSeventy : 0 < singularSeries (evenPair 1570) :=
  singular_series_pos_evenPair (by decide : Even 1570)

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1562) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1562) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1564) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1564) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1566) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1566) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1568) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1568) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1570) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1570) P

theorem nu_p_oneThousandFiveHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1562) p = if p = 2 ∨ p ∣ 1562 then 1 else 2 :=
  nu_p_evenPair (by decide : (1562 : ℕ) ≠ 0) (by decide : Even 1562) hp

theorem nu_p_oneThousandFiveHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1564) p = if p = 2 ∨ p ∣ 1564 then 1 else 2 :=
  nu_p_evenPair (by decide : (1564 : ℕ) ≠ 0) (by decide : Even 1564) hp

theorem nu_p_oneThousandFiveHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1566) p = if p = 2 ∨ p ∣ 1566 then 1 else 2 :=
  nu_p_evenPair (by decide : (1566 : ℕ) ≠ 0) (by decide : Even 1566) hp

theorem nu_p_oneThousandFiveHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1568) p = if p = 2 ∨ p ∣ 1568 then 1 else 2 :=
  nu_p_evenPair (by decide : (1568 : ℕ) ≠ 0) (by decide : Even 1568) hp

theorem nu_p_oneThousandFiveHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1570) p = if p = 2 ∨ p ∣ 1570 then 1 else 2 :=
  nu_p_evenPair (by decide : (1570 : ℕ) ≠ 0) (by decide : Even 1570) hp

theorem nu_p_oneThousandFiveHundredSixtyTwo_two : nu_p (evenPair 1562) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1562)

theorem localFactor_oneThousandFiveHundredSixtyTwo_two : localFactor (evenPair 1562) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1562 : ℕ) ≠ 0) (by decide : Even 1562)

theorem nu_p_oneThousandFiveHundredSeventy_two : nu_p (evenPair 1570) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1570)

theorem localFactor_oneThousandFiveHundredSeventy_two : localFactor (evenPair 1570) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1570 : ℕ) ≠ 0) (by decide : Even 1570)

end Brockian.SingularSeries.Gaps15621570
