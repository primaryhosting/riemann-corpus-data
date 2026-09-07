/-
  Brockian/SingularSeriesGaps15921600.lean — even binary gaps n ∈ {1592, 1594, 1596, 1598, 1600}.

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

namespace Brockian.SingularSeries.Gaps15921600

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiveHundredNinetyTwo : (evenPair 1592).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1592 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredNinetyFour : (evenPair 1594).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1594 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredNinetySix : (evenPair 1596).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1596 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredNinetyEight : (evenPair 1598).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1598 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundred : (evenPair 1600).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1600 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiveHundredNinetyTwo : IsAdmissible (evenPair 1592) :=
  isAdmissible_evenPair (by decide : Even 1592)

theorem isAdmissible_evenPair_oneThousandFiveHundredNinetyFour : IsAdmissible (evenPair 1594) :=
  isAdmissible_evenPair (by decide : Even 1594)

theorem isAdmissible_evenPair_oneThousandFiveHundredNinetySix : IsAdmissible (evenPair 1596) :=
  isAdmissible_evenPair (by decide : Even 1596)

theorem isAdmissible_evenPair_oneThousandFiveHundredNinetyEight : IsAdmissible (evenPair 1598) :=
  isAdmissible_evenPair (by decide : Even 1598)

theorem isAdmissible_evenPair_oneThousandSixHundred : IsAdmissible (evenPair 1600) :=
  isAdmissible_evenPair (by decide : Even 1600)

theorem singular_series_pos_evenPair_oneThousandFiveHundredNinetyTwo : 0 < singularSeries (evenPair 1592) :=
  singular_series_pos_evenPair (by decide : Even 1592)

theorem singular_series_pos_evenPair_oneThousandFiveHundredNinetyFour : 0 < singularSeries (evenPair 1594) :=
  singular_series_pos_evenPair (by decide : Even 1594)

theorem singular_series_pos_evenPair_oneThousandFiveHundredNinetySix : 0 < singularSeries (evenPair 1596) :=
  singular_series_pos_evenPair (by decide : Even 1596)

theorem singular_series_pos_evenPair_oneThousandFiveHundredNinetyEight : 0 < singularSeries (evenPair 1598) :=
  singular_series_pos_evenPair (by decide : Even 1598)

theorem singular_series_pos_evenPair_oneThousandSixHundred : 0 < singularSeries (evenPair 1600) :=
  singular_series_pos_evenPair (by decide : Even 1600)

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1592) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1592) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1594) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1594) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1596) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1596) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1598) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1598) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1600) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1600) P

theorem nu_p_oneThousandFiveHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1592) p = if p = 2 ∨ p ∣ 1592 then 1 else 2 :=
  nu_p_evenPair (by decide : (1592 : ℕ) ≠ 0) (by decide : Even 1592) hp

theorem nu_p_oneThousandFiveHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1594) p = if p = 2 ∨ p ∣ 1594 then 1 else 2 :=
  nu_p_evenPair (by decide : (1594 : ℕ) ≠ 0) (by decide : Even 1594) hp

theorem nu_p_oneThousandFiveHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1596) p = if p = 2 ∨ p ∣ 1596 then 1 else 2 :=
  nu_p_evenPair (by decide : (1596 : ℕ) ≠ 0) (by decide : Even 1596) hp

theorem nu_p_oneThousandFiveHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1598) p = if p = 2 ∨ p ∣ 1598 then 1 else 2 :=
  nu_p_evenPair (by decide : (1598 : ℕ) ≠ 0) (by decide : Even 1598) hp

theorem nu_p_oneThousandSixHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1600) p = if p = 2 ∨ p ∣ 1600 then 1 else 2 :=
  nu_p_evenPair (by decide : (1600 : ℕ) ≠ 0) (by decide : Even 1600) hp

theorem nu_p_oneThousandFiveHundredNinetyTwo_two : nu_p (evenPair 1592) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1592)

theorem localFactor_oneThousandFiveHundredNinetyTwo_two : localFactor (evenPair 1592) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1592 : ℕ) ≠ 0) (by decide : Even 1592)

theorem nu_p_oneThousandSixHundred_two : nu_p (evenPair 1600) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1600)

theorem localFactor_oneThousandSixHundred_two : localFactor (evenPair 1600) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1600 : ℕ) ≠ 0) (by decide : Even 1600)

end Brockian.SingularSeries.Gaps15921600
