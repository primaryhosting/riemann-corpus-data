/-
  Brockian/SingularSeriesGaps17321740.lean — even binary gaps n ∈ {1732, 1734, 1736, 1738, 1740}.

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

namespace Brockian.SingularSeries.Gaps17321740

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSevenHundredThirtyTwo : (evenPair 1732).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1732 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredThirtyFour : (evenPair 1734).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1734 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredThirtySix : (evenPair 1736).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1736 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredThirtyEight : (evenPair 1738).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1738 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredForty : (evenPair 1740).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1740 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSevenHundredThirtyTwo : IsAdmissible (evenPair 1732) :=
  isAdmissible_evenPair (by decide : Even 1732)

theorem isAdmissible_evenPair_oneThousandSevenHundredThirtyFour : IsAdmissible (evenPair 1734) :=
  isAdmissible_evenPair (by decide : Even 1734)

theorem isAdmissible_evenPair_oneThousandSevenHundredThirtySix : IsAdmissible (evenPair 1736) :=
  isAdmissible_evenPair (by decide : Even 1736)

theorem isAdmissible_evenPair_oneThousandSevenHundredThirtyEight : IsAdmissible (evenPair 1738) :=
  isAdmissible_evenPair (by decide : Even 1738)

theorem isAdmissible_evenPair_oneThousandSevenHundredForty : IsAdmissible (evenPair 1740) :=
  isAdmissible_evenPair (by decide : Even 1740)

theorem singular_series_pos_evenPair_oneThousandSevenHundredThirtyTwo : 0 < singularSeries (evenPair 1732) :=
  singular_series_pos_evenPair (by decide : Even 1732)

theorem singular_series_pos_evenPair_oneThousandSevenHundredThirtyFour : 0 < singularSeries (evenPair 1734) :=
  singular_series_pos_evenPair (by decide : Even 1734)

theorem singular_series_pos_evenPair_oneThousandSevenHundredThirtySix : 0 < singularSeries (evenPair 1736) :=
  singular_series_pos_evenPair (by decide : Even 1736)

theorem singular_series_pos_evenPair_oneThousandSevenHundredThirtyEight : 0 < singularSeries (evenPair 1738) :=
  singular_series_pos_evenPair (by decide : Even 1738)

theorem singular_series_pos_evenPair_oneThousandSevenHundredForty : 0 < singularSeries (evenPair 1740) :=
  singular_series_pos_evenPair (by decide : Even 1740)

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1732) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1732) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1734) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1734) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1736) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1736) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1738) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1738) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1740) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1740) P

theorem nu_p_oneThousandSevenHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1732) p = if p = 2 ∨ p ∣ 1732 then 1 else 2 :=
  nu_p_evenPair (by decide : (1732 : ℕ) ≠ 0) (by decide : Even 1732) hp

theorem nu_p_oneThousandSevenHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1734) p = if p = 2 ∨ p ∣ 1734 then 1 else 2 :=
  nu_p_evenPair (by decide : (1734 : ℕ) ≠ 0) (by decide : Even 1734) hp

theorem nu_p_oneThousandSevenHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1736) p = if p = 2 ∨ p ∣ 1736 then 1 else 2 :=
  nu_p_evenPair (by decide : (1736 : ℕ) ≠ 0) (by decide : Even 1736) hp

theorem nu_p_oneThousandSevenHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1738) p = if p = 2 ∨ p ∣ 1738 then 1 else 2 :=
  nu_p_evenPair (by decide : (1738 : ℕ) ≠ 0) (by decide : Even 1738) hp

theorem nu_p_oneThousandSevenHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1740) p = if p = 2 ∨ p ∣ 1740 then 1 else 2 :=
  nu_p_evenPair (by decide : (1740 : ℕ) ≠ 0) (by decide : Even 1740) hp

theorem nu_p_oneThousandSevenHundredThirtyTwo_two : nu_p (evenPair 1732) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1732)

theorem localFactor_oneThousandSevenHundredThirtyTwo_two : localFactor (evenPair 1732) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1732 : ℕ) ≠ 0) (by decide : Even 1732)

theorem nu_p_oneThousandSevenHundredForty_two : nu_p (evenPair 1740) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1740)

theorem localFactor_oneThousandSevenHundredForty_two : localFactor (evenPair 1740) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1740 : ℕ) ≠ 0) (by decide : Even 1740)

end Brockian.SingularSeries.Gaps17321740
