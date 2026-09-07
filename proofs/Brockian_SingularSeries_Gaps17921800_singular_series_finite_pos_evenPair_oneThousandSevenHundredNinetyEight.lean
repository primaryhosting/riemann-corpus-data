/-
  Brockian/SingularSeriesGaps17921800.lean — even binary gaps n ∈ {1792, 1794, 1796, 1798, 1800}.

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

namespace Brockian.SingularSeries.Gaps17921800

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSevenHundredNinetyTwo : (evenPair 1792).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1792 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredNinetyFour : (evenPair 1794).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1794 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredNinetySix : (evenPair 1796).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1796 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredNinetyEight : (evenPair 1798).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1798 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundred : (evenPair 1800).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1800 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSevenHundredNinetyTwo : IsAdmissible (evenPair 1792) :=
  isAdmissible_evenPair (by decide : Even 1792)

theorem isAdmissible_evenPair_oneThousandSevenHundredNinetyFour : IsAdmissible (evenPair 1794) :=
  isAdmissible_evenPair (by decide : Even 1794)

theorem isAdmissible_evenPair_oneThousandSevenHundredNinetySix : IsAdmissible (evenPair 1796) :=
  isAdmissible_evenPair (by decide : Even 1796)

theorem isAdmissible_evenPair_oneThousandSevenHundredNinetyEight : IsAdmissible (evenPair 1798) :=
  isAdmissible_evenPair (by decide : Even 1798)

theorem isAdmissible_evenPair_oneThousandEightHundred : IsAdmissible (evenPair 1800) :=
  isAdmissible_evenPair (by decide : Even 1800)

theorem singular_series_pos_evenPair_oneThousandSevenHundredNinetyTwo : 0 < singularSeries (evenPair 1792) :=
  singular_series_pos_evenPair (by decide : Even 1792)

theorem singular_series_pos_evenPair_oneThousandSevenHundredNinetyFour : 0 < singularSeries (evenPair 1794) :=
  singular_series_pos_evenPair (by decide : Even 1794)

theorem singular_series_pos_evenPair_oneThousandSevenHundredNinetySix : 0 < singularSeries (evenPair 1796) :=
  singular_series_pos_evenPair (by decide : Even 1796)

theorem singular_series_pos_evenPair_oneThousandSevenHundredNinetyEight : 0 < singularSeries (evenPair 1798) :=
  singular_series_pos_evenPair (by decide : Even 1798)

theorem singular_series_pos_evenPair_oneThousandEightHundred : 0 < singularSeries (evenPair 1800) :=
  singular_series_pos_evenPair (by decide : Even 1800)

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1792) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1792) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1794) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1794) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1796) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1796) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1798) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1798) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1800) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1800) P

theorem nu_p_oneThousandSevenHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1792) p = if p = 2 ∨ p ∣ 1792 then 1 else 2 :=
  nu_p_evenPair (by decide : (1792 : ℕ) ≠ 0) (by decide : Even 1792) hp

theorem nu_p_oneThousandSevenHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1794) p = if p = 2 ∨ p ∣ 1794 then 1 else 2 :=
  nu_p_evenPair (by decide : (1794 : ℕ) ≠ 0) (by decide : Even 1794) hp

theorem nu_p_oneThousandSevenHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1796) p = if p = 2 ∨ p ∣ 1796 then 1 else 2 :=
  nu_p_evenPair (by decide : (1796 : ℕ) ≠ 0) (by decide : Even 1796) hp

theorem nu_p_oneThousandSevenHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1798) p = if p = 2 ∨ p ∣ 1798 then 1 else 2 :=
  nu_p_evenPair (by decide : (1798 : ℕ) ≠ 0) (by decide : Even 1798) hp

theorem nu_p_oneThousandEightHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1800) p = if p = 2 ∨ p ∣ 1800 then 1 else 2 :=
  nu_p_evenPair (by decide : (1800 : ℕ) ≠ 0) (by decide : Even 1800) hp

theorem nu_p_oneThousandSevenHundredNinetyTwo_two : nu_p (evenPair 1792) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1792)

theorem localFactor_oneThousandSevenHundredNinetyTwo_two : localFactor (evenPair 1792) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1792 : ℕ) ≠ 0) (by decide : Even 1792)

theorem nu_p_oneThousandEightHundred_two : nu_p (evenPair 1800) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1800)

theorem localFactor_oneThousandEightHundred_two : localFactor (evenPair 1800) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1800 : ℕ) ≠ 0) (by decide : Even 1800)

end Brockian.SingularSeries.Gaps17921800
