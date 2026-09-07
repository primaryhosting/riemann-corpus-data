/-
  Brockian/SingularSeriesGaps17721780.lean — even binary gaps n ∈ {1772, 1774, 1776, 1778, 1780}.

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

namespace Brockian.SingularSeries.Gaps17721780

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSevenHundredSeventyTwo : (evenPair 1772).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1772 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredSeventyFour : (evenPair 1774).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1774 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredSeventySix : (evenPair 1776).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1776 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredSeventyEight : (evenPair 1778).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1778 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredEighty : (evenPair 1780).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1780 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSevenHundredSeventyTwo : IsAdmissible (evenPair 1772) :=
  isAdmissible_evenPair (by decide : Even 1772)

theorem isAdmissible_evenPair_oneThousandSevenHundredSeventyFour : IsAdmissible (evenPair 1774) :=
  isAdmissible_evenPair (by decide : Even 1774)

theorem isAdmissible_evenPair_oneThousandSevenHundredSeventySix : IsAdmissible (evenPair 1776) :=
  isAdmissible_evenPair (by decide : Even 1776)

theorem isAdmissible_evenPair_oneThousandSevenHundredSeventyEight : IsAdmissible (evenPair 1778) :=
  isAdmissible_evenPair (by decide : Even 1778)

theorem isAdmissible_evenPair_oneThousandSevenHundredEighty : IsAdmissible (evenPair 1780) :=
  isAdmissible_evenPair (by decide : Even 1780)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSeventyTwo : 0 < singularSeries (evenPair 1772) :=
  singular_series_pos_evenPair (by decide : Even 1772)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSeventyFour : 0 < singularSeries (evenPair 1774) :=
  singular_series_pos_evenPair (by decide : Even 1774)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSeventySix : 0 < singularSeries (evenPair 1776) :=
  singular_series_pos_evenPair (by decide : Even 1776)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSeventyEight : 0 < singularSeries (evenPair 1778) :=
  singular_series_pos_evenPair (by decide : Even 1778)

theorem singular_series_pos_evenPair_oneThousandSevenHundredEighty : 0 < singularSeries (evenPair 1780) :=
  singular_series_pos_evenPair (by decide : Even 1780)

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1772) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1772) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1774) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1774) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1776) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1776) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1778) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1778) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1780) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1780) P

theorem nu_p_oneThousandSevenHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1772) p = if p = 2 ∨ p ∣ 1772 then 1 else 2 :=
  nu_p_evenPair (by decide : (1772 : ℕ) ≠ 0) (by decide : Even 1772) hp

theorem nu_p_oneThousandSevenHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1774) p = if p = 2 ∨ p ∣ 1774 then 1 else 2 :=
  nu_p_evenPair (by decide : (1774 : ℕ) ≠ 0) (by decide : Even 1774) hp

theorem nu_p_oneThousandSevenHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1776) p = if p = 2 ∨ p ∣ 1776 then 1 else 2 :=
  nu_p_evenPair (by decide : (1776 : ℕ) ≠ 0) (by decide : Even 1776) hp

theorem nu_p_oneThousandSevenHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1778) p = if p = 2 ∨ p ∣ 1778 then 1 else 2 :=
  nu_p_evenPair (by decide : (1778 : ℕ) ≠ 0) (by decide : Even 1778) hp

theorem nu_p_oneThousandSevenHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1780) p = if p = 2 ∨ p ∣ 1780 then 1 else 2 :=
  nu_p_evenPair (by decide : (1780 : ℕ) ≠ 0) (by decide : Even 1780) hp

theorem nu_p_oneThousandSevenHundredSeventyTwo_two : nu_p (evenPair 1772) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1772)

theorem localFactor_oneThousandSevenHundredSeventyTwo_two : localFactor (evenPair 1772) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1772 : ℕ) ≠ 0) (by decide : Even 1772)

theorem nu_p_oneThousandSevenHundredEighty_two : nu_p (evenPair 1780) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1780)

theorem localFactor_oneThousandSevenHundredEighty_two : localFactor (evenPair 1780) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1780 : ℕ) ≠ 0) (by decide : Even 1780)

end Brockian.SingularSeries.Gaps17721780
