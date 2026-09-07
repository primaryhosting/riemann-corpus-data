/-
  Brockian/SingularSeriesGaps772780.lean — even binary gaps n ∈ {772, 774, 776, 778, 780}.

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

namespace Brockian.SingularSeries.Gaps772780

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sevenHundredSeventyTwo : (evenPair 772).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (772 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredSeventyFour : (evenPair 774).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (774 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredSeventySix : (evenPair 776).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (776 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredSeventyEight : (evenPair 778).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (778 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredEighty : (evenPair 780).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (780 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sevenHundredSeventyTwo : IsAdmissible (evenPair 772) :=
  isAdmissible_evenPair (by decide : Even 772)

theorem isAdmissible_evenPair_sevenHundredSeventyFour : IsAdmissible (evenPair 774) :=
  isAdmissible_evenPair (by decide : Even 774)

theorem isAdmissible_evenPair_sevenHundredSeventySix : IsAdmissible (evenPair 776) :=
  isAdmissible_evenPair (by decide : Even 776)

theorem isAdmissible_evenPair_sevenHundredSeventyEight : IsAdmissible (evenPair 778) :=
  isAdmissible_evenPair (by decide : Even 778)

theorem isAdmissible_evenPair_sevenHundredEighty : IsAdmissible (evenPair 780) :=
  isAdmissible_evenPair (by decide : Even 780)

theorem singular_series_pos_evenPair_sevenHundredSeventyTwo : 0 < singularSeries (evenPair 772) :=
  singular_series_pos_evenPair (by decide : Even 772)

theorem singular_series_pos_evenPair_sevenHundredSeventyFour : 0 < singularSeries (evenPair 774) :=
  singular_series_pos_evenPair (by decide : Even 774)

theorem singular_series_pos_evenPair_sevenHundredSeventySix : 0 < singularSeries (evenPair 776) :=
  singular_series_pos_evenPair (by decide : Even 776)

theorem singular_series_pos_evenPair_sevenHundredSeventyEight : 0 < singularSeries (evenPair 778) :=
  singular_series_pos_evenPair (by decide : Even 778)

theorem singular_series_pos_evenPair_sevenHundredEighty : 0 < singularSeries (evenPair 780) :=
  singular_series_pos_evenPair (by decide : Even 780)

theorem singular_series_finite_pos_evenPair_sevenHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 772) P :=
  singular_series_finite_pos_evenPair (by decide : Even 772) P

theorem singular_series_finite_pos_evenPair_sevenHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 774) P :=
  singular_series_finite_pos_evenPair (by decide : Even 774) P

theorem singular_series_finite_pos_evenPair_sevenHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 776) P :=
  singular_series_finite_pos_evenPair (by decide : Even 776) P

theorem singular_series_finite_pos_evenPair_sevenHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 778) P :=
  singular_series_finite_pos_evenPair (by decide : Even 778) P

theorem singular_series_finite_pos_evenPair_sevenHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 780) P :=
  singular_series_finite_pos_evenPair (by decide : Even 780) P

theorem nu_p_sevenHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 772) p = if p = 2 ∨ p ∣ 772 then 1 else 2 :=
  nu_p_evenPair (by decide : (772 : ℕ) ≠ 0) (by decide : Even 772) hp

theorem nu_p_sevenHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 774) p = if p = 2 ∨ p ∣ 774 then 1 else 2 :=
  nu_p_evenPair (by decide : (774 : ℕ) ≠ 0) (by decide : Even 774) hp

theorem nu_p_sevenHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 776) p = if p = 2 ∨ p ∣ 776 then 1 else 2 :=
  nu_p_evenPair (by decide : (776 : ℕ) ≠ 0) (by decide : Even 776) hp

theorem nu_p_sevenHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 778) p = if p = 2 ∨ p ∣ 778 then 1 else 2 :=
  nu_p_evenPair (by decide : (778 : ℕ) ≠ 0) (by decide : Even 778) hp

theorem nu_p_sevenHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 780) p = if p = 2 ∨ p ∣ 780 then 1 else 2 :=
  nu_p_evenPair (by decide : (780 : ℕ) ≠ 0) (by decide : Even 780) hp

theorem nu_p_sevenHundredSeventyTwo_two : nu_p (evenPair 772) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 772)

theorem localFactor_sevenHundredSeventyTwo_two : localFactor (evenPair 772) 2 = 2 :=
  localFactor_evenPair_two (by decide : (772 : ℕ) ≠ 0) (by decide : Even 772)

theorem nu_p_sevenHundredEighty_two : nu_p (evenPair 780) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 780)

theorem localFactor_sevenHundredEighty_two : localFactor (evenPair 780) 2 = 2 :=
  localFactor_evenPair_two (by decide : (780 : ℕ) ≠ 0) (by decide : Even 780)

end Brockian.SingularSeries.Gaps772780
