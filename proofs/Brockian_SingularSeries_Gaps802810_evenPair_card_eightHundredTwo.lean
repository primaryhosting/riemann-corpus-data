/-
  Brockian/SingularSeriesGaps802810.lean — even binary gaps n ∈ {802, 804, 806, 808, 810}.

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

namespace Brockian.SingularSeries.Gaps802810

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightHundredTwo : (evenPair 802).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (802 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredFour : (evenPair 804).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (804 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredSix : (evenPair 806).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (806 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredEight : (evenPair 808).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (808 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredTen : (evenPair 810).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (810 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightHundredTwo : IsAdmissible (evenPair 802) :=
  isAdmissible_evenPair (by decide : Even 802)

theorem isAdmissible_evenPair_eightHundredFour : IsAdmissible (evenPair 804) :=
  isAdmissible_evenPair (by decide : Even 804)

theorem isAdmissible_evenPair_eightHundredSix : IsAdmissible (evenPair 806) :=
  isAdmissible_evenPair (by decide : Even 806)

theorem isAdmissible_evenPair_eightHundredEight : IsAdmissible (evenPair 808) :=
  isAdmissible_evenPair (by decide : Even 808)

theorem isAdmissible_evenPair_eightHundredTen : IsAdmissible (evenPair 810) :=
  isAdmissible_evenPair (by decide : Even 810)

theorem singular_series_pos_evenPair_eightHundredTwo : 0 < singularSeries (evenPair 802) :=
  singular_series_pos_evenPair (by decide : Even 802)

theorem singular_series_pos_evenPair_eightHundredFour : 0 < singularSeries (evenPair 804) :=
  singular_series_pos_evenPair (by decide : Even 804)

theorem singular_series_pos_evenPair_eightHundredSix : 0 < singularSeries (evenPair 806) :=
  singular_series_pos_evenPair (by decide : Even 806)

theorem singular_series_pos_evenPair_eightHundredEight : 0 < singularSeries (evenPair 808) :=
  singular_series_pos_evenPair (by decide : Even 808)

theorem singular_series_pos_evenPair_eightHundredTen : 0 < singularSeries (evenPair 810) :=
  singular_series_pos_evenPair (by decide : Even 810)

theorem singular_series_finite_pos_evenPair_eightHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 802) P :=
  singular_series_finite_pos_evenPair (by decide : Even 802) P

theorem singular_series_finite_pos_evenPair_eightHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 804) P :=
  singular_series_finite_pos_evenPair (by decide : Even 804) P

theorem singular_series_finite_pos_evenPair_eightHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 806) P :=
  singular_series_finite_pos_evenPair (by decide : Even 806) P

theorem singular_series_finite_pos_evenPair_eightHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 808) P :=
  singular_series_finite_pos_evenPair (by decide : Even 808) P

theorem singular_series_finite_pos_evenPair_eightHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 810) P :=
  singular_series_finite_pos_evenPair (by decide : Even 810) P

theorem nu_p_eightHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 802) p = if p = 2 ∨ p ∣ 802 then 1 else 2 :=
  nu_p_evenPair (by decide : (802 : ℕ) ≠ 0) (by decide : Even 802) hp

theorem nu_p_eightHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 804) p = if p = 2 ∨ p ∣ 804 then 1 else 2 :=
  nu_p_evenPair (by decide : (804 : ℕ) ≠ 0) (by decide : Even 804) hp

theorem nu_p_eightHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 806) p = if p = 2 ∨ p ∣ 806 then 1 else 2 :=
  nu_p_evenPair (by decide : (806 : ℕ) ≠ 0) (by decide : Even 806) hp

theorem nu_p_eightHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 808) p = if p = 2 ∨ p ∣ 808 then 1 else 2 :=
  nu_p_evenPair (by decide : (808 : ℕ) ≠ 0) (by decide : Even 808) hp

theorem nu_p_eightHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 810) p = if p = 2 ∨ p ∣ 810 then 1 else 2 :=
  nu_p_evenPair (by decide : (810 : ℕ) ≠ 0) (by decide : Even 810) hp

theorem nu_p_eightHundredTwo_two : nu_p (evenPair 802) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 802)

theorem localFactor_eightHundredTwo_two : localFactor (evenPair 802) 2 = 2 :=
  localFactor_evenPair_two (by decide : (802 : ℕ) ≠ 0) (by decide : Even 802)

theorem nu_p_eightHundredTen_two : nu_p (evenPair 810) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 810)

theorem localFactor_eightHundredTen_two : localFactor (evenPair 810) 2 = 2 :=
  localFactor_evenPair_two (by decide : (810 : ℕ) ≠ 0) (by decide : Even 810)

end Brockian.SingularSeries.Gaps802810
