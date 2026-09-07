/-
  Brockian/SingularSeriesGaps662670.lean — even binary gaps n ∈ {662, 664, 666, 668, 670}.

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

namespace Brockian.SingularSeries.Gaps662670

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixHundredSixtyTwo : (evenPair 662).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (662 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredSixtyFour : (evenPair 664).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (664 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredSixtySix : (evenPair 666).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (666 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredSixtyEight : (evenPair 668).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (668 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredSeventy : (evenPair 670).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (670 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixHundredSixtyTwo : IsAdmissible (evenPair 662) :=
  isAdmissible_evenPair (by decide : Even 662)

theorem isAdmissible_evenPair_sixHundredSixtyFour : IsAdmissible (evenPair 664) :=
  isAdmissible_evenPair (by decide : Even 664)

theorem isAdmissible_evenPair_sixHundredSixtySix : IsAdmissible (evenPair 666) :=
  isAdmissible_evenPair (by decide : Even 666)

theorem isAdmissible_evenPair_sixHundredSixtyEight : IsAdmissible (evenPair 668) :=
  isAdmissible_evenPair (by decide : Even 668)

theorem isAdmissible_evenPair_sixHundredSeventy : IsAdmissible (evenPair 670) :=
  isAdmissible_evenPair (by decide : Even 670)

theorem singular_series_pos_evenPair_sixHundredSixtyTwo : 0 < singularSeries (evenPair 662) :=
  singular_series_pos_evenPair (by decide : Even 662)

theorem singular_series_pos_evenPair_sixHundredSixtyFour : 0 < singularSeries (evenPair 664) :=
  singular_series_pos_evenPair (by decide : Even 664)

theorem singular_series_pos_evenPair_sixHundredSixtySix : 0 < singularSeries (evenPair 666) :=
  singular_series_pos_evenPair (by decide : Even 666)

theorem singular_series_pos_evenPair_sixHundredSixtyEight : 0 < singularSeries (evenPair 668) :=
  singular_series_pos_evenPair (by decide : Even 668)

theorem singular_series_pos_evenPair_sixHundredSeventy : 0 < singularSeries (evenPair 670) :=
  singular_series_pos_evenPair (by decide : Even 670)

theorem singular_series_finite_pos_evenPair_sixHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 662) P :=
  singular_series_finite_pos_evenPair (by decide : Even 662) P

theorem singular_series_finite_pos_evenPair_sixHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 664) P :=
  singular_series_finite_pos_evenPair (by decide : Even 664) P

theorem singular_series_finite_pos_evenPair_sixHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 666) P :=
  singular_series_finite_pos_evenPair (by decide : Even 666) P

theorem singular_series_finite_pos_evenPair_sixHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 668) P :=
  singular_series_finite_pos_evenPair (by decide : Even 668) P

theorem singular_series_finite_pos_evenPair_sixHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 670) P :=
  singular_series_finite_pos_evenPair (by decide : Even 670) P

theorem nu_p_sixHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 662) p = if p = 2 ∨ p ∣ 662 then 1 else 2 :=
  nu_p_evenPair (by decide : (662 : ℕ) ≠ 0) (by decide : Even 662) hp

theorem nu_p_sixHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 664) p = if p = 2 ∨ p ∣ 664 then 1 else 2 :=
  nu_p_evenPair (by decide : (664 : ℕ) ≠ 0) (by decide : Even 664) hp

theorem nu_p_sixHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 666) p = if p = 2 ∨ p ∣ 666 then 1 else 2 :=
  nu_p_evenPair (by decide : (666 : ℕ) ≠ 0) (by decide : Even 666) hp

theorem nu_p_sixHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 668) p = if p = 2 ∨ p ∣ 668 then 1 else 2 :=
  nu_p_evenPair (by decide : (668 : ℕ) ≠ 0) (by decide : Even 668) hp

theorem nu_p_sixHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 670) p = if p = 2 ∨ p ∣ 670 then 1 else 2 :=
  nu_p_evenPair (by decide : (670 : ℕ) ≠ 0) (by decide : Even 670) hp

theorem nu_p_sixHundredSixtyTwo_two : nu_p (evenPair 662) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 662)

theorem localFactor_sixHundredSixtyTwo_two : localFactor (evenPair 662) 2 = 2 :=
  localFactor_evenPair_two (by decide : (662 : ℕ) ≠ 0) (by decide : Even 662)

theorem nu_p_sixHundredSeventy_two : nu_p (evenPair 670) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 670)

theorem localFactor_sixHundredSeventy_two : localFactor (evenPair 670) 2 = 2 :=
  localFactor_evenPair_two (by decide : (670 : ℕ) ≠ 0) (by decide : Even 670)

end Brockian.SingularSeries.Gaps662670
