/-
  Brockian/SingularSeriesGaps502510.lean — even binary gaps n ∈ {502, 504, 506, 508, 510}.

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

namespace Brockian.SingularSeries.Gaps502510

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiveHundredTwo : (evenPair 502).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (502 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredFour : (evenPair 504).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (504 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredSix : (evenPair 506).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (506 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredEight : (evenPair 508).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (508 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredTen : (evenPair 510).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (510 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiveHundredTwo : IsAdmissible (evenPair 502) :=
  isAdmissible_evenPair (by decide : Even 502)

theorem isAdmissible_evenPair_fiveHundredFour : IsAdmissible (evenPair 504) :=
  isAdmissible_evenPair (by decide : Even 504)

theorem isAdmissible_evenPair_fiveHundredSix : IsAdmissible (evenPair 506) :=
  isAdmissible_evenPair (by decide : Even 506)

theorem isAdmissible_evenPair_fiveHundredEight : IsAdmissible (evenPair 508) :=
  isAdmissible_evenPair (by decide : Even 508)

theorem isAdmissible_evenPair_fiveHundredTen : IsAdmissible (evenPair 510) :=
  isAdmissible_evenPair (by decide : Even 510)

theorem singular_series_pos_evenPair_fiveHundredTwo : 0 < singularSeries (evenPair 502) :=
  singular_series_pos_evenPair (by decide : Even 502)

theorem singular_series_pos_evenPair_fiveHundredFour : 0 < singularSeries (evenPair 504) :=
  singular_series_pos_evenPair (by decide : Even 504)

theorem singular_series_pos_evenPair_fiveHundredSix : 0 < singularSeries (evenPair 506) :=
  singular_series_pos_evenPair (by decide : Even 506)

theorem singular_series_pos_evenPair_fiveHundredEight : 0 < singularSeries (evenPair 508) :=
  singular_series_pos_evenPair (by decide : Even 508)

theorem singular_series_pos_evenPair_fiveHundredTen : 0 < singularSeries (evenPair 510) :=
  singular_series_pos_evenPair (by decide : Even 510)

theorem singular_series_finite_pos_evenPair_fiveHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 502) P :=
  singular_series_finite_pos_evenPair (by decide : Even 502) P

theorem singular_series_finite_pos_evenPair_fiveHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 504) P :=
  singular_series_finite_pos_evenPair (by decide : Even 504) P

theorem singular_series_finite_pos_evenPair_fiveHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 506) P :=
  singular_series_finite_pos_evenPair (by decide : Even 506) P

theorem singular_series_finite_pos_evenPair_fiveHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 508) P :=
  singular_series_finite_pos_evenPair (by decide : Even 508) P

theorem singular_series_finite_pos_evenPair_fiveHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 510) P :=
  singular_series_finite_pos_evenPair (by decide : Even 510) P

theorem nu_p_fiveHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 502) p = if p = 2 ∨ p ∣ 502 then 1 else 2 :=
  nu_p_evenPair (by decide : (502 : ℕ) ≠ 0) (by decide : Even 502) hp

theorem nu_p_fiveHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 504) p = if p = 2 ∨ p ∣ 504 then 1 else 2 :=
  nu_p_evenPair (by decide : (504 : ℕ) ≠ 0) (by decide : Even 504) hp

theorem nu_p_fiveHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 506) p = if p = 2 ∨ p ∣ 506 then 1 else 2 :=
  nu_p_evenPair (by decide : (506 : ℕ) ≠ 0) (by decide : Even 506) hp

theorem nu_p_fiveHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 508) p = if p = 2 ∨ p ∣ 508 then 1 else 2 :=
  nu_p_evenPair (by decide : (508 : ℕ) ≠ 0) (by decide : Even 508) hp

theorem nu_p_fiveHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 510) p = if p = 2 ∨ p ∣ 510 then 1 else 2 :=
  nu_p_evenPair (by decide : (510 : ℕ) ≠ 0) (by decide : Even 510) hp

theorem nu_p_fiveHundredTwo_two : nu_p (evenPair 502) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 502)

theorem localFactor_fiveHundredTwo_two : localFactor (evenPair 502) 2 = 2 :=
  localFactor_evenPair_two (by decide : (502 : ℕ) ≠ 0) (by decide : Even 502)

theorem nu_p_fiveHundredTen_two : nu_p (evenPair 510) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 510)

theorem localFactor_fiveHundredTen_two : localFactor (evenPair 510) 2 = 2 :=
  localFactor_evenPair_two (by decide : (510 : ℕ) ≠ 0) (by decide : Even 510)

end Brockian.SingularSeries.Gaps502510
