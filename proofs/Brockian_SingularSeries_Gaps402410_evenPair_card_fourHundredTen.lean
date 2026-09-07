/-
  Brockian/SingularSeriesGaps402410.lean — even binary gaps n ∈ {402, 404, 406, 408, 410}.

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

namespace Brockian.SingularSeries.Gaps402410

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fourHundredTwo : (evenPair 402).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (402 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredFour : (evenPair 404).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (404 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredSix : (evenPair 406).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (406 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredEight : (evenPair 408).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (408 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredTen : (evenPair 410).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (410 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fourHundredTwo : IsAdmissible (evenPair 402) :=
  isAdmissible_evenPair (by decide : Even 402)

theorem isAdmissible_evenPair_fourHundredFour : IsAdmissible (evenPair 404) :=
  isAdmissible_evenPair (by decide : Even 404)

theorem isAdmissible_evenPair_fourHundredSix : IsAdmissible (evenPair 406) :=
  isAdmissible_evenPair (by decide : Even 406)

theorem isAdmissible_evenPair_fourHundredEight : IsAdmissible (evenPair 408) :=
  isAdmissible_evenPair (by decide : Even 408)

theorem isAdmissible_evenPair_fourHundredTen : IsAdmissible (evenPair 410) :=
  isAdmissible_evenPair (by decide : Even 410)

theorem singular_series_pos_evenPair_fourHundredTwo : 0 < singularSeries (evenPair 402) :=
  singular_series_pos_evenPair (by decide : Even 402)

theorem singular_series_pos_evenPair_fourHundredFour : 0 < singularSeries (evenPair 404) :=
  singular_series_pos_evenPair (by decide : Even 404)

theorem singular_series_pos_evenPair_fourHundredSix : 0 < singularSeries (evenPair 406) :=
  singular_series_pos_evenPair (by decide : Even 406)

theorem singular_series_pos_evenPair_fourHundredEight : 0 < singularSeries (evenPair 408) :=
  singular_series_pos_evenPair (by decide : Even 408)

theorem singular_series_pos_evenPair_fourHundredTen : 0 < singularSeries (evenPair 410) :=
  singular_series_pos_evenPair (by decide : Even 410)

theorem singular_series_finite_pos_evenPair_fourHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 402) P :=
  singular_series_finite_pos_evenPair (by decide : Even 402) P

theorem singular_series_finite_pos_evenPair_fourHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 404) P :=
  singular_series_finite_pos_evenPair (by decide : Even 404) P

theorem singular_series_finite_pos_evenPair_fourHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 406) P :=
  singular_series_finite_pos_evenPair (by decide : Even 406) P

theorem singular_series_finite_pos_evenPair_fourHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 408) P :=
  singular_series_finite_pos_evenPair (by decide : Even 408) P

theorem singular_series_finite_pos_evenPair_fourHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 410) P :=
  singular_series_finite_pos_evenPair (by decide : Even 410) P

theorem nu_p_fourHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 402) p = if p = 2 ∨ p ∣ 402 then 1 else 2 :=
  nu_p_evenPair (by decide : (402 : ℕ) ≠ 0) (by decide : Even 402) hp

theorem nu_p_fourHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 404) p = if p = 2 ∨ p ∣ 404 then 1 else 2 :=
  nu_p_evenPair (by decide : (404 : ℕ) ≠ 0) (by decide : Even 404) hp

theorem nu_p_fourHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 406) p = if p = 2 ∨ p ∣ 406 then 1 else 2 :=
  nu_p_evenPair (by decide : (406 : ℕ) ≠ 0) (by decide : Even 406) hp

theorem nu_p_fourHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 408) p = if p = 2 ∨ p ∣ 408 then 1 else 2 :=
  nu_p_evenPair (by decide : (408 : ℕ) ≠ 0) (by decide : Even 408) hp

theorem nu_p_fourHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 410) p = if p = 2 ∨ p ∣ 410 then 1 else 2 :=
  nu_p_evenPair (by decide : (410 : ℕ) ≠ 0) (by decide : Even 410) hp

theorem nu_p_fourHundredTwo_two : nu_p (evenPair 402) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 402)

theorem localFactor_fourHundredTwo_two : localFactor (evenPair 402) 2 = 2 :=
  localFactor_evenPair_two (by decide : (402 : ℕ) ≠ 0) (by decide : Even 402)

theorem nu_p_fourHundredTen_two : nu_p (evenPair 410) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 410)

theorem localFactor_fourHundredTen_two : localFactor (evenPair 410) 2 = 2 :=
  localFactor_evenPair_two (by decide : (410 : ℕ) ≠ 0) (by decide : Even 410)

end Brockian.SingularSeries.Gaps402410
