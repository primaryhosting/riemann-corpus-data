/-
  Brockian/SingularSeriesGaps482490.lean — even binary gaps n ∈ {482, 484, 486, 488, 490}.

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

namespace Brockian.SingularSeries.Gaps482490

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fourHundredEightyTwo : (evenPair 482).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (482 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredEightyFour : (evenPair 484).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (484 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredEightySix : (evenPair 486).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (486 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredEightyEight : (evenPair 488).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (488 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredNinety : (evenPair 490).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (490 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fourHundredEightyTwo : IsAdmissible (evenPair 482) :=
  isAdmissible_evenPair (by decide : Even 482)

theorem isAdmissible_evenPair_fourHundredEightyFour : IsAdmissible (evenPair 484) :=
  isAdmissible_evenPair (by decide : Even 484)

theorem isAdmissible_evenPair_fourHundredEightySix : IsAdmissible (evenPair 486) :=
  isAdmissible_evenPair (by decide : Even 486)

theorem isAdmissible_evenPair_fourHundredEightyEight : IsAdmissible (evenPair 488) :=
  isAdmissible_evenPair (by decide : Even 488)

theorem isAdmissible_evenPair_fourHundredNinety : IsAdmissible (evenPair 490) :=
  isAdmissible_evenPair (by decide : Even 490)

theorem singular_series_pos_evenPair_fourHundredEightyTwo : 0 < singularSeries (evenPair 482) :=
  singular_series_pos_evenPair (by decide : Even 482)

theorem singular_series_pos_evenPair_fourHundredEightyFour : 0 < singularSeries (evenPair 484) :=
  singular_series_pos_evenPair (by decide : Even 484)

theorem singular_series_pos_evenPair_fourHundredEightySix : 0 < singularSeries (evenPair 486) :=
  singular_series_pos_evenPair (by decide : Even 486)

theorem singular_series_pos_evenPair_fourHundredEightyEight : 0 < singularSeries (evenPair 488) :=
  singular_series_pos_evenPair (by decide : Even 488)

theorem singular_series_pos_evenPair_fourHundredNinety : 0 < singularSeries (evenPair 490) :=
  singular_series_pos_evenPair (by decide : Even 490)

theorem singular_series_finite_pos_evenPair_fourHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 482) P :=
  singular_series_finite_pos_evenPair (by decide : Even 482) P

theorem singular_series_finite_pos_evenPair_fourHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 484) P :=
  singular_series_finite_pos_evenPair (by decide : Even 484) P

theorem singular_series_finite_pos_evenPair_fourHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 486) P :=
  singular_series_finite_pos_evenPair (by decide : Even 486) P

theorem singular_series_finite_pos_evenPair_fourHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 488) P :=
  singular_series_finite_pos_evenPair (by decide : Even 488) P

theorem singular_series_finite_pos_evenPair_fourHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 490) P :=
  singular_series_finite_pos_evenPair (by decide : Even 490) P

theorem nu_p_fourHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 482) p = if p = 2 ∨ p ∣ 482 then 1 else 2 :=
  nu_p_evenPair (by decide : (482 : ℕ) ≠ 0) (by decide : Even 482) hp

theorem nu_p_fourHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 484) p = if p = 2 ∨ p ∣ 484 then 1 else 2 :=
  nu_p_evenPair (by decide : (484 : ℕ) ≠ 0) (by decide : Even 484) hp

theorem nu_p_fourHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 486) p = if p = 2 ∨ p ∣ 486 then 1 else 2 :=
  nu_p_evenPair (by decide : (486 : ℕ) ≠ 0) (by decide : Even 486) hp

theorem nu_p_fourHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 488) p = if p = 2 ∨ p ∣ 488 then 1 else 2 :=
  nu_p_evenPair (by decide : (488 : ℕ) ≠ 0) (by decide : Even 488) hp

theorem nu_p_fourHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 490) p = if p = 2 ∨ p ∣ 490 then 1 else 2 :=
  nu_p_evenPair (by decide : (490 : ℕ) ≠ 0) (by decide : Even 490) hp

theorem nu_p_fourHundredEightyTwo_two : nu_p (evenPair 482) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 482)

theorem localFactor_fourHundredEightyTwo_two : localFactor (evenPair 482) 2 = 2 :=
  localFactor_evenPair_two (by decide : (482 : ℕ) ≠ 0) (by decide : Even 482)

theorem nu_p_fourHundredNinety_two : nu_p (evenPair 490) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 490)

theorem localFactor_fourHundredNinety_two : localFactor (evenPair 490) 2 = 2 :=
  localFactor_evenPair_two (by decide : (490 : ℕ) ≠ 0) (by decide : Even 490)

end Brockian.SingularSeries.Gaps482490
